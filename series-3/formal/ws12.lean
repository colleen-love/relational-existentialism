/-
`series-3/formal/ws12.lean`

WS12 (`series-3/spec/ws12/02-design.md`): **hereditary non-domination.** The
existing "no state dominates" results (WS6/WS10) quantify over the *one-step*
successor set. This workstream strengthens them to the *hereditary* closure
`Reaches` (the reflexive-transitive closure of the successor relation):

* **R1 — the reachable bound.** For every state `u`, its reachable set has
  cardinality `≤ κ` (`ws12_reachable_card_le`): the level-wise unions stay `≤ κ`
  because `κ` is infinite (`κ · κ = κ`); no regularity needed.
* **R2 — the continuum keystone (at `κ₀ = ℵ₀`).** The carrier is *strictly* larger
  than `ℵ₀`: an explicit `2^ℵ₀`-family of spine coalgebras injects into it
  (`ws12_carrier_card_continuum`, `ws12_carrier_card_gt`). Finite branching does not
  bound the carrier — infinite-depth behaviour does the coding.
* **R3/R4/R6.** Combining the two: no state hereditarily reaches every state
  (`ws12_no_hereditary_maximal`), no reachable set surjects onto the carrier
  (`ws12_no_hereditary_observer`), every hereditary horizon misses a state
  (`ws12_hereditary_view_proper`). Stated first at generic `κ` under the two typed
  hypotheses (R5 architecture), then instantiated at `ℵ₀` by R1 + R2.

Bundle `ws12_hereditary_scope`. The uncountable strict bound and the general-`κ`
gap remain open remarks (at strong-limit regular `κ` the gap can fail). Axiom-clean
beyond Mathlib's standard three, `sorry`-free.

Built on `ws10` (brings `Reaches`, `carrier_card_ge`, and transitively ws1/ws2/ws6).
-/
import ws10

universe u

open Cardinal Series3.WS1 Series3.WS2 Series3.WS10

namespace Series3.WS12

attribute [local instance] Classical.propDecidable

variable {κ : Cardinal.{u}}

/-! ## Block 1 — levels and the reachable bound (R1) -/

/-- The reachable set of `u` — the hereditary horizon. -/
def ReachSet (u : (νPk κ).X) : Set (νPk κ).X := {y | Reaches u y}

/-- The `n`-th one-step frontier from `u`. -/
def level (u : (νPk κ).X) : ℕ → Set (νPk κ).X
  | 0 => {u}
  | n + 1 => ⋃ v ∈ level u n, ((νPk κ).str v).1

/-- Each level is `≤ κ`: a union over a `≤ κ`-indexed family of `< κ`-sized
successor sets, and `κ · κ = κ` for infinite `κ`. -/
lemma mk_level_le (hinf : ℵ₀ ≤ κ) (u : (νPk κ).X) :
    ∀ n, Cardinal.mk ↥(level u n) ≤ κ := by
  intro n
  induction n with
  | zero =>
    simp only [level, Cardinal.mk_singleton]
    exact le_trans (le_of_lt Cardinal.one_lt_aleph0) hinf
  | succ k ih =>
    have hsup : (⨆ v : ↥(level u k), Cardinal.mk ↥(((νPk κ).str v.1).1)) ≤ κ :=
      ciSup_le' (fun v : ↥(level u k) => le_of_lt ((νPk κ).str v.1).2)
    have hrw : (level u (k + 1)) = ⋃ v : ↥(level u k), ((νPk κ).str v.1).1 := by
      simp only [level]; rw [Set.biUnion_eq_iUnion]
    rw [hrw]
    calc Cardinal.mk ↥(⋃ v : ↥(level u k), ((νPk κ).str v.1).1)
        ≤ Cardinal.mk ↥(level u k) * ⨆ v : ↥(level u k), Cardinal.mk ↥(((νPk κ).str v.1).1) :=
          Cardinal.mk_iUnion_le _
      _ ≤ κ * κ := mul_le_mul' ih hsup
      _ = κ := Cardinal.mul_eq_self hinf

/-- Every reachable state sits at some finite level. -/
lemma reaches_mem_level (u : (νPk κ).X) : ∀ {y}, Reaches u y → ∃ n, y ∈ level u n := by
  intro y h
  induction h with
  | refl => exact ⟨0, by simp [level]⟩
  | tail hab hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by simp only [level]; exact Set.mem_biUnion hn hstep⟩

/-- **R1.** The reachable set has cardinality `≤ κ`. Needs only `ℵ₀ ≤ κ`. -/
theorem ws12_reachable_card_le (hinf : ℵ₀ ≤ κ) (u : (νPk κ).X) :
    Cardinal.mk ↥(ReachSet u) ≤ κ := by
  -- index the level union over `ULift ℕ` so index and carrier share universe `u`
  have hsub : ReachSet u ⊆ ⋃ n : ULift.{u} ℕ, level u n.down := by
    intro y hy
    obtain ⟨n, hn⟩ := reaches_mem_level u hy
    exact Set.mem_iUnion.mpr ⟨ULift.up n, hn⟩
  refine le_trans (Cardinal.mk_le_mk_of_subset hsub) ?_
  refine le_trans (Cardinal.mk_iUnion_le (fun n : ULift.{u} ℕ => level u n.down)) ?_
  have hℕ : Cardinal.mk (ULift.{u} ℕ) ≤ κ := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]; exact hinf
  have hsup : (⨆ n : ULift.{u} ℕ, Cardinal.mk ↥(level u n.down)) ≤ κ :=
    ciSup_le' (fun n : ULift.{u} ℕ => mk_level_le hinf u n.down)
  calc Cardinal.mk (ULift.{u} ℕ) * ⨆ n : ULift.{u} ℕ, Cardinal.mk ↥(level u n.down)
      ≤ κ * κ := mul_le_mul' hℕ hsup
    _ = κ := Cardinal.mul_eq_self hinf

/-! ## Block 2 — the spine injection (R2, the keystone at `ℵ₀`) -/

section Spine

/-- The spine coalgebra of a set `A ⊆ ℕ`: a countable chain
`some 0 → some 1 → …`, with a `none`-terminal loop-off hung at level `n` exactly
when `n ∈ A`. Finitely branching (`≤ 2`). The `A`-dependence is encoded as a
`setOf` (not an `if`) to keep membership reasoning decidability-free. -/
noncomputable def spineCoalg (A : Set ℕ) : Coalg Cardinal.aleph0.{0} where
  X := Option ℕ
  str := fun z =>
    match z with
    | none => ⟨∅, by
        haveI : Finite ↥(∅ : Set (Option ℕ)) := Set.finite_empty.to_subtype
        exact Cardinal.mk_lt_aleph0_iff.mpr ‹_›⟩
    | some n => ⟨insert (some (n + 1)) {z : Option ℕ | z = none ∧ n ∈ A}, by
        have hsub : {z : Option ℕ | z = none ∧ n ∈ A} ⊆ {none} := fun z hz => hz.1
        haveI : Finite ↥(insert (some (n + 1)) {z : Option ℕ | z = none ∧ n ∈ A} :
            Set (Option ℕ)) := (((Set.finite_singleton none).subset hsub).insert _).to_subtype
        exact Cardinal.mk_lt_aleph0_iff.mpr ‹_›⟩

/-- The unique coalgebra morphism from the spine into the terminal carrier. -/
noncomputable def spineHom (A : Set ℕ) : Option ℕ → (νPk Cardinal.aleph0.{0}).X :=
  (νPk_terminal Cardinal.aleph0.{0} (spineCoalg A)).choose

lemma spineHom_nat (A : Set ℕ) (z : Option ℕ) :
    (νPk Cardinal.aleph0.{0}).str (spineHom A z)
      = PkMap Cardinal.aleph0.{0} (spineHom A) ((spineCoalg A).str z) :=
  (νPk_terminal Cardinal.aleph0.{0} (spineCoalg A)).choose_spec.1 z

/-- The image of `none` is the empty-unfolding state. -/
lemma spineHom_none_str (A : Set ℕ) :
    ((νPk Cardinal.aleph0.{0}).str (spineHom A none)).1 = ∅ := by
  rw [spineHom_nat A none]; simp [spineCoalg]

/-- The empty-unfolding state is unique, so every spine sends `none` to it. -/
lemma spineHom_none_eq (A B : Set ℕ) : spineHom A none = spineHom B none := by
  apply (lambek (νPk_terminal Cardinal.aleph0.{0})).injective
  apply Subtype.ext
  rw [spineHom_none_str, spineHom_none_str]

/-- The unfolding of a spine node, computed (the `A`-branch is a `setOf`). -/
lemma spineHom_some_str (A : Set ℕ) (n : ℕ) :
    ((νPk Cardinal.aleph0.{0}).str (spineHom A (some n))).1
      = insert (spineHom A (some (n + 1)))
          {w | w = spineHom A none ∧ n ∈ A} := by
  rw [spineHom_nat A (some n)]
  simp only [PkMap_val, spineCoalg]
  rw [Set.image_insert_eq]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, ⟨hz, hn⟩, rfl⟩; exact ⟨congrArg (spineHom A) hz, hn⟩
  · rintro ⟨hw, hn⟩; exact ⟨none, ⟨rfl, hn⟩, hw.symm⟩

/-- Spine nodes have nonempty unfolding, so they are never the empty state. -/
lemma spineHom_some_ne_none (A : Set ℕ) (n : ℕ) :
    spineHom A (some n) ≠ spineHom A none := by
  intro he
  have h1 : spineHom A (some (n + 1)) ∈ ((νPk Cardinal.aleph0.{0}).str (spineHom A (some n))).1 := by
    rw [spineHom_some_str]; exact Set.mem_insert _ _
  rw [he, spineHom_none_str] at h1
  exact Set.not_mem_empty _ h1

/-- The induction core: equal spine nodes force equal membership at level `n` and
equal successor nodes. -/
lemma spine_step (A B : Set ℕ) (n : ℕ)
    (h : spineHom A (some n) = spineHom B (some n)) :
    (n ∈ A ↔ n ∈ B) ∧ spineHom A (some (n + 1)) = spineHom B (some (n + 1)) := by
  have hset : insert (spineHom A (some (n + 1))) {w | w = spineHom A none ∧ n ∈ A}
      = insert (spineHom B (some (n + 1))) {w | w = spineHom B none ∧ n ∈ B} := by
    have h2 : ((νPk Cardinal.aleph0.{0}).str (spineHom A (some n))).1
        = ((νPk Cardinal.aleph0.{0}).str (spineHom B (some n))).1 := by rw [h]
    rwa [spineHom_some_str, spineHom_some_str] at h2
  have hnone : spineHom A none = spineHom B none := spineHom_none_eq A B
  have hcA : spineHom A (some (n + 1)) ≠ spineHom A none := spineHom_some_ne_none A (n + 1)
  have hcB : spineHom B (some (n + 1)) ≠ spineHom B none := spineHom_some_ne_none B (n + 1)
  -- membership of the shared empty state in each node decides A / B
  have hA : (n ∈ A) ↔
      (spineHom A none ∈ insert (spineHom A (some (n + 1)))
        {w | w = spineHom A none ∧ n ∈ A}) := by
    constructor
    · intro hn; exact Set.mem_insert_iff.mpr (Or.inr ⟨rfl, hn⟩)
    · intro hm
      rcases Set.mem_insert_iff.mp hm with he | hd
      · exact absurd he.symm hcA
      · exact hd.2
  have hB : (n ∈ B) ↔
      (spineHom B none ∈ insert (spineHom B (some (n + 1)))
        {w | w = spineHom B none ∧ n ∈ B}) := by
    constructor
    · intro hn; exact Set.mem_insert_iff.mpr (Or.inr ⟨rfl, hn⟩)
    · intro hm
      rcases Set.mem_insert_iff.mp hm with he | hd
      · exact absurd he.symm hcB
      · exact hd.2
  have hstep1 : (spineHom A none ∈ insert (spineHom A (some (n + 1)))
        {w | w = spineHom A none ∧ n ∈ A})
      = (spineHom A none ∈ insert (spineHom B (some (n + 1)))
        {w | w = spineHom B none ∧ n ∈ B}) := congrArg (spineHom A none ∈ ·) hset
  have hAB : n ∈ A ↔ n ∈ B := by
    rw [hA, hstep1, hnone]; exact hB.symm
  refine ⟨hAB, ?_⟩
  have hmemc : spineHom A (some (n + 1)) ∈ insert (spineHom B (some (n + 1)))
      {w | w = spineHom B none ∧ n ∈ B} := by
    rw [← hset]; exact Set.mem_insert _ _
  rcases Set.mem_insert_iff.mp hmemc with he | hd
  · exact he
  · exfalso; rw [hnone] at hcA; exact hcA hd.1

/-- All spine nodes agree once the roots do. -/
lemma spine_eq_all (A B : Set ℕ) (h0 : spineHom A (some 0) = spineHom B (some 0)) :
    ∀ n, spineHom A (some n) = spineHom B (some n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact (spine_step A B k ih).2

/-- The encoding `A ↦ spineHom A (some 0)` is injective. -/
theorem encode_injective :
    Function.Injective (fun A : Set ℕ => spineHom A (some 0)) := by
  intro A B h
  ext n
  exact (spine_step A B n (spine_eq_all A B h n)).1

/-- **R2 (the keystone).** The `ℵ₀`-carrier has at least continuum many states. -/
theorem ws12_carrier_card_continuum :
    2 ^ Cardinal.aleph0.{0} ≤ Cardinal.mk (νPk Cardinal.aleph0.{0}).X := by
  have h := Cardinal.mk_le_of_injective encode_injective
  rwa [Cardinal.mk_set, Cardinal.mk_nat] at h

/-- **R2 corollary.** The `ℵ₀`-carrier is strictly larger than `ℵ₀`. -/
theorem ws12_carrier_card_gt :
    Cardinal.aleph0.{0} < Cardinal.mk (νPk Cardinal.aleph0.{0}).X :=
  lt_of_lt_of_le (Cardinal.cantor _) ws12_carrier_card_continuum

end Spine

/-! ## Block 3 — generic conditional forms + `ℵ₀` instances (R5, R3, R4, R6) -/

/-- **R3 (generic).** If the reachable set is `≤ κ` and the carrier is strictly
larger, no state hereditarily reaches every state. -/
theorem ws12_no_hereditary_maximal' (u : (νPk κ).X)
    (hreach : Cardinal.mk ↥(ReachSet u) ≤ κ)
    (hgt : κ < Cardinal.mk (νPk κ).X) : ¬ ∀ v, Reaches u v := by
  intro hall
  have huniv : ReachSet u = Set.univ := Set.eq_univ_of_forall hall
  have hge : Cardinal.mk (νPk κ).X ≤ Cardinal.mk ↥(ReachSet u) := by
    rw [huniv]; exact le_of_eq (Cardinal.mk_univ).symm
  exact absurd (hge.trans hreach) (not_le.mpr hgt)

/-- **R4 (generic).** No surjection from the reachable set onto the carrier. -/
theorem ws12_no_hereditary_observer' (obs : (νPk κ).X)
    (hreach : Cardinal.mk ↥(ReachSet obs) ≤ κ)
    (hgt : κ < Cardinal.mk (νPk κ).X) :
    ¬ ∃ f : ↥(ReachSet obs) → (νPk κ).X, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact absurd ((Cardinal.mk_le_of_surjective hf).trans hreach) (not_le.mpr hgt)

/-- **R6 (generic).** Every hereditary horizon misses a state. -/
theorem ws12_hereditary_view_proper' (u : (νPk κ).X)
    (hreach : Cardinal.mk ↥(ReachSet u) ≤ κ)
    (hgt : κ < Cardinal.mk (νPk κ).X) : ∃ y, ¬ Reaches u y := by
  by_contra h
  push_neg at h
  exact ws12_no_hereditary_maximal' u hreach hgt h

/-- **R3 at `ℵ₀`.** -/
theorem ws12_no_hereditary_maximal (u : (νPk Cardinal.aleph0.{0}).X) :
    ¬ ∀ v, Reaches u v :=
  ws12_no_hereditary_maximal' u
    (ws12_reachable_card_le (le_refl _) u) ws12_carrier_card_gt

/-- **R4 at `ℵ₀`.** -/
theorem ws12_no_hereditary_observer (obs : (νPk Cardinal.aleph0.{0}).X) :
    ¬ ∃ f : ↥(ReachSet obs) → (νPk Cardinal.aleph0.{0}).X, Function.Surjective f :=
  ws12_no_hereditary_observer' obs
    (ws12_reachable_card_le (le_refl _) obs) ws12_carrier_card_gt

/-- **R6 at `ℵ₀`.** -/
theorem ws12_hereditary_view_proper (u : (νPk Cardinal.aleph0.{0}).X) :
    ∃ y, ¬ Reaches u y :=
  ws12_hereditary_view_proper' u
    (ws12_reachable_card_le (le_refl _) u) ws12_carrier_card_gt

/-! ## Block 4 — bundle -/

/-- The WS12 hereditary-scope upgrade at `κ₀ = ℵ₀`. Named for the scope upgrade it
delivers, not `ws12_resolved` (the uncountable strict bound and the general-`κ` gap
remain open remarks). -/
structure WS12Hereditary where
  reach_le : ∀ u : (νPk Cardinal.aleph0.{0}).X, Cardinal.mk ↥(ReachSet u) ≤ Cardinal.aleph0.{0}
  card_gt : Cardinal.aleph0.{0} < Cardinal.mk (νPk Cardinal.aleph0.{0}).X
  no_her_max : ∀ u : (νPk Cardinal.aleph0.{0}).X, ¬ ∀ v, Reaches u v
  no_her_obs : ∀ obs : (νPk Cardinal.aleph0.{0}).X,
    ¬ ∃ f : ↥(ReachSet obs) → (νPk Cardinal.aleph0.{0}).X, Function.Surjective f

/-- **The WS12 deliverable.** -/
theorem ws12_hereditary_scope : WS12Hereditary where
  reach_le := fun u => ws12_reachable_card_le (le_refl _) u
  card_gt := ws12_carrier_card_gt
  no_her_max := ws12_no_hereditary_maximal
  no_her_obs := ws12_no_hereditary_observer

end Series3.WS12
