/-
`program-2/series-0/formal/P2S0/ws1.lean`

WS1 - The attention carrier and reification. Program 2 Series 0 (2.0), the blocking workstream.

This file IMPORTS the P1 foundation (`import P1`, Program 2 permits it) and builds ON it, rather than
transcribing it. It fixes the ONE new carrier of the series: the ATTENTION CARRIER `attends : X → Finset X`
(finite out-attention, the SOLE ontological bound), the directed knowing (`knows`), the symmetric relating
(`sym`), the passive in-attention (`attendedBy`, possibly infinite), the view of finite out-attention as a
`PkObj κ`-coalgebra (`finsetToPk`, `outDest`, whose neighborhoods are finite for EVERY κ, so κ never bounds
the world), and the symmetric reduct (`symDest`, whose κ is AMBIENT CARRIER SIZE only, audit (a)). On this
carrier it establishes the reification section on the FINITE functor (`FinReify`, the honest analog of P1's
`IsReify`; total `IsReify` on `PkObj κ` is unsatisfiable for the finite functor, disclosed in
`charter-status.md`), proved to EXIST non-vacuously (`ws1_reification_exists`, on a carrier where
`Finset X ≃ X`), the bound proved finite with no cardinal ceiling (`ws1_bound_is_finite_attention`), and the
finite tower (`finReifyStep`, `finTowerN`, `ws1_tower_monotone`).

Design docs: `program-2/series-0/spec/ws1-design.md`; shared objects `spec/README.md` §2.2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P1

universe u

namespace P2S0

open P1.Core P1.Reader Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## Finite out-attention as a `PkObj κ`-coalgebra -/

/-- **A `Finset` as a bounded pattern.** A finite set has cardinality `< ℵ₀ ≤ κ`, so `κ` never bounds it;
the injector needs only that the `Finset` is finite, NOT that the carrier `X` is finite. -/
noncomputable def finsetToPk (hinf : ℵ₀ ≤ κ) {X : Type u} (s : Finset X) : PkObj κ X :=
  ⟨↑s, by
    haveI : Finite (↥(↑s : Set X)) := s.finite_toSet.to_subtype
    exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) hinf⟩

@[simp] lemma finsetToPk_val (hinf : ℵ₀ ≤ κ) {X : Type u} (s : Finset X) :
    (finsetToPk hinf s).1 = (↑s : Set X) := rfl

/-- **A bounded singleton over any type** (a singleton has cardinal `1 < κ`). -/
noncomputable def pkSingle (hinf : ℵ₀ ≤ κ) {Y : Type u} (y : Y) : PkObj κ Y :=
  ⟨{y}, mk_singleton_lt hinf y⟩

@[simp] lemma pkSingle_val (hinf : ℵ₀ ≤ κ) {Y : Type u} (y : Y) : (pkSingle hinf y).1 = {y} := rfl

/-- **The directed knowing.** `x` KNOWS `y` iff `x` actively attends `y`. -/
def knows {X : Type u} (attends : X → Finset X) (x y : X) : Prop := y ∈ attends x
/-- **The symmetric relating**, blind to direction: `x` and `y` relate iff either attends the other. -/
def sym {X : Type u} (attends : X → Finset X) (x y : X) : Prop := y ∈ attends x ∨ x ∈ attends y
/-- **The passive in-attention** (possibly UNBOUNDED in-degree, the passive side). -/
def attendedBy {X : Type u} (attends : X → Finset X) (x : X) : Set X := {z | x ∈ attends z}

/-- **The generating coalgebra: finite out-attention.** A finite-powerset coalgebra; its neighborhoods are
finite for EVERY κ. -/
noncomputable def outDest (hinf : ℵ₀ ≤ κ) {X : Type u} (attends : X → Finset X) : X → PkObj κ X :=
  fun x => finsetToPk hinf (attends x)

/-- **The symmetric relating as a `PkObj κ`-coalgebra.** Its neighborhoods `{y | sym x y}` may be infinite
(unbounded in-degree); `κ` here is AMBIENT CARRIER SIZE (`hcar : mk X < κ`), never an ontological ceiling
(audit (a)). -/
noncomputable def symDest (hinf : ℵ₀ ≤ κ) {X : Type u} (hcar : Cardinal.mk X < κ)
    (attends : X → Finset X) : X → PkObj κ X :=
  fun x => ⟨{y | sym attends x y}, lt_of_le_of_lt (Cardinal.mk_subtype_le _) hcar⟩

/-! ## The reification section on the FINITE functor -/

/-- **Reification on the finite functor.** A section of `attends`: `attends (reify s) = s` for all finite
`s`. The honest analog of P1's `IsReify`; total `IsReify` on `PkObj κ` is unsatisfiable for the finite
functor (finite images vs infinite patterns), disclosed. -/
def FinReify {X : Type u} (attends : X → Finset X) (reify : Finset X → X) : Prop :=
  ∀ s : Finset X, attends (reify s) = s

/-- A finite section is injective. -/
theorem ws1_finreify_injective {X : Type u} (attends : X → Finset X) (reify : Finset X → X)
    (h : FinReify attends reify) : Function.Injective reify := by
  intro s₁ s₂ he
  have hd : attends (reify s₁) = attends (reify s₂) := by rw [he]
  rwa [h s₁, h s₂] at hd

/-- **THE REIFICATION EXISTS (non-vacuously).** There is a carrier with a finite-out-attention map and a
`reify : Finset X → X` sectioning it, injective. Discharged on an infinite carrier where `Finset X ≃ X`
(`Cardinal.mk_finset_of_infinite`), so the section is a bijection: `Ω ≅ F(Ω)` realized for the finite
functor. If the finite functor admitted NO section, this is the pre-registered OBSTRUCTED outcome. -/
theorem ws1_reification_exists :
    ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X),
      FinReify attends reify ∧ Function.Injective reify := by
  obtain ⟨e⟩ : Nonempty (Finset ℕ ≃ ℕ) := Cardinal.eq.mp (Cardinal.mk_finset_of_infinite ℕ)
  exact ⟨ℕ, e.symm, e, fun s => e.symm_apply_apply s, e.injective⟩

/-- **THE ONTOLOGICAL BOUND IS FINITE ATTENTION, NO CARDINAL CEILING (audit (a)).** The out-neighborhoods
are strictly FINITE (`< ℵ₀`), uniformly in `κ`: the bound is ℵ₀ (finiteness), below ANY infinite κ, never
κ itself. -/
theorem ws1_bound_is_finite_attention (hinf : ℵ₀ ≤ κ) {X : Type u} (attends : X → Finset X) :
    ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < Cardinal.aleph0 := by
  intro x
  haveI : Finite (↥((outDest hinf attends x).1)) := by
    show Finite (↥(↑(attends x) : Set X))
    exact (attends x).finite_toSet.to_subtype
  exact Cardinal.lt_aleph0_of_finite _

/-! ## The reification tower on the finite functor (the companion the tick will need) -/

/-- One reification step: adjoin every relatum reifiable from a non-empty finite pattern within `Ωα`. -/
def finReifyStep {X : Type u} (reify : Finset X → X) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : Finset X, ↑s ⊆ Ωα ∧ s.Nonempty ∧ x = reify s }

/-- A concrete ℕ-indexed iterate of the finite tower. -/
def finTowerN {X : Type u} (reify : Finset X → X) (Ω₀ : Set X) : ℕ → Set X
  | 0 => Ω₀
  | n + 1 => finReifyStep reify (finTowerN reify Ω₀ n)

theorem ws1_tower_step_subset {X : Type u} (reify : Finset X → X) (Ω₀ : Set X) (n : ℕ) :
    finTowerN reify Ω₀ n ⊆ finTowerN reify Ω₀ (n + 1) := fun _ hx => Or.inl hx

theorem ws1_tower_monotone {X : Type u} (reify : Finset X → X) (Ω₀ : Set X) {m n : ℕ} (hmn : m ≤ n) :
    finTowerN reify Ω₀ m ⊆ finTowerN reify Ω₀ n := by
  induction hmn with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (ws1_tower_step_subset reify Ω₀ _)

/-! ## The unified witness (Charter Extension 1): the self, its reified self-relation, the first other

One witness (`Fin 3`, at `Cardinal.{0}`) carrying the self `s0` (self-loop, the self-relation), its reified
self-relation `s1` (the FIRST OTHER, `= reifyU {s0}`), and the reification iterated `s2`. Reification CREATES
`s1`, non-recoverable from `s0` at the tower level; the WS3 asymmetry (`ws3.lean`) is the self against this
SAME first other. This is the shared witness the extension (`spec/ext1-design.md`, R1-R2) requires, drawing the
separation from the imported `P1.Reader.rankLift` / `ws2_many_general` mechanism (a reified relatum ranks above
its constituent, so it is plain-bisimilar to a base relatum yet label-separated). The first other is a MINTED,
self-manufactured distinction (non-recoverable, hence a genuine import, consistent with the inherited collapse),
NOT multiplicity from relating alone. -/

/-- The self (self-relation: the self-loop). -/
def s0 : Fin 3 := 0
/-- The reified self-relation: the FIRST OTHER (`= reifyU {s0}`). -/
def s1 : Fin 3 := 1
/-- The reification iterated (the proliferation). -/
def s2 : Fin 3 := 2

/-- `s0` self-loops (attends itself); `s1` attends `s0`; `s2` attends `s1`. -/
def attendsU : Fin 3 → Finset (Fin 3) := fun x => if x = s0 then {s0} else if x = s1 then {s0} else {s1}
/-- The tower level: `s0` at 0 (base/self), `s1` at 1 (reified self-relation), `s2` at 2. -/
def rankU : Fin 3 → ℕ := fun x => if x = s0 then 0 else if x = s1 then 1 else 2
/-- Pointwise reification: the self-relation `{s0}` reifies to `s1`; `{s1}` to `s2`. -/
def reifyU : Finset (Fin 3) → Fin 3 := fun s => if s = {s0} then s1 else if s = {s1} then s2 else s0

lemma attendsU_s1 : attendsU s1 = {s0} := rfl
lemma reifyU_self : reifyU {s0} = s1 := rfl
lemma reify_sections_self : attendsU (reifyU {s0}) = {s0} := rfl

lemma attendsU_nonempty : ∀ x : Fin 3, (attendsU x).Nonempty := by decide

lemma outDestU_ne_empty {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) (x : Fin 3) :
    (outDest hinf attendsU x).1 ≠ ∅ := by
  show (↑(attendsU x) : Set (Fin 3)) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsU_nonempty x))

lemma SHNE_U {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) (x : Fin 3) : SHNE (outDest hinf attendsU) x :=
  fun v _ => outDestU_ne_empty hinf v

/-- The general fact `plainOf (rankLift dest rank) = dest` (the tower label forgets to the bare relating). -/
lemma plainOf_rankLift {κ : Cardinal.{0}} (dest : Fin 3 → PkObj κ (Fin 3)) (rank : Fin 3 → ℕ) :
    plainOf (rankLift dest rank) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨rank x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- The tower-labelled edge set at `x`. -/
lemma rankLiftU_val {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) (x : Fin 3) :
    (rankLift (outDest hinf attendsU) rankU x).1
      = (fun z => ((⟨rankU x⟩ : ULift.{0} ℕ), z)) '' (↑(attendsU x) : Set (Fin 3)) := rfl

/-- **The first other is label-separated from the self.** No tower-bisimulation relates `s1` and `s0`:
`s1`'s edge carries tower level `rankU s1 = 1`, `s0`'s only edge carries `rankU s0 = 0`. The mechanism of
`P1.Reader.ws2_many_general` (a reified relatum outranks its base). -/
lemma firstOther_label_sep {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (rankLift (outDest hinf attendsU) rankU) R ∧ R s1 s0 := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR s1 s0 hRel
  have hedge : ((⟨rankU s1⟩ : ULift.{0} ℕ), s0)
      ∈ (rankLift (outDest hinf attendsU) rankU s1).1 := by
    rw [rankLiftU_val]; exact ⟨s0, by simp [attendsU_s1], rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [rankLiftU_val] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have : rankU s1 = rankU s0 := congrArg ULift.down hfst
  exact absurd this (by decide)

/-- **THE FIRST OTHER (Charter Extension 1, R1).** Reifying the self-relation `{s0}` yields `s1`, which
SECTIONS it (`attendsU (reifyU {s0}) = {s0}`, a real pointwise section), and `s1` is plain-bisimilar to the
self `s0` over the bare out-attention relating (the imported collapse engine `ws1_atomless_bisim`) yet NOT
recoverable from it (tower-separated, `firstOther_label_sep`): a genuine, non-recoverable first other, created
by reification and participating in the WS3 asymmetry. This is the reification target the ground actually
needs, replacing the inert counting-bijection as the WS5 flag (R4). -/
theorem ws1_first_other {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    reifyU {s0} = s1
  ∧ attendsU (reifyU {s0}) = {s0}
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0 := by
  refine ⟨rfl, rfl, ?_, firstOther_label_sep hinf⟩
  rw [plainOf_rankLift]
  exact ws1_atomless_bisim (outDest hinf attendsU) s1 s0 (SHNE_U hinf s1) (SHNE_U hinf s0)

end P2S0
