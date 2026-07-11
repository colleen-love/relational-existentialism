/-
`series-03/formal/ws13.lean`

WS13 (`series-03/spec/ws13/02-design.md`): **pairs and relations as states.** On the
terminal carrier `νP_κ`, Lambek makes `str` a bijection, so every `< κ`-sized subset
of the carrier is the unfolding of exactly one state: an internal state-former
`mkState`. This workstream shows that ordered pairs of states, and hence `< κ`
binary relations between states, exist *as states*:

* **`mkState` (Block 0).** The `lambek`-inverse state-former, with `str_mkState`,
  `mkState_str`, `mkState_inj`. Exported for reuse (WS15 consumes it).
* **Kuratowski pairing (P1).** `pairK` is injective in both arguments
  (`ws13_pair_inj : Function.Injective2 pairK`).
* **relation reification (P3, P4).** `reify` sends a `< κ` relation to a state whose
  unfolding is exactly the set of its pair-states; `reify` is faithful
  (`ws13_reify_inj`) and membership of a pair-state decides the relation
  (`ws13_reify_mem`).
* **iterability (P6).** Relations between reified relations are again states
  (`ws13_reify_iterated`).

Bundle `ws13_reification`. Everything is `noncomputable` (choice enters only through
`mkState`'s `lambek`-inverse); axiom-clean beyond Mathlib's standard three,
`sorry`-free.

Built on `ws1`/`ws2`: `PkObj`, `lambek`, `mk_singleton_lt`, `νPk`, `νPk_terminal`.
-/
import ws2

universe u

open Cardinal Series03.WS1 Series03.WS2

namespace Series03.WS13

variable {κ : Cardinal.{u}}

/-! ## Block 0 — the state-former (exported interface) -/

/-- `dest = str` on the terminal carrier, packaged as an equivalence (Lambek). -/
noncomputable def destEquivPk (κ : Cardinal.{u}) : (νPk κ).X ≃ PkObj κ (νPk κ).X :=
  Equiv.ofBijective (νPk κ).str (lambek (νPk_terminal κ))

/-- The internal state-former: the unique state whose unfolding is `s`. -/
noncomputable def mkState (s : PkObj κ (νPk κ).X) : (νPk κ).X :=
  (destEquivPk κ).symm s

@[simp] theorem str_mkState (s : PkObj κ (νPk κ).X) : (νPk κ).str (mkState s) = s :=
  (destEquivPk κ).apply_symm_apply s

@[simp] theorem mkState_str (u : (νPk κ).X) : mkState ((νPk κ).str u) = u :=
  (destEquivPk κ).symm_apply_apply u

theorem mkState_inj : Function.Injective (mkState (κ := κ)) :=
  (destEquivPk κ).symm.injective

/-! ## Block 1 — small-set cardinality helpers -/

/-- A two-element set is `< κ` (needs `ℵ₀ ≤ κ`). -/
theorem mk_pair_lt (hinf : ℵ₀ ≤ κ) {α : Type u} (x y : α) :
    Cardinal.mk ↥({x, y} : Set α) < κ := by
  have hfin : ({x, y} : Set α).Finite := (Set.finite_singleton y).insert x
  haveI : Finite ↥({x, y} : Set α) := hfin.to_subtype
  exact lt_of_lt_of_le (Cardinal.mk_lt_aleph0_iff.mpr ‹_›) hinf

/-! ## Block 2 — Kuratowski pairing (P1) -/

/-- The singleton state `{x}`. -/
noncomputable def sing (hinf : ℵ₀ ≤ κ) (x : (νPk κ).X) : (νPk κ).X :=
  mkState ⟨{x}, mk_singleton_lt hinf x⟩

/-- The doubleton state `{x, y}`. -/
noncomputable def doub (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X) : (νPk κ).X :=
  mkState ⟨{x, y}, mk_pair_lt hinf x y⟩

/-- The Kuratowski pair state `{{x}, {x, y}}`. -/
noncomputable def pairK (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X) : (νPk κ).X :=
  mkState ⟨{sing hinf x, doub hinf x y}, mk_pair_lt hinf _ _⟩

@[simp] lemma str_sing (hinf : ℵ₀ ≤ κ) (x : (νPk κ).X) :
    ((νPk κ).str (sing hinf x)).1 = {x} := by simp [sing]

@[simp] lemma str_doub (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X) :
    ((νPk κ).str (doub hinf x y)).1 = {x, y} := by simp [doub]

lemma sing_inj (hinf : ℵ₀ ≤ κ) : Function.Injective (sing hinf) := by
  intro x y h
  have hs : ({x} : Set (νPk κ).X) = {y} := by
    have := congrArg (fun s => ((νPk κ).str s).1) h; simpa using this
  exact Set.singleton_eq_singleton_iff.mp hs

/-- `{x, x} = {x}` collapses `doub` to `sing`. -/
lemma doub_self (hinf : ℵ₀ ≤ κ) (x : (νPk κ).X) : doub hinf x x = sing hinf x := by
  rw [doub, sing]; congr 1; apply Subtype.ext; simp

lemma doub_eq_iff (hinf : ℵ₀ ≤ κ) {x y x' y' : (νPk κ).X} :
    doub hinf x y = doub hinf x' y' ↔ ({x, y} : Set (νPk κ).X) = {x', y'} := by
  constructor
  · intro h; have := congrArg (fun s => ((νPk κ).str s).1) h; simpa using this
  · intro h; rw [doub, doub]; congr 1; exact Subtype.ext h

/-- A singleton state never equals a genuine doubleton state (different unfolding
cardinalities). -/
lemma sing_ne_doub (hinf : ℵ₀ ≤ κ) {x y z : (νPk κ).X} (h : x ≠ y) :
    sing hinf z ≠ doub hinf x y := by
  intro he
  have hs : ({z} : Set (νPk κ).X) = {x, y} := by
    have := congrArg (fun s => ((νPk κ).str s).1) he; simpa using this
  have hxz : x = z := by
    have hx : x ∈ ({z} : Set (νPk κ).X) := by rw [hs]; exact Set.mem_insert x {y}
    simpa using hx
  have hyz : y = z := by
    have hy : y ∈ ({z} : Set (νPk κ).X) := by rw [hs]; exact Set.mem_insert_of_mem x rfl
    simpa using hy
  exact h (hxz.trans hyz.symm)

/-- **P1.** Kuratowski pairing is injective in both arguments. -/
theorem ws13_pair_inj (hinf : ℵ₀ ≤ κ) : Function.Injective2 (pairK (κ := κ) hinf) := by
  intro x₁ x₂ y₁ y₂ h
  -- the two Kuratowski unfoldings coincide
  have hpair : ({sing hinf x₁, doub hinf x₁ y₁} : Set (νPk κ).X)
      = {sing hinf x₂, doub hinf x₂ y₂} :=
    congrArg Subtype.val (mkState_inj h)
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- straight case: sing x₁ = sing x₂, doub x₁ y₁ = doub x₂ y₂
    have hxx : x₁ = x₂ := sing_inj hinf h1
    subst hxx
    have hsets : ({x₁, y₁} : Set (νPk κ).X) = {x₁, y₂} := (doub_eq_iff hinf).mp h2
    rcases Set.pair_eq_pair_iff.mp hsets with ⟨_, hy⟩ | ⟨hxy', hyx⟩
    · exact ⟨rfl, hy⟩
    · exact ⟨rfl, hyx.trans hxy'⟩
  · -- cross case: sing x₁ = doub x₂ y₂ and doub x₁ y₁ = sing x₂
    by_cases hx2y2 : x₂ = y₂
    · subst hx2y2
      -- doub x₂ x₂ = sing x₂, so h1 : sing x₁ = sing x₂
      rw [doub_self] at h1
      have hxx : x₁ = x₂ := sing_inj hinf h1
      subst hxx
      -- h2 : doub x₁ y₁ = sing x₁, so x₁ = y₁
      by_cases hxy : x₁ = y₁
      · exact ⟨rfl, hxy.symm⟩
      · exact absurd h2.symm (sing_ne_doub hinf hxy)
    · exact absurd h1 (sing_ne_doub hinf hx2y2)

/-! ## Block 3 — reification (P3, P4) -/

/-- The uncurried pairing function. -/
noncomputable def pairFun (hinf : ℵ₀ ≤ κ) : (νPk κ).X × (νPk κ).X → (νPk κ).X :=
  fun p => pairK hinf p.1 p.2

lemma pairFun_inj (hinf : ℵ₀ ≤ κ) : Function.Injective (pairFun hinf) := by
  intro p q h
  obtain ⟨h1, h2⟩ := ws13_pair_inj hinf h
  exact Prod.ext h1 h2

/-- The reification of a `< κ` binary relation `R` to a state: the state whose
unfolding is the set of pair-states of `R`. -/
noncomputable def reify (hinf : ℵ₀ ≤ κ) (R : Set ((νPk κ).X × (νPk κ).X))
    (hR : Cardinal.mk ↥R < κ) : (νPk κ).X :=
  mkState ⟨pairFun hinf '' R, lt_of_le_of_lt Cardinal.mk_image_le hR⟩

/-- **P3.** Reification is faithful: distinct relations get distinct states. -/
theorem ws13_reify_inj (hinf : ℵ₀ ≤ κ) {R S : Set ((νPk κ).X × (νPk κ).X)}
    {hR : Cardinal.mk ↥R < κ} {hS : Cardinal.mk ↥S < κ}
    (h : reify hinf R hR = reify hinf S hS) : R = S := by
  have h2 : pairFun hinf '' R = pairFun hinf '' S := congrArg Subtype.val (mkState_inj h)
  exact Set.image_injective.mpr (pairFun_inj hinf) h2

/-- **P4.** Reified relations are usable: membership of a pair-state in the reified
state decides the relation. -/
theorem ws13_reify_mem (hinf : ℵ₀ ≤ κ) (R : Set ((νPk κ).X × (νPk κ).X))
    (hR : Cardinal.mk ↥R < κ) (x y : (νPk κ).X) :
    pairK hinf x y ∈ ((νPk κ).str (reify hinf R hR)).1 ↔ (x, y) ∈ R := by
  rw [reify, str_mkState]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have : p = (x, y) := pairFun_inj hinf hpe
    rwa [this] at hp
  · intro h; exact ⟨(x, y), h, rfl⟩

/-! ## Block 4 — iteration (P6) and the bundle -/

/-- **P6.** Relations between reified relations are again states — the construction
is iterable. -/
theorem ws13_reify_iterated (hinf : ℵ₀ ≤ κ) (R S : Set ((νPk κ).X × (νPk κ).X))
    (hR : Cardinal.mk ↥R < κ) (hS : Cardinal.mk ↥S < κ) :
    ∃ r : (νPk κ).X,
      ((νPk κ).str r).1 = {pairK hinf (reify hinf R hR) (reify hinf S hS)} :=
  ⟨mkState ⟨{pairK hinf (reify hinf R hR) (reify hinf S hS)}, mk_singleton_lt hinf _⟩, by
    simp [str_mkState]⟩

/-- The WS13 reification interface. -/
structure WS13Reification (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) where
  pair_inj : Function.Injective2 (pairK (κ := κ) hinf)
  reify_inj : ∀ {R S : Set ((νPk κ).X × (νPk κ).X)}
    {hR : Cardinal.mk ↥R < κ} {hS : Cardinal.mk ↥S < κ},
    reify hinf R hR = reify hinf S hS → R = S
  reify_mem : ∀ (R : Set ((νPk κ).X × (νPk κ).X)) (hR : Cardinal.mk ↥R < κ)
    (x y : (νPk κ).X),
    pairK hinf x y ∈ ((νPk κ).str (reify hinf R hR)).1 ↔ (x, y) ∈ R
  iterated : ∀ (R S : Set ((νPk κ).X × (νPk κ).X))
    (hR : Cardinal.mk ↥R < κ) (hS : Cardinal.mk ↥S < κ),
    ∃ r : (νPk κ).X,
      ((νPk κ).str r).1 = {pairK hinf (reify hinf R hR) (reify hinf S hS)}

/-- **The WS13 deliverable.** -/
theorem ws13_reification (hinf : ℵ₀ ≤ κ) : WS13Reification κ hinf where
  pair_inj := ws13_pair_inj hinf
  reify_inj := fun h => ws13_reify_inj hinf h
  reify_mem := ws13_reify_mem hinf
  iterated := ws13_reify_iterated hinf

end Series03.WS13
