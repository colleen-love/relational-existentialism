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

open P1.Core Cardinal

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

end P2S0
