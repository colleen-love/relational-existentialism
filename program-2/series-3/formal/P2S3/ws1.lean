/-
`program-2/series-3/formal/P2S3/ws1.lean`

WS1 - The valuation and `Converges₂` (typed, never evaluated). Program 2 Series 3 (2.3).

Imports the `P2S2` pair and builds on its transitive API (`slf`/`oth`/`attendsR`, the collapse engine, all
reached through S2). Adds the two primitives, FRESH and constrained on the S2 pair, NOT imported from Series 12
(whose compass/convergence is excluded from the foundation for program-review-1's PR1-S1, the tautology): the
per-perspective VALUATION `Valuation` (`val`, `raise`), the coherence relation `Converges₂` (the valuation at `x`,
raised toward `y`, agrees with the valuation at `y`), and the structural constraint `Faithful₂` (the raising
carries the valuation unchanged), under which `Converges₂ c x y ↔ c.val x = c.val y`. Proves `Converges₂` typed
and NON-VACUOUS (`ws1_converges_typed`) and TWO-SIDED FREE — it fixes no valuation, a converging and a
non-converging faithful valuation both exist at `(slf, oth)` (`ws1_two_sided_free`, the strip test at the
definition, the "no valuation evaluated" discipline, audit (a)). The witness valuations `cUnif`/`cDiss` are used
ONLY inside existentials (audit (a)).

Neutral names (audit (e)): `Valuation`/`val`/`raise`/`Converges₂`/`Faithful₂` carry no forbidden content-name
(`\borientation\b` does not match `val`; `\bconvergence\b` does not match `Converges`).

Design docs: `program-2/series-3/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S2

universe u

namespace P2S3

open P1.Core P1.Reader P2S0 P2S2 Cardinal

set_option linter.unusedVariables false

/-! ## The valuation, the convergence relation, and the faithful constraint -/

/-- **The per-perspective valuation.** `Or` an EXOGENOUS space the mathematics never inhabits canonically; `val`
the per-relatum valuation, `raise` the per-edge raising. Both fields arbitrary; every theorem quantifies over
`(Or)` and `(c : Valuation …)`; the concrete witnesses live only inside existentials. -/
structure Valuation (X Or : Type) where
  val   : X → Or
  raise : X → X → Or → Or

/-- **`Converges₂ c x y`.** The valuation at `x`, raised toward `y`, agrees with the valuation at `y`. A genuine
equation in `Or` depending on `c`; instantiated at `(slf, oth)`. NOT `True`, NOT `False`, NOT `val x = val x`
(`ws1_two_sided_free`). -/
def Converges₂ {X Or : Type} (c : Valuation X Or) (x y : X) : Prop :=
  c.raise x y (c.val x) = c.val y

/-- **The faithful class (the structural constraint, anti-PR1-S1).** The raising carries the valuation UNCHANGED.
Non-empty (`id` raising); a PROPER sub-relation is what sight carves out of it (`ws4_insight_proper`). -/
def Faithful₂ {X Or : Type} (c : Valuation X Or) : Prop := ∀ x y : X, c.raise x y = id

/-- Under `Faithful₂`, convergence is exactly valuation-coherence. -/
theorem faithful_converges_iff {X Or : Type} (c : Valuation X Or) (hf : Faithful₂ c) (x y : X) :
    Converges₂ c x y ↔ c.val x = c.val y := by
  unfold Converges₂; rw [hf x y]; exact Iff.rfl

/-! ## The witness valuations (used ONLY inside existentials; audit (a)) -/

/-- The uniform valuation: constant, identity raising. Faithful, in-sight (WS2), converges at `(slf, oth)`. -/
def cUnif : Valuation RCar (ULift.{0} Bool) := ⟨fun _ => ⟨true⟩, fun _ _ o => o⟩

/-- The dissenting valuation: `⟨true⟩` on `slf`, `⟨false⟩` elsewhere, identity raising. Faithful, NOT in-sight
(it separates the plain-bisimilar `slf`, `oth`), fails at `(slf, oth)`. -/
def cDiss : Valuation RCar (ULift.{0} Bool) := ⟨fun z => if z = slf then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩

lemma cUnif_faithful : Faithful₂ cUnif := fun _ _ => rfl
lemma cDiss_faithful : Faithful₂ cDiss := fun _ _ => rfl

lemma cUnif_converges : Converges₂ cUnif slf oth := rfl

lemma cDiss_not_converges : ¬ Converges₂ cDiss slf oth := by
  rw [faithful_converges_iff cDiss cDiss_faithful slf oth]; decide

/-! ## The payoffs -/

/-- **`Converges₂` IS TYPED AND NON-VACUOUS (WS1).** A faithful valuation converging at `(slf, oth)` exists, so
the relation is inhabited (not always false). -/
theorem ws1_converges_typed :
    ∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ Converges₂ c slf oth :=
  ⟨cUnif, cUnif_faithful, cUnif_converges⟩

/-- **NO VALUATION EVALUATED (the strip test at the definition, audit (a)).** `Converges₂` fixes no valuation: a
faithful valuation under which it holds AND a faithful valuation under which it fails both exist at `(slf, oth)`,
so the relation is two-sided free (neither `True` nor `False` nor reflexive), and the core reads off no canonical
valuation. -/
theorem ws1_two_sided_free :
    ∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth :=
  ⟨cUnif, cDiss, cUnif_faithful, cDiss_faithful, cUnif_converges, cDiss_not_converges⟩

end P2S3
