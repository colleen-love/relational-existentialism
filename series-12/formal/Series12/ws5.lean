/-
`series-12/formal/Series12/ws5.lean`

WS5 - The verdict as a function, and the generalized neutrality. Series 12.

Consumes WS1-WS4. Defines the verdict type `Series12Verdict`, the data-level `ConvergenceFork` (which
disjunct of the trichotomy WS4 discharged, design-review-1 Finding 4), and `verdictOfFork` (the verdict
BRANCHES on the fork, never a returned constant). The concrete verdict `ws5_verdict` is computed from the
`underdet` fork (the model pair), so `ws5_verdict = shapeDrawn` is a THEOREM. And the generalized neutrality:
adjoining ANY name for the inhabitant changes no downstream theorem.

BUILD NOTE. The verdict type + fork are defined here (the earliest consumer, importing WS4 whose `Converges`/
`NonDegenerate` the fork's `underdet` constructor references); WS7 imports WS5 and reuses them for the audit.
The type is co-owned (README §3); its physical home in `ws5.lean` respects the WS5 → WS6 → WS7 order.

Design doc: `series-12/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws4

universe u

namespace Series12.WS5

open Series12.WS1 Series12.WS2 Series12.WS3 Series12.WS4 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-! ## The verdict type and the convergence fork (README §3, Finding 4) -/

/-- **The verdict.** -/
inductive Series12Verdict
  | shapeDrawn | convergenceDecided | Partial | Refuted | Circular
  deriving DecidableEq

/-- **The convergence fork (data-level, Finding 4), over a compass CLASS `InClass` (PR2-S1).** WHICH disjunct
of the trichotomy was discharged over the given compass class, each constructor carrying its proof.
Data-level so the verdict can CASE on it. Parameterizing the class lets the SAME genuine edge be forked over
the full faithful class (underdetermined) and over the in-sight sub-class (decided), so `convergenceDecided`
is reached AT THE EDGE, not at a reflexive non-edge. -/
inductive ConvergenceFork {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (InClass : Compass dest reify (ULift.{u} Bool) → Prop) (a b : X) : Type u
  | forcedHolds (h : ∀ (c : Compass dest reify (ULift.{u} Bool)), InClass c → Converges dest reify c a b)
  | forcedFails (h : ∀ (c : Compass dest reify (ULift.{u} Bool)), InClass c → ¬ Converges dest reify c a b)
  | underdet    (h : ∃ c₁ c₂ : Compass dest reify (ULift.{u} Bool),
                       InClass c₁ ∧ InClass c₂
                       ∧ Converges dest reify c₁ a b ∧ ¬ Converges dest reify c₂ a b
                       ∧ NonDegenerate dest reify c₁ a b ∧ NonDegenerate dest reify c₂ a b)

/-- **The verdict BRANCHES on the certified fork (Finding 4), not a returned constant.** -/
def verdictOfFork {X : Type u} {dest : X → PkObj κ X} {reify : PkObj κ X → X}
    {InClass : Compass dest reify (ULift.{u} Bool) → Prop} {a b : X} :
    ConvergenceFork dest reify InClass a b → Series12Verdict
  | .forcedHolds _ => .convergenceDecided
  | .forcedFails _ => .convergenceDecided
  | .underdet    _ => .shapeDrawn

/-- The fork WS4 discharged at the genuine part-and-whole edge `(aW, bW)`, over the FULL faithful class:
`underdet` (the faithful model pair). -/
noncomputable def s12_fork (hinf : ℵ₀ ≤ κ) :
    ConvergenceFork (destW hinf) (reifyW hinf) Faithful aW bW :=
  .underdet (ws4_underdetermined hinf).2

/-- The fork at the SAME genuine edge `(aW, bW)`, over the IN-SIGHT faithful sub-class (`Faithful ∧
BisimInvariant`): `forcedHolds` (every sight-bound faithful compass coheres, `ws4_decided_within_sight`), so
`convergenceDecided` is genuinely constructible AT THE EDGE, and the fork is open where the verdict lives
(PR2-S1). The class is inhabited (`ws4_insight_inhabited`, not a vacuous `forcedHolds`); DISCLOSED (PR3-R1):
on this carrier its members are orientation-uniform (`ws4_sight_is_uniform`), so the decided arm's compasses
are all orientation-constant, decided because sight collapses to the One. -/
noncomputable def s12_fork_insight (hinf : ℵ₀ ≤ κ) :
    ConvergenceFork (destW hinf) (reifyW hinf)
      (fun c => Faithful c ∧ BisimInvariant (destW hinf) c) aW bW :=
  .forcedHolds (fun c h => ws4_decided_within_sight hinf c h.1 h.2)

/-- **The verdict, computed by casing on the fork.** -/
noncomputable def ws5_verdict (hinf : ℵ₀ ≤ κ) : Series12Verdict := verdictOfFork (s12_fork hinf)

/-- `ws5_verdict = shapeDrawn` is a THEOREM (the fork is `underdet`), not a definitional constant. -/
theorem ws5_verdict_eq (hinf : ℵ₀ ≤ κ) : ws5_verdict hinf = Series12Verdict.shapeDrawn := rfl

/-- **THE VERDICT REACHES BOTH VALUES AT THE GENUINE EDGE (falsifiability, PR2-S1).** `verdictOfFork` is
genuinely non-constant at the SAME genuine part-and-whole edge `(aW, bW)`: over the full faithful class the
fork is `underdet` and the verdict is `shapeDrawn`; over the in-sight faithful sub-class the fork is
`forcedHolds` (`ws4_decided_within_sight`) and the verdict is `convergenceDecided`. So SHAPE-DRAWN is
FALSIFIABLE where the verdict is computed (restricting to what the structure sees closes the fork), not by a
triviality at a reflexive non-edge. -/
theorem ws5_verdict_reaches_both (hinf : ℵ₀ ≤ κ) :
    verdictOfFork (s12_fork hinf) = Series12Verdict.shapeDrawn
  ∧ verdictOfFork (s12_fork_insight hinf) = Series12Verdict.convergenceDecided :=
  ⟨rfl, rfl⟩

theorem ws5_verdict_not_decided (hinf : ℵ₀ ≤ κ) : ws5_verdict hinf ≠ .convergenceDecided := by
  rw [ws5_verdict_eq hinf]; decide
theorem ws5_verdict_not_partial (hinf : ℵ₀ ≤ κ) : ws5_verdict hinf ≠ .Partial := by
  rw [ws5_verdict_eq hinf]; decide
theorem ws5_verdict_not_circular (hinf : ℵ₀ ≤ κ) : ws5_verdict hinf ≠ .Circular := by
  rw [ws5_verdict_eq hinf]; decide

/-! ## The generalized neutrality (the silence as a theorem) -/

/-- **GENERALIZED NEUTRALITY.** Adjoining ANY name for the inhabitant, a map `name : Or → Name` into an
arbitrary `Name`, changes no downstream theorem: the payoffs never mention `name`, so they hold identically
for every naming. The silence is the theorem. -/
theorem ws5_name_neutral {Name : Type u} (name : ULift.{u} Bool → Name) (hinf : ℵ₀ ≤ κ) :
    Many (destWL hinf)
  ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  ⟨ws2_many_witness hinf, ws4_underdetermined_pair hinf⟩

/-- **Neutrality across ALL names at once.** One theorem, universally quantified over names. -/
theorem ws5_name_neutral_all (hinf : ℵ₀ ≤ κ) :
    ∀ {Name : Type u} (name : ULift.{u} Bool → Name),
      Many (destWL hinf)
    ∧ (∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
          Converges (destW hinf) (reifyW hinf) c₁ aW bW
        ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW) :=
  fun {Name} name => ws5_name_neutral name hinf

end Series12.WS5
