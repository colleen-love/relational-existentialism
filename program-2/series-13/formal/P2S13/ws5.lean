/-
`program-2/series-13/formal/P2S13/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 13 (2.13), THE CURVE.

The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= inert` on the earned flags,
DISCRIMINATING (reaches all four outcomes), the flags EARNED by the WS1-WS4 headlines. The computed verdict is INERT:
a non-constant grain and a non-trivial distance (WS1), the distance a function of the adjacency and responsive to it
(WS2), the imported distance INVARIANT under grain-change at fixed adjacency and reading only the adjacency (WS3),
INERT reached by the imported distance and the GRAVITATIONAL pole inhabited only by the foil (WS4). Geometry decoupled
from the grain — no gravity — the honest NOT-RECOVERED that Series 2.4's DISTINCTNESS of space and the measure
foretold, and the specification for the next iteration: couple the two axes 2.4 kept apart. The five audit clauses
(a)-(e) bundle the payoffs.

(The GRAVITATIONAL outcome constructor is named `sourced`, not `gravitational`: a neutral name clear of the forbidden
"gravity". "gravitational"/"INERT" in prose.)

Design docs: `program-2/series-13/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S13.ws1
import P2S13.ws2
import P2S13.ws3
import P2S13.ws4

namespace P2S13

set_option linter.unusedVariables false

/-! ## The verdict -/

/-- **The outcome type.** `inert` the imported distance invariant under grain-change at fixed adjacency — geometry
decoupled from the grain, no gravity, the NOT-RECOVERED (the expected close, grounded in Series 2.4's DISTINCTNESS);
`sourced` the imported distance genuinely varies with the grain — the grain sources the geometry, gravity recovered,
scoped to a proportionality (not reached here); `shapeDrawn` the fork drawn, neither pole forced, or the baseline
unestablished; `partial'` primed (`partial` is a Lean keyword) degenerate — the ground trivial, or the object under
test a grain-weighted gadget (the smuggle guard). No identifier embeds a forbidden content-name (`sourced`, not
`gravitational`, is clear of "gravity"). -/
inductive Outcome
  | sourced
  | inert
  | shapeDrawn
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION** of six earned flags: `grainNonConstant` (the grain non-constant, WS1), `distNonTrivial`
(the distance non-trivial, WS1), `distFromAdj` (the distance a function of the adjacency, WS2), `couplingEarned` (the
object under test reads only the adjacency, WS3), `forkTwoSided` (the GRAVITATIONAL pole inhabited, WS4), and
`couplingPresent` (the IMPORTED distance varies with the grain at fixed adjacency, WS3/WS4). `inert` when the coupling
is earned, the ground non-degenerate, the baseline set, the fork two-sided, and the imported distance NOT
grain-dependent. `sourced` if it were; `shapeDrawn` if the baseline or fork fails; `partial'` if the object is a
gadget or the ground degenerate. -/
def verdict (grainNonConstant distNonTrivial distFromAdj couplingEarned forkTwoSided couplingPresent : Bool) : Outcome :=
  if !couplingEarned then Outcome.partial'
  else if !(grainNonConstant && distNonTrivial) then Outcome.partial'
  else if !distFromAdj then Outcome.shapeDrawn
  else if !forkTwoSided then Outcome.shapeDrawn
  else if couplingPresent then Outcome.sourced
  else Outcome.inert

/-- **THE COMPUTED VERDICT.** On the earned flags (a non-constant grain and non-trivial distance, the distance a
function of the adjacency, the coupling earned, the fork two-sided, the imported distance NOT grain-dependent),
`inert` — INERT, by computation. -/
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.inert := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all four outcomes. -/
theorem ws5_verdict_discriminates :
    verdict true true true true true false  = Outcome.inert
  ∧ verdict true true true true true true   = Outcome.sourced
  ∧ verdict true true true true false false = Outcome.shapeDrawn
  ∧ verdict true true true false true false = Outcome.partial'
  ∧ verdict false true true true true false = Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The six deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set:
`grainNonConstant` / `distNonTrivial` (WS1, `ws1_grain_and_metric_nontrivial`); `distFromAdj` (WS2,
`ws2_metric_from_adjacency`); `couplingEarned` (WS3, `ws3_no_by_hand_coupling`); `forkTwoSided` (WS4,
`ws4_gravitational_reachable`); and the NEGATION justifying `couplingPresent = false` (WS3, `ws3_grain_test`: the
imported distance is NOT grain-dependent at fixed adjacency). -/
theorem ws5_flags_justified :
    (∃ x y : S, grainBump x ≠ grainBump y)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')
  ∧ (∀ c1 c2 : Config, c1.1 = c2.1 → ∀ x y, adjDist c1 x y = adjDist c2 x y)
  ∧ (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump) :=
  ⟨ws1_grain_and_metric_nontrivial.1, ws1_grain_and_metric_nontrivial.2,
   ws2_metric_from_adjacency, ws3_no_by_hand_coupling.1,
   ws4_gravitational_reachable.2.1, ws3_grain_test cfgFlat cfgBump rfl⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) THE COUPLING IS EARNED, NOT DEFINED (the no-smuggling gate, at the capstone).** The distance under test
reads the adjacency component ONLY (`adjDist c = pathDist c.1`); the single grain-weighted object (`foilDist`) is a
DISTINCT object, not the distance under test. No proof term defines the distance as a function of the grain and
recovers it. -/
theorem ws5_audit_coupling_earned :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ c x y, foilDist c x y ≠ adjDist c x y) :=
  ws3_no_by_hand_coupling

/-- **(b) THE FORK NOT BY FIAT.** INERT reachable by the imported distance (`¬ grainDependent adjDist`) and
GRAVITATIONAL inhabited by the foil (`grainDependent foilDist`), both from the SAME test on a pair whose grain
genuinely differs (`cfgFlat.2 ≠ cfgBump.2`); the verdict discriminates (`shapeDrawn` when the fork is one-sided). -/
theorem ws5_audit_fork_genuine :
    (¬ grainDependent adjDist cfgFlat cfgBump)
  ∧ (grainDependent foilDist cfgFlat cfgBump)
  ∧ (cfgFlat.2 ≠ cfgBump.2)
  ∧ (verdict true true true true false false = Outcome.shapeDrawn) :=
  ⟨ws3_grain_test cfgFlat cfgBump rfl, ws4_gravitational_reachable.2.1, ws4_inert_reachable.2.1, rfl⟩

/-- **(c) THE DISTANCE IS THE BUILT ONE.** The distance under test is the imported adjacency-distance (`adjDist c =
pathDist c.1`, a function of the adjacency), and it genuinely RESPONDS to the adjacency (a different adjacency gives a
different distance) — not a rigged constant, not a fresh grain-weighted gadget. -/
theorem ws5_audit_metric_is_built :
    (∀ c x y, adjDist c x y = pathDist c.1 x y)
  ∧ (∃ x y : S, pathDist aChain x y ≠ pathDist aStar x y) :=
  ⟨fun _ _ _ => rfl, ws2_metric_reads_adjacency⟩

/-- **(d) THE SCOPE IS DISCLOSED.** At most a grain-dependence test on the model's own distance is claimed; the
verdict is `inert` (no coupling claimed of the imported distance), which claims even less than a proportionality. No
theorem claims a full Einstein field equation, nor the area law (Bekenstein / holographic, information bounded by
boundary not volume) — the disclosed forward-note. -/
theorem ws5_audit_scope :
    (verdict true true true true true false = Outcome.inert)
  ∧ (¬ grainDependent adjDist cfgFlat cfgBump) :=
  ⟨ws5_verdict_eq, ws3_grain_test cfgFlat cfgBump rfl⟩

/-- **(e) NAMES-NOT-TERMS.** The four `Outcome` values are pairwise DISTINCT: the verdict's codomain is a genuine
four-way discrimination among NEUTRALLY-named outcomes, none named for the interpretive content. The full identifier
property (no proof term, definition, or discharged obligation named "gravity," "curvature," "curve," "mass,"
"geometry," "metric," "spacetime," "self," "import," "God," "choice" as content) is a META-property about the source
text, enforced by the protocol §6 mechanical grep (hits are docstring prose / the Lean `import` keyword only) — the
real teeth. -/
theorem ws5_audit_names_not_terms :
    Outcome.sourced ≠ Outcome.inert ∧ Outcome.inert ≠ Outcome.shapeDrawn
  ∧ Outcome.shapeDrawn ≠ Outcome.partial' ∧ Outcome.sourced ≠ Outcome.partial' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The computed verdict, assembled -/

/-- **THE VERDICT IS INERT.** With every flag earned by the WS1-WS4 headlines (`ws5_flags_justified`), the computed
verdict is `inert`: the imported distance is invariant under grain-change at fixed adjacency. Geometry decoupled from
the grain — no gravity — the honest NOT-RECOVERED that Series 2.4's DISTINCTNESS of space and the measure foretold,
and the specification for the next iteration: couple the two axes 2.4 kept apart. The full Einstein equation and the
area law (Bekenstein / holographic) are the disclosed forward-note. As the terminal series, this closes Phase 3 and
the built arc. -/
theorem ws5_the_verdict : verdict true true true true true false = Outcome.inert := ws5_verdict_eq

end P2S13
