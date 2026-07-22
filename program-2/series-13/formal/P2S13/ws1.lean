/-
`program-2/series-13/formal/P2S13/ws1.lean`

WS1 - The grain and the distance (the ground). Program 2 Series 13 (2.13), THE CURVE.

Imports its predecessor `P2S9` (reaching `P2S8 / P2S7 / … / P2S4 / … / P2S0 / P1` transitively) and builds on its
transitive API: chiefly Series 2.4's directed distance (`stepsFrom`, the shortest directed attention-path length, a
function of the adjacency alone) and Series 2.7's measure of distinction (`rankM`, the reification rank, the grain).
This file fixes the SHARED objects of the series, re-seated FRESH and faithful to the imported constructions on the
witness carrier `S := Fin 4` (the Series 2.9 precedent: `P2S9` re-seats the Series 2.4 world/metric as `Fin 5` with a
fresh `dist`), de-risked on paper first (`spec/grain-derisking.md`):

- the carrier `S` (four relata), the adjacency `Adj` (directed reachability), the grain `Grain` (a measure over the
  relata, Series 2.7's `rankM` re-seated), and a configuration `Config := Adj × Grain`;
- the directed path-length `pathDist` (Series 2.4's `stepsFrom` re-seated as a decidable fuel-computation): the least
  step-count reaching `y` from `x` in the adjacency, a function of the ADJACENCY ALONE (it takes no grain argument);
- the concrete carriers: one adjacency `aChain` (the forward chain) and, on it, two grains `grainFlat` / `grainBump`
  differing only at `p3` — the same adjacency, different grain (the grain-derisking experiment).

WS1 proves the setup NON-TRIVIAL (`ws1_grain_and_metric_nontrivial`): the grain is non-constant (a source that
varies) and the distance takes at least two distinct values (a geometry it could bend), so the grain-dependence test
is non-degenerate.

Design docs: `program-2/series-13/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S9

namespace P2S13

set_option linter.unusedVariables false

/-! ## The carrier, the adjacency, the grain (Series 2.4's world / Series 2.7's measure, re-seated) -/

/-- The witness carrier: four relata (Series 2.4's world re-seated, cf. `P2S9`'s `Fin 5`). -/
abbrev S : Type := Fin 4

def p0 : S := 0   -- the source relatum (basepoint)
def p1 : S := 1   -- a relatum one step out
def p2 : S := 2   -- a relatum two steps out
def p3 : S := 3   -- the far relatum (where the grain is packed)

/-- The ADJACENCY: the directed reachability structure over the relata — exactly the input the distance reads. -/
abbrev Adj : Type := S → Finset S

/-- The GRAIN: the measure of distinction over the relata (Series 2.7's reification rank `rankM`, re-seated). -/
abbrev Grain : Type := S → ℕ

/-- A CONFIGURATION: an adjacency and a grain on the same relata. -/
abbrev Config : Type := Adj × Grain

/-! ## The distance (Series 2.4's directed path-length, re-seated as a decidable fuel-computation) -/

/-- The nodes reachable from `x` within `n` steps of the adjacency `a`. -/
def stepBall (a : Adj) : ℕ → S → Finset S
  | 0,     x => {x}
  | (n+1), x => insert x ((a x).biUnion (fun y => stepBall a n y))

/-- **THE DISTANCE** (Series 2.4's directed self-relative distance `stepsFrom`, re-seated): the least step-count
reaching `y` from `x` in the adjacency, with sentinel `4` when `y` is unreachable within `3` steps (the carrier's
diameter bound). It is a function of the ADJACENCY `a` ALONE — it takes no grain argument, so it has no channel
through which the grain could enter. Named `pathDist` in code ("metric" is a forbidden content-name for a term,
audit e); "the metric" / "the geometry" in prose. -/
def pathDist (a : Adj) (x y : S) : ℕ :=
  if y ∈ stepBall a 0 x then 0
  else if y ∈ stepBall a 1 x then 1
  else if y ∈ stepBall a 2 x then 2
  else if y ∈ stepBall a 3 x then 3
  else 4

/-! ## The concrete carriers (the grain-derisking experiment: same adjacency, different grain) -/

/-- The forward chain `p0 → p1 → p2 → p3` (the witnessing adjacency). -/
def aChain : Adj := fun x => if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else ∅

/-- The star from `p0` (a SECOND adjacency, to witness that the distance responds to the adjacency). -/
def aStar : Adj := fun x => if x = 0 then {1, 2, 3} else ∅

/-- The flat grain: every relatum carries no distinction. -/
def grainFlat : Grain := fun _ => 0

/-- The bumped grain: the far relatum `p3` carries one unit of distinction (non-constant, and ≠ `grainFlat`). -/
def grainBump : Grain := fun x => if x = p3 then 1 else 0

/-- The flat configuration: the chain adjacency with the flat grain. -/
def cfgFlat : Config := (aChain, grainFlat)

/-- The bumped configuration: the SAME chain adjacency, the bumped grain (differs from `cfgFlat` only in the grain). -/
def cfgBump : Config := (aChain, grainBump)

/-! ## The payoff — the setup is non-trivial -/

/-- **THE SETUP IS NON-TRIVIAL (WS1).** The grain is non-constant (`grainBump p3 = 1 ≠ 0 = grainBump p0` — a source
that varies), and the distance takes at least two distinct values (`pathDist aChain p0 p1 = 1 ≠ 3 =
pathDist aChain p0 p3` — a geometry it could bend). Both are the model's own (Series 2.7's grain, Series 2.4's
distance, re-seated). So the grain-dependence test is non-degenerate. -/
theorem ws1_grain_and_metric_nontrivial :
    (∃ x y : S, grainBump x ≠ grainBump y)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y') :=
  ⟨⟨p3, p0, by decide⟩, ⟨p0, p1, p0, p3, by decide⟩⟩

end P2S13
