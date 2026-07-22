# WS1 design — the grain and the distance (the ground) (2.13)

**IDENTIFY the two objects gravity would relate and prove the setup non-trivial: the GRAIN (Series 2.7's measure of distinction, the candidate source) is non-constant, and the DISTANCE (Series 2.4's directed path-length, the candidate curved geometry) is non-trivial. A source that varies and a geometry it could bend, so the grain-dependence test is non-degenerate. Both are the model's own, re-seated faithfully.**

## The shared objects (fixed here, used by all workstreams)

```lean
namespace P2S13
open P2S9

abbrev S : Type := Fin 4                 -- the witness carrier (Series 2.4's world re-seated, cf. P2S9's Fin 5)
def p0 : S := 0
def p1 : S := 1
def p2 : S := 2
def p3 : S := 3

abbrev Adj    : Type := S → Finset S      -- the adjacency (directed reachability)
abbrev Grain  : Type := S → ℕ             -- the measure of distinction over the relata
abbrev Config : Type := Adj × Grain

-- nodes reachable from x within n steps of the adjacency a.
def stepBall (a : Adj) : ℕ → S → Finset S
  | 0,     x => {x}
  | (n+1), x => insert x ((a x).biUnion (fun y => stepBall a n y))

-- THE DISTANCE (Series 2.4's directed path-length `stepsFrom`, re-seated as a decidable fuel-computation):
-- least step-count reaching y from x, sentinel 4 if unreachable. A function of the adjacency ALONE.
def pathDist (a : Adj) (x y : S) : ℕ :=
  if y ∈ stepBall a 0 x then 0
  else if y ∈ stepBall a 1 x then 1
  else if y ∈ stepBall a 2 x then 2
  else if y ∈ stepBall a 3 x then 3
  else 4

-- the concrete carriers (§ grain-derisking): one adjacency, two grains.
def aChain : Adj := fun x => if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else ∅
def aStar  : Adj := fun x => if x = 0 then {1,2,3} else ∅
def grainFlat : Grain := fun _ => 0
def grainBump : Grain := fun x => if x = p3 then 1 else 0
def cfgFlat : Config := (aChain, grainFlat)
def cfgBump : Config := (aChain, grainBump)
```

## Signatures

```lean
-- THE SETUP IS NON-TRIVIAL (WS1). The grain is non-constant (a source that varies), and the distance is
-- non-trivial (it takes at least two distinct values — a geometry it could bend). Both the model's own.
theorem ws1_grain_and_metric_nontrivial :
    (∃ x y : S, grainBump x ≠ grainBump y)
  ∧ (∃ x y x' y' : S, pathDist aChain x y ≠ pathDist aChain x' y')
```

## Proof

`by decide` (or `⟨⟨p3, p0, by decide⟩, ⟨p0, p1, p0, p3, by decide⟩⟩`): `grainBump p3 = 1 ≠ 0 = grainBump p0`; `pathDist aChain p0 p1 = 1 ≠ 3 = pathDist aChain p0 p3`. Verified in the prototype.

## Strip test

Delete "grain," "source," "distance," "geometry," "gravity": the statement is a bare `(a function `S → ℕ` is non-constant) ∧ (a function `S → S → ℕ` takes two distinct values)`. Survives — a non-degeneracy fact, no content smuggled by the words.

## Costume watch

The grain `grainBump` is genuinely non-constant (Series 2.7's `ws1_rank_nontrivial` re-seated), not a labelled constant; the distance `pathDist` is the genuine directed graph-distance (Series 2.4's `stepsFrom`), not a placeholder. Both are needed for the test to have teeth: a constant grain or a trivial distance would make the grain-dependence test vacuous.
