/-
`program-3/series-4/formal/P3S4/ws1.lean`

WS1 - The dynamical metric, and the static question kept honest. Program 3 Series 4 (3.4), the curve.

Imports `P3S3` at the series boundary. The metric is the shortest directed attention-path length in the
state, with the sentinel `3` for unreachable pairs — a fresh definition at this carrier (Series 2.13's
`pathDist` lives on four relata and cannot be imported; the shape is restated and named fresh, per the
bridge discipline).

- `ws1_dist_self`: distance zero to oneself, in every state;
- `ws1_metric_reads_state`: two states with different distances;
- `ws1_grain_underdetermines`: two states with identical charges everywhere and different distances — the
  static grain does not determine the metric. Series 2.13's INERT, recovered as the reason the coupling
  law must be dynamical.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3

namespace P3S4

open P3S0 P3S1 P3S2 P3S3

set_option linter.unusedVariables false

/-- The nodes reachable within `n` steps of the state's attention. -/
def ball (g : G) : ℕ → Fin 3 → Finset (Fin 3)
  | 0, x => {x}
  | (n + 1), x => insert x ((g x).biUnion (fun y => ball g n y))

/-- The dynamical metric: shortest directed attention-path length in the state, sentinel `3` when
unreachable. Named fresh at this carrier; the fresh naming and its reason are in the outline. -/
def flowDist (g : G) (x y : Fin 3) : ℕ :=
  if y ∈ ball g 0 x then 0
  else if y ∈ ball g 1 x then 1
  else if y ∈ ball g 2 x then 2
  else 3

/-- Distance zero to oneself, in every state. -/
theorem ws1_dist_self (g : G) (x : Fin 3) : flowDist g x x = 0 := by
  have hx : x ∈ ball g 0 x := Finset.mem_singleton_self x
  simp [flowDist, hx]

/-- The metric responds to the state: with the edge present the neighbour is at distance one; with the
state empty it sits at the sentinel. -/
theorem ws1_metric_reads_state :
    flowDist gFwd 0 1 = 1 ∧ flowDist (fun _ => ∅) 0 1 = 3 := by
  constructor <;> decide

/-- The mutual pair on `0, 1`. -/
def gM01 : G := fun w => if w = 0 then {1} else if w = 1 then {0} else ∅

/-- The mutual pair on `0, 2`. -/
def gM02 : G := fun w => if w = 0 then {2} else if w = 2 then {0} else ∅

/-- The static grain does not determine the metric: the two mutual-pair states carry identical charges
everywhere (all zero) and different distances. Series 2.13 asked the static question and got INERT; this
is that fact inside the flow world, and the reason the coupling law must be a law of change. -/
theorem ws1_grain_underdetermines :
    (∀ w, charge gM01 w = charge gM02 w)
  ∧ flowDist gM01 0 1 ≠ flowDist gM02 0 1 := by
  constructor <;> decide

end P3S4
