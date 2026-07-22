/-
`program-3/series-3/formal/P3S3/ws2.lean`

WS2 - The winding is word-dependent, and its orientation is a declared convention. Program 3 Series 3
(3.3), the phase.

Two co-terminal histories from one state with different windings: the one-move history that carries the
attention from `1` to `2` directly, and the two-move history that routes it through `0`. Both end at the
same state; their windings are `1` and `2`. The winding is not a function of the endpoints.

Scope, repaired at Program Review 3-1 (finding P3R1-S1). The winding is a function of the move word, not
of the trajectory through state space: the transport map is symmetric in its last two arguments
(`transport_swap`), so the words `(x, y, z)` and `(x, z, y)` denote one and the same map while carrying
opposite step signs (`stepSign_swap`), and `ws2_winding_orientation` records the obstruction — a pair of
words with identical runs from every state and windings `1` and `-1`. The phase therefore lives on
oriented moves: a word carries an orientation the map alone does not, exactly as a loop in ordinary
holonomy carries an orientation its image does not. The orientation is a declared convention of the word
alphabet, antisymmetric under reversal, and no theorem in this series derives it from the state; the
honest reading of every "path-dependent" claim below is word-dependent, with co-terminality still doing
real work (the routed histories are not presentation-variants of the direct one — their windings differ
by more than a sign).

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S3.ws1

namespace P3S3

open P3S0 P3S1 P3S2

set_option linter.unusedVariables false

/-- The direct history: one move, attention from `1` to `2`. -/
def hDirect : Hist := [(0, 1, 2)]

/-- The routed history: two moves, attention from `1` through `0` to `2`. -/
def hRouted : Hist := [(0, 1, 0), (0, 0, 2)]

/-- A longer routed history: three moves, out to `0`, back to `1`, then to `2`. Winding `3`. -/
def hLong : Hist := [(0, 1, 0), (0, 0, 1), (0, 1, 2)]

/-- The transport map is symmetric in its last two arguments: the words `(x, y, z)` and `(x, z, y)`
denote one and the same map on every state. (Program Review 3-1, P3R1-S1: the fact that forces the
word-level reading of the winding.) -/
theorem transport_swap (x y z : Fin 3) (g : G) : transport x z y g = transport x y z g := by
  funext w
  by_cases hw : w = x
  · subst hw
    rw [transport_row, transport_row]
    by_cases hA : y ∈ g w ∧ z ∉ g w
    · rw [if_neg (fun h => h.2 hA.1), if_pos hA, if_pos hA]
    · by_cases hB : z ∈ g w ∧ y ∉ g w
      · rw [if_pos hB, if_neg hA, if_pos hB]
      · rw [if_neg hB, if_neg hA, if_neg hA, if_neg hB]
  · rw [transport_other x z y w hw, transport_other x y z w hw]

/-- The two presentations of one map carry opposite step signs: the orientation is data of the word, not
of the map, antisymmetric under reversal — as a loop's orientation is data the loop's image does not
carry. -/
theorem stepSign_swap (x y z : Fin 3) (g : G) :
    stepSign (x, z, y) g = - stepSign (x, y, z) g := by
  show (if z ∈ g x ∧ y ∉ g x then (1 : ℤ) else if y ∈ g x ∧ z ∉ g x then -1 else 0)
      = -(if y ∈ g x ∧ z ∉ g x then (1 : ℤ) else if z ∈ g x ∧ y ∉ g x then -1 else 0)
  by_cases hA : y ∈ g x ∧ z ∉ g x
  · rw [if_neg (fun h => h.2 hA.1), if_pos hA, if_pos hA]
  · by_cases hB : z ∈ g x ∧ y ∉ g x
    · rw [if_pos hB, if_neg hA, if_pos hB]
      norm_num
    · rw [if_neg hB, if_neg hA, if_neg hA, if_neg hB]
      norm_num

/-- The flipped presentation of the direct move. -/
def hFlipped : Hist := [(0, 2, 1)]

/-- The obstruction, recorded (Program Review 3-1, P3R1-S1): the flipped word runs identically to the
direct word from every state, and their windings from the one-edge state are `-1` and `1`. The winding
does not descend to maps; the phase reads the oriented word. -/
theorem ws2_winding_orientation :
    (∀ g : G, run hFlipped g = run hDirect g)
  ∧ wind hFlipped gFwd = -1
  ∧ wind hDirect gFwd = 1 := by
  refine ⟨?_, by decide, by decide⟩
  intro g
  show stepOf (0, 2, 1) g = stepOf (0, 1, 2) g
  exact transport_swap 0 1 2 g

/-- The winding is word-dependent beyond orientation: the direct and routed histories are co-terminal
from the one-edge state, with windings `1` and `2` — a difference no presentation flip accounts for (a
flip negates; it cannot send `1` to `2`). The phase reads the oriented word, not the endpoints. -/
theorem ws2_winding_path_dependent :
    run hDirect gFwd = run hRouted gFwd
  ∧ wind hDirect gFwd = 1
  ∧ wind hRouted gFwd = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The long history is also co-terminal, with winding `3`: the windings realize both parities on
co-terminal histories, which WS4's interference needs. -/
theorem ws2_windings_both_parities :
    run hLong gFwd = run hDirect gFwd ∧ wind hLong gFwd = 3 := by
  refine ⟨by decide, by decide⟩

end P3S3
