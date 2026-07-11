/-
`series-8/formal/Series8.lean`

Series 8 — **Finite perspective breaks the One.** The aggregator root.

Part Two of the program: Series 7 proved the determined, groundless, atomless plain world is the
One; Series 8 finds the fourth thing the collapse did not consider — the finitude of holding — and
shows the One becomes many, moving, and layered through re-restriction.

The spine (WS1) is honestly a **Partial** (series-review-3; the charter §5.5/§9 pre-registered this as
the sharpest risk). What is PROVED: a recoverable/symmetric god's-eye node collapses to the One
(`ws1_no_gods_eye`), and a genuine plurality of faces on an atomless field is necessarily FREE, never a
recoverable totality (`ws1_distinct_faces_atomless_not_recoverable`) — so there is no rich symmetric
totality to host plurality. What is NOT reached at charter strength: an *independent* collapse. The
positionless collapse `ws1_gods_eye_collapses` provably coincides with relational identity
(`ws1_symmetric_states_bisimilar`: a positionless node's states are all bisimilar, so the collapse is
behavioral identity, not a separate fact — the coincidence rule fails). This does not hand victory to
monism: the plurality is real and distributed (WS2, `ws1_freeness_needs_two_positions`). From the
spine (in its honest scope) three consequences: plurality by free perspective (WS2), forced
dynamics (WS3), depth-as-narrowing (WS4). The central open law — conservation of breadth — is TESTED,
not assumed: the kill condition fires (`ws5_kill_condition`), so strict conservation is Refuted and
the bound is mere boundedness (WS5/WS6). The verdict is `perspectiveEstablished` (WS7).

This file is SELF-CONTAINED: every Series 7/4 lemma is transcribed into `Series8/wsNN.lean` and
re-namespaced `Series8.WSn` — nothing is imported from `series-7/`, `series-4/`, or `archive/`.
`Series8.AxiomCheck` runs `#print axioms` over every headline. Sorry-free; axiom-clean beyond
Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series8.ws1
import Series8.ws2
import Series8.ws3
import Series8.ws4
import Series8.ws5
import Series8.ws6
import Series8.ws7
