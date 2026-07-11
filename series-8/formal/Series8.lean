/-
`series-8/formal/Series8.lean`

Series 8 — **Finite perspective breaks the One.** The aggregator root.

Part Two of the program: Series 7 proved the determined, groundless, atomless plain world is the
One; Series 8 finds the fourth thing the collapse did not consider — the finitude of holding — and
shows the One becomes many, moving, and layered through re-restriction.

The spine (WS1) is a proved Impossibility: no relationally-identified god's-eye node exists. The
god's-eye node is the POSITIONLESS node — one holding all faces symmetrically, with no asymmetry
anywhere (`dest x = dest y` for all `x, y`) — and it is label-bisimilar to the trivial self-loop, so
it collapses to the One by the engine (behavioral identity), annihilating the faces it was meant to
hold: `ws1_gods_eye_collapses` (no `Recoverable`/atomless hypothesis). The surviving plural node is
provably NOT symmetric (`ws1_labelLoop_not_symmetric`), so it is genuinely distributed perspective
(WS2), never a symmetric totality that escaped collapse. From the spine three consequences: plurality
by free perspective (WS2), forced
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
