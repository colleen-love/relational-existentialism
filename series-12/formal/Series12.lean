-- `Series12` - the live Lean root (Spec Series 12).
--
-- Series 03-06, 08-11 are closed and frozen under `archive/`; Series 07 is complete under `series-07/`.
-- Series 12 is WHOLLY STANDALONE (charter §1): the one prior result it presupposes and names is Series 07,
-- transcribed (not imported) into `series-12/formal/Series12/wsNN.lean` and re-namespaced `Series12.WSNN`.
-- Nothing is imported from `series-07/`, `archive/`, or any other series. The full build compiles
-- `sorry`-free with no custom axioms; every result rests only on Mathlib's standard three
-- (`propext` / `Classical.choice` / `Quot.sound`), recorded by `AxiomCheck.lean`.
--
-- HEADLINE. The shape of the undefinable, drawn exactly and left open. WS1 draws the OPENING (the shape
-- `¬ Recoverable`) and proves the COINCIDENCE (what Series 07 requires and what the diagonal generates share
-- the shape, forced-for-all vs exists-satisfying, never object-identity). WS2 inhabits it: `Many` on a
-- concrete four-state rank-labelled tower where a reified relatum carrying a reified constituent and a base
-- relatum are plain-bisimilar yet rank-separated, reification load-bearing, rank non-injective, generalized.
-- WS3 types the COMPASS (per-relatum, layered, exogenous) and holds it parametric, evaluating none. WS4
-- defines CONVERGENCE and proves it UNDERDETERMINED by a genuine non-degenerate model pair. WS5 computes the
-- verdict (branching on the certified fork) and proves the generalized neutrality. WS6 states the provable
-- core and the permanent opens as theorems. WS7 audits and the typed verdict is SHAPE-DRAWN.

-- WS1 - the opening (`Opening`) and the shape-coincidence (`ws1_shape_coincidence`, `ws1_coincidence_not_identity`).
import Series12.ws1
-- WS2 - knowing: finite attention and the inhabited opening (`Many`, `ws2_many_witness`, `ws2_many_general`).
import Series12.ws2
-- WS3 - feeling: the compass TYPE (`Compass`, `ws3_compass_exogenous`, `ws3_compass_layered`), parametric.
import Series12.ws3
-- WS4 - convergence defined (`Converges`) and underdetermined (`ws4_underdetermined`, `ws4_wall_is_structural`).
import Series12.ws4
-- WS5 - the verdict as a function of the fork (`ws5_verdict`) and the generalized neutrality (`ws5_name_neutral`).
import Series12.ws5
-- WS6 - the program's close: the provable core and the permanent opens as theorems.
import Series12.ws6
-- WS7 - the anti-circularity audit and the typed verdict (`ws7_verdict = shapeDrawn`).
import Series12.ws7
