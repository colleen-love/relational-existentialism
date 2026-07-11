-- `Series4` — the live Lean root (Spec Series 4).
-- Series 3 is closed and archived under `archive/`; Series 4 opens on a fresh
-- foundation: quality as restriction (each thing turns only part of itself toward
-- another). The Series 4 charter (`series-4/charter.md`) and its per-workstream
-- design docs (`series-4/spec/wsNN-design.md`) grow it.
--
-- STATUS: WS1–WS7 are all formalized and the full build compiles, `sorry`-free and
-- with no custom axioms — every result rests only on Mathlib's standard three
-- (`propext` / `Classical.choice` / `Quot.sound`), as recorded by
-- `AxiomCheck.lean`. Series 4 is COMPLETELY self-contained: the groundless carrier
-- and every reused lemma are reproduced here from the Series 3 archive; nothing is
-- imported from `archive/`. Partial/conditional obligations are stated as explicit
-- hypotheses or typed structures (never `sorry`), exactly as the charter §7 outcome
-- vocabulary and §9 hedges pre-register.
--
-- WS1 (`series-4/spec/ws01-design.md`) — the world and its faces: the terminal
-- coalgebra of the κ-bounded powerset functor (via QPF/`Cofix`), the derived
-- intrinsic `face`, the inherited weak-pullback gate, and Ω with its improper
-- self-face.
import Series4.ws1
-- WS2 (`ws02-design.md`) — the collapse (atomless ∧ plural unsatisfiable on `νP_κ`),
-- the imported-weight leak over a minimal quality algebra, and the forced-answer
-- dichotomy.
import Series4.ws2
-- WS3 (`ws03-design.md`) — plurality without atoms: a self-contained labelled carrier
-- `νLk` on which loops are distinguished by face, with composition unconditionally
-- atom-free.
import Series4.ws3
-- WS4 (`ws04-design.md`) — no top, no view from nowhere: the endogenous no-top wall
-- (each object's own `< κ` relating outgrown by the world), positioned views, and
-- substantive standpoints.
import Series4.ws4
-- WS5 (`ws05-design.md`) — the self-bounding of the world: the M1/M2 negatives, the
-- global-groundlessness Impossibility, and the endogenous bound on the loop-spine.
import Series4.ws5
-- WS6 (`ws06-design.md`) — the two incompletenesses: the proper self-face and its
-- Lawvere diagonal (off the diagonal), and Ω's complete-yet-unclosed self-model (on
-- it), with attention as face-thickening.
import Series4.ws6
-- WS7 (`ws07-design.md`) — the anti-trivialization audit: the finitude of facing, the
-- one-finitude reduction, the distinctness anchor, and the typed program verdict.
import Series4.ws7
