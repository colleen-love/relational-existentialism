-- `Series5` — the live Lean root (Spec Series 5).
-- Series 3 is closed and frozen under `archive/`; Series 4 is complete under
-- `series-4/`. Series 5 opens the stratification program: a doubly-unbounded
-- tower of faced carriers `W_α` whose colimit `W_∞` is boundless above (no
-- last level, no imposed cardinal) and groundless below (no first level, no
-- atom-floor), with graded cross-level faces. The Series 5 charter
-- (`series-5/charter.md`) and its per-workstream design docs
-- (`series-5/spec/wsNN-design.md`) grow it.
--
-- STATUS: WS1–WS7 are all formalized and the full build compiles, `sorry`-free and
-- with no custom axioms — every result rests only on Mathlib's standard three
-- (`propext` / `Classical.choice` / `Quot.sound`), as recorded by `AxiomCheck.lean`.
-- Series 5 is WHOLLY STANDALONE (charter §1, `series-5/spec/readme.md`): every Series 4
-- (and, in WS6, Series 3) lemma it reuses is transcribed into `series-5/formal/wsNN.lean`
-- and re-namespaced `Series5.WSNN` — nothing is imported from `series-4/` or `archive/`.
-- Toolchain pinned as Series 4: Lean 4 `v4.15.0` / Mathlib `v4.15.0`.
--
-- Two design fixes discovered in the build and recorded in `charter-status.md` (WS1):
-- (i) the colimit structure map `destInf` is realized as the representative-independent
--     successor *set* `succSet` (the design's `Σ' a, LkObj κ_α Q (Winf T)` codomain is not
--     `Quot.lift`-definable), with the local `< κ_α` bound recovered as `ws1_local_bound`;
-- (ii) the connecting-map law `ι_dest` carries an explicit bound-relaxation `LkRelax`
--     (`LkObj κ_α` and `LkObj κ_β` are distinct types). Neither weakens a target.

-- WS1 (`ws01-design.md`) — the tower and its colimit: `Level`, `Tower`, the colimit
-- `Winf`, the gate `ws1_bisim_eq_colim`, Ω recovered with a local bound.
import ws1
-- WS2 (`ws02-design.md`) — the Explosion Dilemma, the `ℤ` index (no least / no greatest /
-- self-dual), and the forced answer.
import ws2
-- WS3 (`ws03-design.md`) — boundlessness without a wall: no object relates to everything,
-- powered by no-last-level (the escaping object lives at a higher level).
import ws3
-- WS4 (`ws04-design.md`) — no first / no last: groundless without collapse, the poles
-- (self-dual or lopsided), and no-view (V2 laundering vs V3 earned).
import ws4
-- WS5 (`ws05-design.md`) — the self-bounding revisited: grain-not-wall tower-wide, against
-- the standing M1/M2/M3 negatives, with the residual-fiat report.
import ws5
-- WS6 (`ws06-design.md`) — relating across levels: leak-free transport, descent, the
-- incompletenesses, no strict distributive law, the graded weak law, attention.
import ws6
-- WS7 (`ws07-design.md`) — the anti-trivialization audit and the typed program verdict.
import ws7
