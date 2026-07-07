-- `Series3` — the live Lean root (Spec Series 3).
-- Series 2 is closed and archived under `archive/`; Series 3 opens on the new
-- foundation. The Series 3 charter (`series-3/charter.md`) grows it.
--
-- WS1 (`series-3/spec/ws1/4-charter-design-review.md`) — the Groundless Carrier:
-- the terminal coalgebra of the κ-bounded powerset functor, its Lambek iso,
-- bisimulation = identity, the canonical `Ω = {Ω}`, and the C2 solution lemma.
import ws1
-- WS2 (`series-3/spec/ws2/04-charter-design-review.md`) — `νP_κ` and its
-- bisimulation theory: the final coalgebra, non-degeneracy, bisim = identity,
-- weak-pullback preservation (Lemma 3.1a), behavioural equivalence, coinduction.
import ws2
-- WS3 (`series-3/spec/ws3/04-charter-design-review.md`) — bidirectional
-- constitution (Commitment 4 / criterion (iv)): no strict distributive law exists
-- (Klin–Salamanca, Part A), and the Egli–Milner weak bialgebra that delivers the
-- content (Part B).
import ws3
-- WS4 (`series-3/spec/ws4/04-charter-design-review.md`, v3) — graded parthood over
-- a good quantale: the Q-weighted functor `W_Q` as a QPF, its terminal coalgebra,
-- Lambek/bisim, and the graded weak law's multiplication coherence, instantiated at
-- the concrete non-idempotent Łukasiewicz witness `Łₙ` (with `tensor_section` proved
-- and consumed via `weight_split`). PARTIAL: Layer C weak-pullback preservation
-- (step 6) is registered as a typed open obligation `WQPreservesWeakPullback`, not
-- proved — the top bundle is `ws4_graded_coherence_Luk`, not `ws4_resolved`.
import ws4
