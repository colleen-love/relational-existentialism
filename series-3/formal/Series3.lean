-- `Series3` — the live Lean root (Spec Series 3).
-- Series 2 is closed and archived under `archive/`; Series 3 opens on the new
-- foundation. The Series 3 charter (`series-3/charter.md`) grows it.
--
-- STATUS: WS1–WS8 are all formalized and the full build compiles, `sorry`-free.
-- Every workstream's headline deliverable rests only on Mathlib's standard three
-- axioms (`propext` / `Classical.choice` / `Quot.sound`) — no custom axioms — as
-- verified at build time by `AxiomCheck.lean` (a `#print axioms` sweep over one
-- top result per workstream; the `Łₙ` quantitative witness is even choice-free).
-- The dynamical half of criterion (vii) is discharged for exhibited dynamics: the
-- nonexpansive, linear, AND fitness-dependent **exponential** replicators all
-- converge on explicit μ-bands (`ws8_{,exp_}replicator_converges`), so the WS7
-- dynamical status is `partial_band`, not `deferred`. Partial/open obligations are
-- named as typed holes and never laundered into discharged-looking theorems (see
-- each `ws*.lean` header for its exact scope).
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
-- WS5 (`series-3/spec/ws5/04-charter-design-review.md`, rev. 3) — finite attention:
-- self-description incompleteness (Impossibility-proved, (F,κ)-robust), the
-- plurality/anti-collapse floor (Discharged), and convergence (Partial-conditional:
-- the Banach step proved, the contraction premise a typed open obligation).
import ws5
-- WS6 (`series-3/spec/ws6/04-charter-design-review.md`, rev. 2) — no poles, no
-- outside: the pole-coincidence split (Impossibility-proved, scoped), the no-maximal
-- wall discharged by κ-fiat, and criterion (vi) reported Open (vacuous) with a routed
-- obstruction — never laundered.
import ws6
-- WS7 (`series-3/spec/ws7/04-charter-design-review.md`, v3) — non-collapse, the
-- collector: the static band + retro-validation of the shared (F,κ,μ,#Q) tuple at one
-- concrete choice, the richness/plurality floors (with the (iv)-blocking general
-- branching held open), and the dynamical Banach step (convergence deferred to the
-- open Lemma B). Named ws7_band_and_retro, not ws7_resolved.
import ws7
-- WS8 (`series-3/spec/ws8/02-design.md`) — filling the holes A–E: weighted
-- weak-pullback preservation proved POSITIVELY (discharging WS4's open obligation;
-- the design's impossibility is false against the sup-based lifting), canonicity of
-- the weak law (∃!), general-branching refuted + the honest alg-relative floor, and
-- both faces of criterion (vi) (no global observer + positioned views). C deferred.
import ws8
