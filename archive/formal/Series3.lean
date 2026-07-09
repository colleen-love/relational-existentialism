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
-- WS9 (`series-3/spec/ws9/`) — the convergence boundary, a full stratification of where
-- attention converges. WS8 gave sufficient contraction bands; WS9 adds: FALSE — unique
-- convergence is not universal (`ws9_no_unique_attention`/`ws9_no_contraction`: three
-- fixed points of `w_r²/∑w²` at `μ = 3/8`) and attention can fail to settle at all
-- (`ws9_two_cycle`: a contrarian selection's exact 2-cycle); TRUE — existence for every
-- `μ` (`ws9_center_fixed_all`) and multistability on `μ ∈ (0,3/8]` (`ws9_multistable_interval`);
-- BIFURCATION — the pitchfork `μ⋆ = 1/2` via the center's multiplier `2(1−μ)`
-- (`ws9_bifurcation`); CONDITIONAL — nonexpansive selection converges on all `μ`
-- (`ws9_nonexpansive_converges`). Named by parts, not `ws9_convergence_characterized`.
import ws9
-- WS10 (`series-3/spec/ws10/`) — statement–gloss reconciliation from the external
-- review. The keystone `carrier_card_ge` proves `κ ≤ #(νPk κ).X` (the `hcard` every
-- cardinality-touching "Discharged" silently assumed), so the concrete tuple at
-- `κ₀ = ℵ₀` is exhibited hypothesis-free (`ws10_concrete_tuple`), incompleteness gets
-- its κ-consuming half (`ws10_bounded_self_model`), standpoints are proper
-- (`ws10_standpoint_proper`), and — at ℵ₀ where supports are finite by the carrier's
-- own bound — attention converges on a carrier support (`ws10_carrier_attention_converges`).
import ws10
-- WS11 (`series-3/spec/ws11/02-design.md`) — the identity split: on any coalgebra,
-- strong extensionality forces downward determination (equality-of-unfoldings is a
-- bisimulation), so upward-load-bearing identity is impossible inside the strongly
-- extensional class (`ws11_no_upward_identity`) yet realized outside it by an explicit
-- three-state witness (`ws11_upward_witness`); the terminal map erases exactly the
-- upward distinctions (`ws11_terminal_identifies`). Named `ws11_identity_split`.
import ws11
-- WS12 (`series-3/spec/ws12/02-design.md`) — hereditary non-domination. Every reachable
-- set is `≤ κ` (`ws12_reachable_card_le`), and at `κ₀ = ℵ₀` the carrier is STRICTLY larger:
-- a `2^ℵ₀` spine-coalgebra family injects into it (`ws12_carrier_card_continuum`,
-- `ws12_carrier_card_gt`) — the R2 keystone lands. Hence no state hereditarily reaches
-- everything and no reachable set surjects onto the carrier (`ws12_hereditary_scope`).
import ws12
-- WS13 (`series-3/spec/ws13/02-design.md`) — pairs and relations as states. The
-- `lambek`-inverse state-former `mkState` gives Kuratowski pairing (`ws13_pair_inj`) and
-- faithful, usable reification of every `< κ` relation as a state (`ws13_reify_inj`,
-- `ws13_reify_mem`), iterable (`ws13_reification`). Exports `mkState` (consumed by WS15).
import ws13
-- WS14 (`series-3/spec/ws14/02-design.md`) — the graded carrier defeats the collapse.
-- Self-loop states exist at every weight (`loop_str_self`), distinct weights give distinct,
-- hereditarily-supported loops (`ws14_loop_ne`, `loop_hereditary`), so the weighted carrier
-- carries a plural hereditarily-supported subclass (`ws14_graded_core`) — opposite verdict
-- to WS10's plain-carrier collapse — plus the weighted cardinality bound (`ws14_wq_card_ge`).
-- The closure fork (G5), standpoints (G8), Lawvere witness (G9), and weak-law class (G6)
-- remain open remarks routed to later waves.
import ws14
-- WS15 (`series-3/spec/ws15/02-design.md`) — constitutive attention. The dynamics' output
-- re-enters the carrier as a state (`selfModel`, via WS13's `mkState`), proper exactly when
-- attention under-covers the support (`ws15_selfModel_eq_iff`, `ws15_selfModel_view_proper`);
-- and the coordination family's exact count via the cubic factorization
-- (`ws15_coord_cubic_factor`) pins the bifurcation threshold at precisely `1/2`
-- (`ws15_multistable_iff`); every orbit keeps its floor (`ws15_orbit_floor`).
-- The convergence half of the linear family (A4) and the settled self-model (A3) are
-- open remarks. Named `ws15_constitutive_attention`.
import ws15
