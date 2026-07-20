-- `P2S0` - the live Lean root (Program 2 Series 0, 2.0).
--
-- Series 0 is the Program 2 GROUND: relating is finite attending. Unlike a Program 1 series it IMPORTS the
-- P1 foundation (`program-2/formal/P1`, Program 2 permits it) and builds on it, rather than transcribing.
-- The full build compiles `sorry`-free with no custom axioms; every headline rests only on Mathlib's
-- standard three (`propext` / `Classical.choice` / `Quot.sound`), recorded by `AxiomCheck.lean`.
--
-- HEADLINE. The carrier is the ATTENTION CARRIER `attends : X → Finset X`, finite out-attention the sole
-- ontological bound (no cardinal ceiling). WS1 fixes the carrier and the reification section on the finite
-- functor (`ws1_reification_exists`, `ws1_bound_is_finite_attention`). WS2 restates the inherited collapse
-- over the symmetric relating (`ws2_collapse_inherited`), the imported P1 engine, baseline not result. WS3,
-- the knot, proves the asymmetry of knowing genuine: direction non-recoverable (`ws3_direction_not_recoverable`),
-- passive constitution real and load-bearing (`ws3_passive_constitution`), active and passive two
-- (`ws3_active_passive_distinct`). WS4 seats the import as an exogenous, quantified symmetry-breaker
-- (`ws4_import_breaks_baseline`, `ws4_import_quantified`), never named. WS5 computes the verdict from
-- WS1/WS3/WS4 (`ws5_verdict_eq`, GROUND-ESTABLISHED) and folds in the audit (a)-(e).

-- WS1 - the carrier and the finite-functor reification (`ws1_reification_exists`, `ws1_bound_is_finite_attention`).
import P2S0.ws1
-- WS2 - the inherited collapse (`ws2_collapse_inherited`), the imported engine applied to the symmetric relating.
import P2S0.ws2
-- WS3 - the asymmetry of knowing (the knot): direction non-recoverable, passive constitution load-bearing, two modes.
import P2S0.ws3
-- WS4 - the import seated, quantified, never named (`ws4_import_breaks_baseline`, `ws4_import_quantified`).
import P2S0.ws4
-- WS5 - the verdict computed from WS1/WS3/WS4 and the folded-in audit (`ws5_verdict_eq`, `ws5_audit_*`).
import P2S0.ws5
