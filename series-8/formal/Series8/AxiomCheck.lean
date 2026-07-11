/-
`series-8/formal/Series8/AxiomCheck.lean`

The axiom pass over the whole Series 8 build. Each `#print axioms` confirms the headline reduces to
Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`) — no `sorry`, no custom
axiom. See `series-8/spec/axiom-check-log.md` for the committed record.
-/
import Series8

-- WS1 — the no-god's-eye spine (Impossibility proved)
#print axioms Series8.WS1.ws1_no_gods_eye
#print axioms Series8.WS1.ws1_no_gods_eye_node
#print axioms Series8.WS1.ws1_hold_forced
#print axioms Series8.WS1.ws1_symmetric_hold_recoverable
#print axioms Series8.WS1.ws1_directed_hold_free

-- WS2 — perspective breaks the collapse (plurality by free perspective)
#print axioms Series8.WS2.ws2_perspective_breaks_merge
#print axioms Series8.WS2.ws2_free_not_recoverable
#print axioms Series8.WS2.ws2_plurality_by_perspective
#print axioms Series8.WS2.ws2_monism_broken

-- WS3 — the re-restriction engine
#print axioms Series8.WS3.ws3_rerestriction_no_leaf
#print axioms Series8.WS3.ws3_rerestriction_not_function
#print axioms Series8.WS3.ws3_dynamics_forced
#print axioms Series8.WS3.ws3_prec_is_reach
#print axioms Series8.WS3.ws3_imported_index_refuted

-- WS4 — narrowing and depth
#print axioms Series8.WS4.ws4_step_narrows
#print axioms Series8.WS4.ws4_depth_is_narrowing
#print axioms Series8.WS4.ws4_reaches_is_trace
#print axioms Series8.WS4.ws4_depth_forecloses_witness

-- WS5 — the conservation fork (Refuted-universal / Partial)
#print axioms Series8.WS5.ws5_strict_refuted
#print axioms Series8.WS5.ws5_kill_condition
#print axioms Series8.WS5.ws5_conserves_if_nonincreasing
#print axioms Series8.WS5.ws5_verdict_justified

-- WS6 — the heuristic ceiling / retraction
#print axioms Series8.WS6.ws6_provable_core
#print axioms Series8.WS6.ws6_conservation_retracted

-- WS7 — the audit and the typed verdict
#print axioms Series8.WS7.ws7_audit
#print axioms Series8.WS7.ws7_verdict
#print axioms Series8.WS7.ws7_verdict_eq
#print axioms Series8.WS7.ws7_no_conservation_by_fiat
#print axioms Series8.WS7.ws7_freeness_not_defined_in
#print axioms Series8.WS7.ws7_strip_ledger
