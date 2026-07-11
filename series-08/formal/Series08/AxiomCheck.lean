/-
`series-08/formal/Series08/AxiomCheck.lean`

The axiom pass over the whole Series 08 build. Each `#print axioms` confirms the headline reduces to
Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`) — no `sorry`, no custom
axiom. See `series-08/spec/axiom-check-log.md` for the committed record.
-/
import Series08

-- WS1 — the no-god's-eye spine (Impossibility proved) + the S1 fork (series-review-1)
#print axioms Series08.WS1.ws1_no_gods_eye
#print axioms Series08.WS1.ws1_no_gods_eye_node
#print axioms Series08.WS1.ws1_hold_forced
#print axioms Series08.WS1.ws1_symmetric_hold_recoverable
#print axioms Series08.WS1.ws1_directed_hold_free
#print axioms Series08.WS1.ws1_symmetric_bisim_trivial
#print axioms Series08.WS1.ws1_symmetric_states_bisimilar
#print axioms Series08.WS1.ws1_gods_eye_collapses
#print axioms Series08.WS1.ws1_symLoop_not_behav
#print axioms Series08.WS1.ws1_labelLoop_not_symmetric
#print axioms Series08.WS1.ws1_distinct_faces_atomless_not_recoverable
#print axioms Series08.WS1.ws1_freeness_needs_two_positions
#print axioms Series08.WS1.ws1_plural_faces_free_witness

-- WS2 — perspective breaks the collapse (plurality by free perspective)
#print axioms Series08.WS2.ws2_perspective_breaks_merge
#print axioms Series08.WS2.ws2_free_not_recoverable
#print axioms Series08.WS2.ws2_plurality_by_perspective
#print axioms Series08.WS2.ws2_monism_broken

-- WS3 — the re-restriction engine
#print axioms Series08.WS3.ws3_rerestriction_no_leaf
#print axioms Series08.WS3.ws3_rerestriction_not_function
#print axioms Series08.WS3.ws3_dynamics_forced
#print axioms Series08.WS3.ws3_prec_is_reach
#print axioms Series08.WS3.ws3_imported_index_refuted

-- WS4 — narrowing and depth
#print axioms Series08.WS4.ws4_step_narrows
#print axioms Series08.WS4.ws4_depth_is_narrowing
#print axioms Series08.WS4.ws4_reaches_is_trace
#print axioms Series08.WS4.ws4_depth_forecloses_witness

-- WS5 — the conservation fork (Refuted-universal / Partial)
#print axioms Series08.WS5.ws5_strict_refuted
#print axioms Series08.WS5.ws5_kill_condition
#print axioms Series08.WS5.ws5_conserves_if_nonincreasing
#print axioms Series08.WS5.ws5_verdict_justified

-- WS6 — the heuristic ceiling / retraction
#print axioms Series08.WS6.ws6_provable_core
#print axioms Series08.WS6.ws6_conservation_retracted

-- WS7 — the audit and the typed verdict
#print axioms Series08.WS7.ws7_audit
#print axioms Series08.WS7.ws7_verdict
#print axioms Series08.WS7.ws7_verdict_eq
#print axioms Series08.WS7.ws7_no_conservation_by_fiat
#print axioms Series08.WS7.ws7_freeness_not_defined_in
#print axioms Series08.WS7.ws7_strip_ledger
