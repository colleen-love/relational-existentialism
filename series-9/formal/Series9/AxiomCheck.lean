/-
`series-9/formal/Series9/AxiomCheck.lean`

The axiom pass over the whole Series 9 build. Each `#print axioms` confirms the headline reduces to
Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`) — no `sorry`, no custom axiom.

The single most important record (protocol §C): `#print axioms Series9.WS1.ws1_no_self_total_hold`
reduces to the standard three, and its proof term (see `series-9/spec/axiom-check-log.md`) is a diagonal
fixed-point contradiction — it contains NO `IsBisim` / `BehaviorallyIdentified` /
`ws1_symmetric_states_bisimilar`, so the spine is INDEPENDENT of relational identity (not Coincident).
-/
import Series9

-- WS1 — the hold-reflexive carrier and the diagonal spine (the repair of Series 8)
#print axioms Series9.WS1.ws1_no_self_total_hold
#print axioms Series9.WS1.ws1_insp_not_surjective
#print axioms Series9.WS1.ws1_diagonal_not_bisim
#print axioms Series9.WS1.ws1_unrestricted_carrier_inconsistent
#print axioms Series9.WS1.ws1_holdreflexive_not_selfloop
#print axioms Series9.WS1.ws1_hold_forced
#print axioms Series9.WS1.ws1_symmetric_states_bisimilar

-- WS2 — the residue breaks the collapse from one position
#print axioms Series9.WS2.ws2_residue_distinct
#print axioms Series9.WS2.ws2_residue_free
#print axioms Series9.WS2.ws2_residue_is_import
#print axioms Series9.WS2.ws2_from_one_position
#print axioms Series9.WS2.ws2_distributed_special_case

-- WS3 — the re-diagonalization engine
#print axioms Series9.WS3.ws3_redi_no_leaf
#print axioms Series9.WS3.ws3_redi_not_function
#print axioms Series9.WS3.ws3_dynamics_forced
#print axioms Series9.WS3.ws3_order_endogenous
#print axioms Series9.WS3.ws3_imported_index_refuted

-- WS4 — the tower and depth
#print axioms Series9.WS4.ws4_new_blind_spot
#print axioms Series9.WS4.ws4_depth_is_tower
#print axioms Series9.WS4.ws4_reaches_is_trace
#print axioms Series9.WS4.ws4_depth_grows_witness

-- WS5 — the monotonicity fork (Refuted-universal / Partial)
#print axioms Series9.WS5.ws5_retention_refuted
#print axioms Series9.WS5.ws5_kill_condition
#print axioms Series9.WS5.ws5_monotone_on_fresh
#print axioms Series9.WS5.ws5_verdict_justified

-- WS6 — the heuristic ceiling / retraction
#print axioms Series9.WS6.ws6_provable_core
#print axioms Series9.WS6.ws6_monotonicity_retracted

-- WS7 — the audit, the coincidence check, and the typed verdict
#print axioms Series9.WS7.ws7_audit
#print axioms Series9.WS7.ws7_verdict
#print axioms Series9.WS7.ws7_verdict_eq
#print axioms Series9.WS7.ws7_coincidence_check
#print axioms Series9.WS7.ws7_no_coincidence
#print axioms Series9.WS7.ws7_no_monotonicity_by_fiat
#print axioms Series9.WS7.ws7_freeness_not_defined_in
#print axioms Series9.WS7.ws7_carrier_genuine
#print axioms Series9.WS7.ws7_strip_ledger
