/-
`program-2/series-1/formal/P2S1/AxiomCheck.lean`

Imports the whole Series 1 build and emits a `#print axioms` record for the headline theorem of every
workstream. The bar (protocol §6): sorry-free and no new axioms - every headline rests only on Mathlib's
standard three, `propext` / `Classical.choice` / `Quot.sound`, with no `sorryAx` and no custom `axiom`.
`ws5_verdict_eq` and `ws5_verdict_discriminates` depend on NO axioms.
-/
import P2S1

-- WS1 - the cycle reifies into the composite (a relatum of the field, finite composed attention)
#print axioms P2S1.ws1_cycle_reifies
#print axioms P2S1.ws1_composite_attention_finite

-- WS2 - subtractivity (free residue) and the arrow (reader load-bearing, tick irreversible)
#print axioms P2S1.ws2_composite_distinguishes
#print axioms P2S1.ws2_composite_residue
#print axioms P2S1.ws2_composite_real_for
#print axioms P2S1.ws2_tick_irreversible

-- WS3 - the stream exogenous and load-bearing
#print axioms P2S1.ws3_stream_exogenous
#print axioms P2S1.ws3_tick_needs_stream

-- WS4 - the clock knot: causal order endogenous, linearization import, the two-zone fork
#print axioms P2S1.ws4_causal_order_endogenous
#print axioms P2S1.ws4_linearization_import
#print axioms P2S1.ws4_two_zone

-- WS5 - the verdict computed from the flags, the flags earned, the audit (a)-(e) folded in
#print axioms P2S1.ws5_verdict_eq
#print axioms P2S1.ws5_verdict_discriminates
#print axioms P2S1.ws5_flags_justified
#print axioms P2S1.ws5_audit_no_smuggled_index
#print axioms P2S1.ws5_audit_stream_exogenous
#print axioms P2S1.ws5_audit_reader_loadbearing
#print axioms P2S1.ws5_audit_fork_genuine
#print axioms P2S1.ws5_audit_names_not_terms
