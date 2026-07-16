/-
`series-13/formal/Series13/AxiomCheck.lean`

Imports the whole Series 13 build and emits a `#print axioms` record for the headline theorem of every
workstream. The bar (charter §7): sorry-free and no new axioms. A clean pass shows every headline rests only
on Mathlib's standard three, `propext` / `Classical.choice` / `Quot.sound`, with no `sorryAx` and no custom
`axiom`. (`Classical.choice` enters via `Classical.propDecidable` for `residue`'s `not_not` and the verdict's
carrier case-split, and via `toPk` / `Cardinal` machinery, Mathlib-base axioms, not new ones.)
-/
import Series13

-- WS1 - the two orders, each non-trivial (the knot), plus the transcribed premises (Series 07, Series 12 WS1)
#print axioms Series13.WS1.ws1_orders_insp_nontrivial
#print axioms Series13.WS1.ws1_orders_lab_nontrivial
#print axioms Series13.WS1.ws2_import_theorem
#print axioms Series13.WS1.ws3_atomless_distinct_is_import
#print axioms Series13.WS1.ws1_atomless_bisim
#print axioms Series13.WS1.ws2_residue_free
#print axioms Series13.WS1.ws2_residue_distinct
#print axioms Series13.WS1.ws1_no_self_total_hold
#print axioms Series13.WS1.ws1_shape_coincidence
#print axioms Series13.WS1.ws1_coincidence_not_identity_witness

-- WS2 - the mint, the transport (via the diagonal) and the exogeneity (the mint above the plain layer)
#print axioms Series13.WS2.ws2_mint_lands_in_opening
#print axioms Series13.WS2.ws2_transport_forall
#print axioms Series13.WS2.ws2_mint_exogenous
#print axioms Series13.WS2.ws2_mint_not_plain_function
#print axioms Series13.WS2.ws2_mint_nontrivial

-- WS3 - the adjoint, the Galois connection, closure/interior, the non-identity round trip (the fit)
#print axioms Series13.WS3.ws3_galois
#print axioms Series13.WS3.ws3_mint_monotone
#print axioms Series13.WS3.ws3_read_monotone
#print axioms Series13.WS3.ws3_roundtrip_closure
#print axioms Series13.WS3.ws3_roundtrip_interior
#print axioms Series13.WS3.ws3_roundtrip_not_identity

-- WS4 - mintability up to `≈`: the defect (DUAL), its structural exclusion, and the flat-layer TOTAL
#print axioms Series13.WS4.ws4_mint_not_surjective
#print axioms Series13.WS4.ws4_exclusion_structural
#print axioms Series13.WS4.ws4_mint_essentially_surjective_degenerate

-- WS5 - the verdict as a function of WS1-WS4 (computed), the falsifiability, and the folded-in audit
#print axioms Series13.WS5.ws5_verdict_eq
#print axioms Series13.WS5.ws5_verdict_degenerate
#print axioms Series13.WS5.ws5_verdict_not_total
#print axioms Series13.WS5.ws5_verdict_not_disconnected
#print axioms Series13.WS5.ws5_verdict_not_partial
#print axioms Series13.WS5.ws5_audit_genuine_connection
#print axioms Series13.WS5.ws5_audit_exogeneity
#print axioms Series13.WS5.ws5_audit_structural_defect
-- concrete carriers: the verdict unconditional on carrier existence (series-review-2 SR2-2)
#print axioms Series13.WS5.ws5_dual_witnessed
#print axioms Series13.WS5.ws5_total_witnessed
