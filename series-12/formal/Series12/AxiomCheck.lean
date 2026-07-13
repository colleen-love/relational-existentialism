/-
`series-12/formal/Series12/AxiomCheck.lean`

Imports the whole Series 12 build and emits a `#print axioms` record for the headline theorem of every
workstream. The bar (charter §7): sorry-free and no new axioms. A clean pass shows every headline rests only
on Mathlib's standard three, `propext` / `Classical.choice` / `Quot.sound`, with no `sorryAx` and no custom
`axiom`. (`Classical.choice` enters via `Classical.propDecidable` for the reification section's Set-equality
and via `toPk` / `Cardinal` machinery, a Mathlib-base axiom, not a new one.)
-/
import Series12

-- WS1 - the opening and the coincidence (forced-for-all vs exists-satisfying, never object-identity)
#print axioms Series12.WS1.ws1_two_halves
#print axioms Series12.WS1.ws1_shape_coincidence
#print axioms Series12.WS1.ws1_coincidence_not_identity
#print axioms Series12.WS1.ws1_coincidence_not_identity_witness
#print axioms Series12.WS1.ws2_import_theorem
#print axioms Series12.WS1.ws3_atomless_distinct_is_import

-- WS2 - knowing: finite attention and the inhabited opening (the plurality, reification load-bearing)
#print axioms Series12.WS2.ws2_attention_subtractive
#print axioms Series12.WS2.ws2_many_general
#print axioms Series12.WS2.ws2_many_witness
#print axioms Series12.WS2.ws2_attention_makes_real
#print axioms Series12.WS2.ws2_reification_loadbearing
#print axioms Series12.WS2.ws_witness_rank_noninjective
#print axioms Series12.WS2.ws2_no_import_is_one
#print axioms Series12.WS2.ws2_distinction_free
#print axioms Series12.WS2.ws3_no_total_attention

-- WS3 - feeling: the compass TYPE, parametric, exogenous (an import), layered
#print axioms Series12.WS3.ws3_compass_exogenous
#print axioms Series12.WS3.ws3_compass_exogenous_import
#print axioms Series12.WS3.ws3_compass_layered

-- WS4 - convergence defined and underdetermined over the faithful class (the wall, genuinely open fork)
#print axioms Series12.WS4.ws4_underdetermined
#print axioms Series12.WS4.ws4_fork_open
#print axioms Series12.WS4.ws4_underdetermined_up
#print axioms Series12.WS4.ws4_wall_is_structural
#print axioms Series12.WS4.ws4_convergence_decided_shape

-- WS5 - the verdict as a function of the fork, non-constant, and the generalized neutrality
#print axioms Series12.WS5.ws5_verdict_eq
#print axioms Series12.WS5.ws5_verdict_reaches_both
#print axioms Series12.WS5.ws5_name_neutral
#print axioms Series12.WS5.ws5_verdict_not_decided

-- WS6 - the program's close: the provable core and the permanent opens as theorems
#print axioms Series12.WS6.ws6_provable_core
#print axioms Series12.WS6.ws6_permanent_opens
#print axioms Series12.WS6.ws6_tenets_aligned

-- WS7 - the anti-circularity audit and the typed verdict (SHAPE-DRAWN)
#print axioms Series12.WS7.ws7_verdict_eq
#print axioms Series12.WS7.ws7_no_evaluation
#print axioms Series12.WS7.ws7_model_pair_genuine
#print axioms Series12.WS7.ws7_fork_can_close
#print axioms Series12.WS7.ws7_inhabitation_genuine
#print axioms Series12.WS7.ws7_names_not_terms
#print axioms Series12.WS7.ws7_strip_ledger
#print axioms Series12.WS7.ws7_verdict_is_shapeDrawn
