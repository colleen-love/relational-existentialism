# Series 12 — Axiom-Check Log

Captured from `lake build Series12.AxiomCheck` (`#print axioms` over every headline theorem). The bar
(charter §7): sorry-free and no new axioms. Every headline rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`. (`Classical.choice`
enters via `Classical.propDecidable` for the reification section's Set-equality and via `toPk` / `Cardinal`
machinery, a Mathlib-base axiom, not a new one; `ws_witness_rank_noninjective` needs only `propext` /
`Quot.sound`.)

Series-review-1 (Phase D/E) additions: the layered underdetermination `ws4_underdetermined_up` (SR1-2) is
included; the demoted `ws3_attention_compass_dual` (SR1-3) is removed.

```
'Series12.WS1.ws1_two_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS1.ws1_shape_coincidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS1.ws1_coincidence_not_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS1.ws2_import_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS1.ws3_atomless_distinct_is_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws2_attention_subtractive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws2_many_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws2_many_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws2_reification_loadbearing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws_witness_rank_noninjective' depends on axioms: [propext, Quot.sound]
'Series12.WS2.ws2_no_import_is_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws2_distinction_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS2.ws3_no_total_attention' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS3.ws3_compass_exogenous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS3.ws3_compass_layered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS4.ws4_underdetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS4.ws4_underdetermined_up' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS4.ws4_wall_is_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS4.ws4_convergence_decided_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS5.ws5_verdict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS5.ws5_name_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS5.ws5_verdict_not_decided' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS6.ws6_provable_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS6.ws6_permanent_opens' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS6.ws6_tenets_aligned' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_verdict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_no_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_model_pair_genuine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_inhabitation_genuine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_names_not_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_strip_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series12.WS7.ws7_verdict_is_shapeDrawn' depends on axioms: [propext, Classical.choice, Quot.sound]
```

*Build: `lake build Series12 Series12.AxiomCheck` completed successfully (Lean 4 v4.15.0 / Mathlib
v4.15.0). The closure gate (`scripts/gate.sh`) confirms Series 12 imports resolve only to `Series12.*`
roots plus Mathlib: nothing is imported across series.*
