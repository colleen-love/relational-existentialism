# Series 06 — Axiom Check Log

Machine-checked `#print axioms` against the pinned build (Lean 4 v4.15.0 / Mathlib v4.15.0),
run via `lake env lean series-06/formal/Series06/AxiomCheck.lean`. Every headline theorem is
sorry-free and rests only on Mathlib's standard three (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorryAx`, no custom `axiom`. (`Classical.choice` enters via the `toPk`
finiteness bound and `Cardinal` machinery, a Mathlib-base axiom, not a new one.)

Recorded 2026-07-10.

```
'Series06.WS1.proc_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS1.ws1_process_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS1.ws1_no_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS1.ws1_omega_process' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS1.ws1_productive_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS1.ws1_no_productive_plurality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS2.ws2_static_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS2.ws2_escapes_are_imports' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS2.ws2_subsumes_parmenides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS2.ws2_subsumes_tower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS2.ws2_forced_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_incompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_residue_is_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_fpf_eq_incompleteness_eq_nontermination' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_residue_new' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_diagonal_drives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS3.ws3_omega_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_survey_lossy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_residue_one_to_many' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_arrow_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_no_return' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_arrow_has_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS4.ws4_arrow_from_properness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_agree_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_agreement_is_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_plurality_forbids_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_causal_partial_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_incomparability_is_bare_poset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS5.ws5_omega_absolute_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_incompleteness_inherited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_groundlessness_from_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_no_view_from_nowhere' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_atomless_and_plural_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_plurality_costs_an_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS6.ws6_one_engine_obstructed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_one_incompletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_payoffs_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_engine_not_painted_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_distinctness_anchors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_strip_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_c2_collapses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series06.WS7.ws7_verdict_eq' does not depend on any axioms
'Series06.WS7.ws7_not_trivialized' does not depend on any axioms
```
