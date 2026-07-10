# Series 7 — Axiom Check Log

Machine-checked `#print axioms` against the pinned build (Lean 4 v4.15.0 / Mathlib v4.15.0),
run via `lake env lean series-7/formal/Series7/AxiomCheck.lean`. Every headline theorem is
sorry-free and rests only on Mathlib's standard three (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorryAx`, no custom `axiom`.

Recorded 2026-07-10.

```
'Series7.WS1.ws1_atomless_bisim' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS1.ws1_recovers_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS1.ws1_recovers_dynamic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS1.ws1_productive_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS2.ws2_import_theorem_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS2.ws2_import_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS2.ws2_plurality_requires_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS2.ws2_dynamic_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS2.ws2_non_circular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS3.ws3_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS3.ws3_history_collapses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS3.ws3_trichotomy_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS3.ws3_leaf_not_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS3.ws3_import_not_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS4.ws4_import_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS4.ws4_labels_are_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS4.ws4_levels_are_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS4.ws4_program_explained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS5.ws5_limit_reintroduces_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS5.ws5_leafy_plurality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS5.ws5_adjudication_justified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS5.ws5_fork_is_genuine' does not depend on any axioms
'Series7.WS6.ws6_provable_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS6.ws6_universal_is_heuristic' does not depend on any axioms
'Series7.WS7.ws7_non_circularity_audit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS7.ws7_trichotomy_not_definitional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series7.WS7.ws7_strip_ledger_clean' does not depend on any axioms
'Series7.WS7.ws7_verdict_eq' does not depend on any axioms
'Series7.WS7.ws7_not_circular' does not depend on any axioms
'Series7.WS7.ws7_circular_if_fiat' does not depend on any axioms
'Series7.WS7.ws7_import_forced_if_exhaustive' does not depend on any axioms
```
