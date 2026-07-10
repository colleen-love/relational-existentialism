/-
`series-7/formal/Series7/AxiomCheck.lean`

Imports the whole Series 7 build and emits a `#print axioms` record for the headline theorem of
every workstream. The bar (charter §7, inherited from Series 4/5/6): **sorry-free and no new
axioms.** A clean pass shows every headline theorem rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`.
(`Classical.choice` enters via the `toPk` finiteness bound and `Cardinal` machinery, a
Mathlib-base axiom, not a new one.)
-/
import Series7

-- WS1 — the engine and the two recovered instances
#print axioms Series7.WS1.ws1_atomless_bisim
#print axioms Series7.WS1.ws1_recovers_static
#print axioms Series7.WS1.ws1_recovers_dynamic
#print axioms Series7.WS1.ws1_productive_unique

-- WS2 — the Import Theorem and non-circularity
#print axioms Series7.WS2.ws2_import_theorem_static
#print axioms Series7.WS2.ws2_import_theorem
#print axioms Series7.WS2.ws2_plurality_requires_drop
#print axioms Series7.WS2.ws2_dynamic_instance
#print axioms Series7.WS2.ws2_non_circular

-- WS3 — the single-coalgebra dichotomy + the contentful third kind on the process
#print axioms Series7.WS3.ws3_dichotomy
#print axioms Series7.WS3.ws3_atomless_distinct_is_import
#print axioms Series7.WS3.ws3_leafy_thread_inhabited
#print axioms Series7.WS3.ws3_leafy_thread_collapses
#print axioms Series7.WS3.ws3_no_same_limit_haecceity
#print axioms Series7.WS3.ws3_history_collapses
#print axioms Series7.WS3.ws3_leaf_not_import
#print axioms Series7.WS3.ws3_import_not_leaf

-- WS4 — the imports catalogued: drop (1) [labelled, survives quotient] and drop (2) [plain non-reduction]
#print axioms Series7.WS4.ws4_labels_are_import
#print axioms Series7.WS4.ws4_label_drop_atomless
#print axioms Series7.WS4.ws4_label_survives_quotient
#print axioms Series7.WS4.ws4_free_label_is_import
#print axioms Series7.WS4.ws4_recoverable_not_import
#print axioms Series7.WS4.ws4_recoverable_atomless_collapses
#print axioms Series7.WS4.ws4_recoverable_plurality_requires_drop
#print axioms Series7.WS4.ws4_labelLoop_not_recoverable
#print axioms Series7.WS4.ws4_restriction_collapses_escalation_imports
#print axioms Series7.WS4.ws4_atomless_recoverable_all_bisimL
#print axioms Series7.WS4.ws4_atomless_label_distinction_imports
#print axioms Series7.WS4.ws4_subset_selection_survives_as_import
#print axioms Series7.WS4.att_cannot_distinguish_atomless_histories
#print axioms Series7.WS4.ws4_toy_loop_is_drop2
#print axioms Series7.WS4.ws4_index_reuses_label_mechanism
#print axioms Series7.WS4.ws4_program_explained

-- WS5 — the limit-atomlessness loophole
#print axioms Series7.WS5.ws5_limit_reintroduces_leaves
#print axioms Series7.WS5.ws5_leafy_pair
#print axioms Series7.WS5.ws5_adjudication_justified
#print axioms Series7.WS5.ws5_fork_is_genuine

-- WS6 — the heuristic ceiling
#print axioms Series7.WS6.ws6_provable_core
#print axioms Series7.WS6.ws6_universal_is_heuristic

-- The verdict `def`s themselves (series-review-3 C5: the reported constants, not just their eq-lemmas)
#print axioms Series7.WS7.ws7_verdict
#print axioms Series7.WS5.ws5_loophole_adjudication
#print axioms Series7.WS6.ws6_universal

-- WS7 — the audit and the mechanized (certificate-wired) verdict
#print axioms Series7.WS7.leafCoalg_behav
#print axioms Series7.WS7.ws7_non_circularity_audit
#print axioms Series7.WS7.ws7_kinds_distinct
#print axioms Series7.WS7.ws7_strip_ledger
#print axioms Series7.WS7.ws7_audit
#print axioms Series7.WS7.ws7_verdict_eq
#print axioms Series7.WS7.ws7_audited_not_circular
#print axioms Series7.WS7.ws7_import_forced_if_exhaustive
