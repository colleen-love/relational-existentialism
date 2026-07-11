# Series 10 — Axiom Check Log

**Executed axiom pass (series-review-1 R2).** The blind review could not compile in its
environment and correctly flagged the axiom-cleanliness claim as asserted-not-executed. This
log records the ACTUAL output of `lake build Series10.AxiomCheck` (which runs `#print axioms`
over every Series 10 headline), captured 2026-07-11.

- **Toolchain:** `leanprover/lean4:v4.15.0` (Mathlib `v4.15.0`).
- **Command:** `lake build Series10 && lake build Series10.AxiomCheck`
- **Result:** `Build completed successfully`; every headline reduces to Mathlib's standard
  three (`propext` / `Classical.choice` / `Quot.sound`), except `ws6_series11_handoff` (a
  `def`) which depends on no axioms. **No `sorry`, no `admit`, no `native_decide`, no custom
  `axiom`** anywhere in `series-10/formal/` (grep-clean and confirmed by the pass below).

The `Classical.choice` / `Quot.sound` dependencies come from transcribed Mathlib lemmas
(`Cardinal`, `Set`, `Relation.ReflTransGen`) and `Classical.em` in `ws4_dichotomy`; they are
the standard three the whole program treats as the axiom-clean baseline (Series 07/08/09 same).

---

## Captured `#print axioms` output

```
'Series10.WS1.ws1_close_forbidden_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws1_diagonal_forbids_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws1_free_reification' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws1_no_self_total_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws1_reification_is_free_label' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws1_reify_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS1.ws2_residue_is_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS2.ws2_free_label_survives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS2.ws2_growth_is_bookkeeping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS2.ws2_label_free_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS2.ws2_plain_collapse_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS2.ws2_reify_bisim_embeds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS3.ws3_imported_order_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS3.ws3_order_endogenous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS3.ws3_reify_preserves_SHNE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS3.ws3_tower_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS3.ws3_tower_monotone_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS4.ws4_close_forbidden' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS4.ws4_close_forbidden_not_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS4.ws4_diagonal_forbids_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS4.ws4_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS4.ws4_fold_is_reflexivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS5.ws5_fold_not_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS5.ws5_fold_on_scaffold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS5.ws5_step_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS5.ws5_verdict_justified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS6.ws6_fold_scope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS6.ws6_provable_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS6.ws6_series11_handoff' does not depend on any axioms
'Series10.WS7.ws7_audit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_audited_is_bookkeeping' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_audited_not_reificationEstablished' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_bookkeeping_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_close_forbidden_inspection_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_kappa_discipline' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_spine_is_residue_freeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_strip_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_verdict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series10.WS7.ws7_verdict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

*R2 closed: the axiom claim is now executed and recorded, not asserted. Re-run the two commands
above to reproduce.*
