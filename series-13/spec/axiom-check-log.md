# Series 13 — Axiom-Check Log

Captured from `lake build Series13.AxiomCheck` (`#print axioms` over every headline theorem). The bar
(charter §7): sorry-free and no new axioms. Every headline rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`. (`Classical.choice`
enters via `Classical.propDecidable` for `residue`'s `not_not`, the reference-fold, and the verdict's
carrier case-split, and via `toPk` / `Cardinal` machinery — Mathlib-base axioms, not new ones.)

**Capture provenance.** Phase E (series-review-1 closure), branch `claude/series-13-design-docs-s7uthq`,
after merging `origin/main`. Re-run confirming `series-review-1.md` SR1-6 (the review could not run Lean).
The strengthened non-triviality (`ws1_orders_lab_nontrivial` third conjunct, `ws2_mint_nontrivial`) is
included and axiom-clean. The three-series `lake build` (07/12/13) succeeds and `scripts/gate.sh` is green
on all three (SR1-4 closed).

**The four critical checks, all confirmed:**
1. Fork OPEN — `ws4_mint_not_surjective` locates up to `≈`, never sorts; no `Origin`/`genealogy` term.
2. Connection GENUINE — orders non-trivial with the ANTITONE REFERENCE POSITION now load-bearing in the
   certificate (`ws1_orders_lab_nontrivial` third conjunct) and non-triviality at MINT POINTS
   (`ws2_mint_nontrivial`), plus `ws3_roundtrip_not_identity` (SR1-1, SR1-2 closed Fixed).
3. Mint EXOGENOUS — `ws2_mint_exogenous` / `ws2_mint_not_plain_function`.
4. Defect STRUCTURAL — `ws4_exclusion_structural`, the diagonal link surviving `≈`.

**Computed verdict.** `ws5_verdict = Dual` on any carrier with a second hold (`ws5_verdict_eq`), `= Total`
on the degenerate single-hold carrier (`ws5_verdict_degenerate`). FLAT-LAYER scope; layer-stability a named
open. Domain narrowing (`Lab` vs `LkObj`) disclosed as charter discrepancy CD-1 (SR1-3).

```
'Series13.WS1.ws1_orders_insp_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws1_orders_lab_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws2_import_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws3_atomless_distinct_is_import' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws1_atomless_bisim' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws2_residue_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws2_residue_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws1_no_self_total_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws1_shape_coincidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS1.ws1_coincidence_not_identity_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS2.ws2_mint_lands_in_opening' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS2.ws2_transport_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS2.ws2_mint_exogenous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS2.ws2_mint_not_plain_function' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS2.ws2_mint_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_galois' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_mint_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_read_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_roundtrip_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_roundtrip_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS3.ws3_roundtrip_not_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS4.ws4_mint_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS4.ws4_exclusion_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS4.ws4_mint_essentially_surjective_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_verdict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_verdict_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_verdict_not_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_genuine_connection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_exogeneity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_structural_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
```
