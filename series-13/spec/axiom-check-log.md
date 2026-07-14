# Series 13 — Axiom-Check Log

Captured from `lake build Series13.AxiomCheck` (`#print axioms` over every headline theorem). The bar
(charter §7): sorry-free and no new axioms. Every headline rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`. (`Classical.choice`
enters via `Classical.propDecidable` for `residue`'s `not_not`, the reference-fold, and the verdict's
carrier case-split, and via `toPk` / `Cardinal` machinery — Mathlib-base axioms, not new ones.)

**Capture provenance.** Phase C build-all (branch `claude/series-13-design-docs-s7uthq`), the full five
workstreams plus the transcribed premises. The whole Series 13 build compiles `sorry`-free and axiom-clean;
the three-series `lake build` (Series 07, Series 12, Series 13) succeeds.

**The four critical checks (the series' reasons to exist), all confirmed at build:**
1. The fork stays OPEN — WS4's `ws4_mint_not_surjective` LOCATES an import outside the mint's image up to `≈`
   (`¬ ∃ insp, mintL insp ≈ outWit`); no theorem sorts an out-of-image import into given/chosen (grep-clean:
   no `Origin`/`genealogy` term, `given`/`chosen` in prose only).
2. The connection is GENUINE — both orders proved non-trivial (`ws1_orders_insp_nontrivial`,
   `ws1_orders_lab_nontrivial`), and the interior round trip proved non-identity at `bRefActive`
   (`ws3_roundtrip_not_identity`): not an isomorphism in disguise.
3. The mint is EXOGENOUS — `ws2_mint_exogenous` a genuine proof term: `plainOf ∘ mintL` is constant in the
   inspection yet the mint is not, so the plain relating cannot perform it (`ws2_mint_not_plain_function`).
4. The defect is STRUCTURAL — `ws4_exclusion_structural`: `≈` preserves the diagonal-link data, every mint is
   on the link, `outWit` is off it. The label (the diagonal) excludes, not a cardinality/universe/typing
   artifact.

**Computed verdict.** `ws5_verdict = Dual` on any carrier with a second hold (`ws5_verdict_eq`, the TOTAL
target refuted by `outWit`), `= Total` on the degenerate single-hold carrier (`ws5_verdict_degenerate`). The
verdict is COMPUTED (branches on the carrier's hold count), never hand-set. FLAT-LAYER scope: the reification
tower is deliberately outside the transcription; layer-stability is a named open (WS5).

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
