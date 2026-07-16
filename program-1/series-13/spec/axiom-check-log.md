# Series 13 — Axiom-Check Log

Captured from `lake build Series13.AxiomCheck` (`#print axioms` over every headline theorem). The bar
(charter §7): sorry-free and no new axioms. Every headline rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`. (`Classical.choice`
enters via `Classical.propDecidable` for `residue`'s `not_not`, the reference-fold, and the verdict's
carrier case-split, and via `toPk` / `Cardinal` machinery — Mathlib-base axioms, not new ones.)

**Capture provenance.** Phase E (series-review-2 closure), branch `claude/series-13-design-docs-s7uthq`,
after merging `origin/main`. 34 headline records, all `[propext, Classical.choice, Quot.sound]`. Includes the
strengthened non-triviality (`ws1_orders_lab_nontrivial` third conjunct, `ws2_mint_nontrivial`, SR1-1/SR1-2)
and the concrete carriers (`ws5_dual_witnessed`, `ws5_total_witnessed`, SR2-2) making the verdict
unconditional on carrier existence. The three-series `lake build` (07/12/13) succeeds; `scripts/gate.sh` is
green on all three.

**Attestation status (`series-review-2.md` SR2-1, recorded per its explicit request).** Axiom-cleanliness is
**BUILDER-ATTESTED and REVIEWER-UNVERIFIED** in this program: no reviewing session has reproduced this log,
two review passes running, because the review sandbox has no Lean toolchain and `leanprover-community` is off
its network allowlist (`403 host_not_allowed`). What the reviews DID verify mechanically: source hygiene is
clean (no `sorry`/`admit`/custom `axiom`/`native_decide` in `formal/`, all grep hits docstring prose), and
this log is internally consistent — every `#print axioms` target in `AxiomCheck.lean` diffs exactly against a
record here (no gaps either direction), all standard three, zero non-standard records. The log is coherent
and consistent with the source; it remains a builder self-report until a review environment with the Mathlib
cache reproduces it.

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
'Series13.WS5.ws5_verdict_not_disconnected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_verdict_not_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_genuine_connection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_exogeneity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_audit_structural_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_dual_witnessed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series13.WS5.ws5_total_witnessed' depends on axioms: [propext, Classical.choice, Quot.sound]
```
