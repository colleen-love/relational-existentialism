# Series 5 — Axiom-check log (committed evidence)

**Addresses project-review-1.md finding S3** ("the axiom-clean / `lake build`-green claim is
static, not shown"). This file records the actual `lake build` result and the `#print axioms`
output for every headline theorem, captured from a clean build against the pinned toolchain.

- **Toolchain:** `leanprover/lean4:v4.15.0`, Mathlib `v4.15.0` (see `lake/lean-toolchain`,
  `lake/lakefile.toml`).
- **Build:** `cd lake && lake build` → `Build completed successfully.` (default target
  `Series5` = `ws1 … ws7` + `AxiomCheck`).
- **Textual audit:** no `sorry`, no `admit`, no custom `axiom`, no `native_decide` in
  `series-5/formal/` (the only textual hits are inside doc-comments).
- **Closure gate:** `scripts/gate.sh` → `OK series-5/ — imports resolve only to allowed
  roots` (nothing imported from `series-4/` or `archive/`).

To reproduce: warm the Mathlib cache (environment Setup script), then `cd lake && lake build`;
the `#print axioms` lines are emitted by `series-5/formal/AxiomCheck.lean`.

## `#print axioms` output

Every headline theorem depends only on Mathlib's standard three — `propext`,
`Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom axiom. (Two purely
definitional/decidable results depend on *no* axioms.)

```
-- WS1
'Series5.WS1.ws1_colim_equiv'        : [propext, Classical.choice, Quot.sound]
'Series5.WS1.ws1_bisim_eq_colim'     : [propext, Classical.choice, Quot.sound]
'Series5.WS1.ws1_omega_selfloop'     : [propext, Classical.choice, Quot.sound]
'Series5.WS1.ws1_local_bound'        : [propext, Classical.choice, Quot.sound]

-- WS2
'Series5.WS2.ws2_collapse'           : [propext, Classical.choice, Quot.sound]
'Series5.WS2.ws2_explosion_dilemma'  : [propext, Classical.choice, Quot.sound]
'Series5.WS2.ws2_no_least'           : [propext, Quot.sound]
'Series5.WS2.ws2_no_great'           : [propext, Quot.sound]
'Series5.WS2.ws2_self_dual'          : [propext, Classical.choice, Quot.sound]
'Series5.WS2.ws2_forced_answer'      : [propext, Classical.choice, Quot.sound]

-- WS3
'Series5.WS3.ws3_no_top'             : [propext, Classical.choice, Quot.sound]
'Series5.WS3.ws3_wall_vs_grain'      : [propext, Classical.choice, Quot.sound]
'Series5.WS3.nuLk_card_ge'           : [propext, Classical.choice, Quot.sound]

-- WS4
'Series5.WS4.ws4_groundless_no_collapse' : [propext, Classical.choice, Quot.sound]
'Series5.WS4.ws4_singly_bounded_collapses' : [propext, Classical.choice, Quot.sound]
'Series5.WS4.ws4_poles_coincide'     : [propext, Quot.sound]
'Series5.WS4.ws4_no_completing_view' : [propext, Classical.choice, Quot.sound]
'Series5.WS4.ws4_unknowable_eq_noview' : [propext, Classical.choice, Quot.sound]

-- WS5
'Series5.WS5.ws5_endogenous_tower'   : [propext, Classical.choice, Quot.sound]
'Series5.WS5.ws5_stratification_frees_bound' : [propext, Classical.choice, Quot.sound]
'Series5.WS5.ws5_contraction_insufficient' : [propext, Classical.choice, Quot.sound]

-- WS6
'Series5.WS6.ws6_crosslevel_never_annihilate' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_descent_nonterminating' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_relating_is_composition' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_lawvere_incomplete' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_omega_nonterminating' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_tower_unknowable'   : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_no_strict_graded_law' : [propext, Classical.choice, Quot.sound]
'Series5.WS6.ws6_graded_weak_law_exists' : [propext, Classical.choice, Quot.sound]

-- WS7
'Series5.WS7.ws7_double_unboundedness' : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_setindexed_walls'   : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_no_du_tower'        : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_payoffs_hold'       : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_leakfree_NOT_from_du' : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_notop_vs_collapse_distinct' : [propext, Classical.choice, Quot.sound]
'Series5.WS7.ws7_verdict_eq'         : (no axioms — `rfl`)
'Series5.WS7.ws7_not_trivialized'    : (no axioms — `decide`)
```

*`Classical.choice` enters via the transcribed QPF `repr` / terminal-coalgebra machinery,
exactly as in Series 4/3; it is a Mathlib-base axiom, not a new one. This log is regenerated
whenever `AxiomCheck.lean` or its dependencies change.*
