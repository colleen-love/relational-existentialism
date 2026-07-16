# Series 05 — Axiom-check log (committed evidence)

**Addresses project-review-1.md finding S3** (and **project-review-2.md S3**: "committed
evidence, not re-verified" — the log must be regenerated against the *addressed* build). This
file records the actual `lake build` result and the `#print axioms` output for every headline
theorem, captured from a clean build against the pinned toolchain.

- **Regenerated:** against the **obligations-#2/#12 build** (`paper-prep-1.md`) — i.e. after
  closing register #2 (carrier-level descent on `Winf`) and #12 (a genuine, non-`Iff.rfl`
  relating = composed-of coincidence). The lines below are the verbatim
  `#print axioms` emit for all **47** headline theorems, now including
  `ws6_carrier_descent_nonterminating`, `ws6_carrier_descent_crosslevel`, `lcomp_lstr`, and
  `ws6_relating_is_composition_coincidence` (prior passes added `ws7_cardinalTower_du`,
  `ws7_notop_unconditional`, `ws7_payoffs_unconditional`, `boundRelax_injective`, and the
  universe-refactored `ws3_no_top` / `GradedObsCoherentShift`).
- **Toolchain:** `leanprover/lean4:v4.15.0`, Mathlib `v4.15.0` (see `lake/lean-toolchain`,
  `lake/lakefile.toml`).
- **Build:** `cd lake && lake build` → `Build completed successfully.` (default targets now
  `Series04` + `Series05`, each in its own module namespace; the Series 05 pass is `Series05` =
  `ws1 … ws7` + `Series05.AxiomCheck`).
- **Textual audit:** no `sorry`, no `admit`, no custom `axiom`, no `native_decide` in
  `series-05/formal/` (the only textual hits are inside doc-comments).
- **Closure gate:** `scripts/gate.sh` → `OK series-05/ — imports resolve only to allowed
  roots` (nothing imported from `series-04/` or `archive/`).

To reproduce: warm the Mathlib cache (environment Setup script), then `cd lake && lake build`;
the `#print axioms` lines are emitted by `series-05/formal/Series05/AxiomCheck.lean`.

## `#print axioms` output

Every headline theorem depends only on Mathlib's standard three — `propext`,
`Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom axiom. (Two purely
definitional/decidable results depend on *no* axioms.)

```
-- WS1
'Series05.WS1.ws1_colim_equiv'        : [propext, Classical.choice, Quot.sound]
'Series05.WS1.ws1_bisim_eq_colim'     : [propext, Classical.choice, Quot.sound]
'Series05.WS1.ws1_omega_selfloop'     : [propext, Classical.choice, Quot.sound]
'Series05.WS1.ws1_local_bound'        : [propext, Classical.choice, Quot.sound]

-- WS2
'Series05.WS2.ws2_collapse'           : [propext, Classical.choice, Quot.sound]
'Series05.WS2.ws2_explosion_dilemma'  : [propext, Classical.choice, Quot.sound]
'Series05.WS2.ws2_no_least'           : [propext, Quot.sound]
'Series05.WS2.ws2_no_great'           : [propext, Quot.sound]
'Series05.WS2.ws2_self_dual'          : [propext, Classical.choice, Quot.sound]
'Series05.WS2.ws2_forced_answer'      : [propext, Classical.choice, Quot.sound]

-- WS3
'Series05.WS3.ws3_no_top'             : [propext, Classical.choice, Quot.sound]
'Series05.WS3.ws3_wall_vs_grain'      : [propext, Classical.choice, Quot.sound]
'Series05.WS3.nuLk_card_ge'           : [propext, Classical.choice, Quot.sound]
'Series05.WS3.boundRelax_injective'   : [propext, Classical.choice, Quot.sound]  -- gate settled
'Series05.WS3.ws1_gate_settled'       : [propext, Classical.choice, Quot.sound]  -- gate settled

-- WS4
'Series05.WS4.ws4_groundless_no_collapse' : [propext, Classical.choice, Quot.sound]
'Series05.WS4.ws4_singly_bounded_collapses' : [propext, Classical.choice, Quot.sound]
'Series05.WS4.ws4_poles_coincide'     : [propext, Quot.sound]
'Series05.WS4.ws4_no_completing_view' : [propext, Classical.choice, Quot.sound]
'Series05.WS4.ws4_unknowable_eq_noview' : [propext, Classical.choice, Quot.sound]

-- WS5
'Series05.WS5.ws5_endogenous_tower'   : [propext, Classical.choice, Quot.sound]
'Series05.WS5.ws5_stratification_frees_bound' : [propext, Classical.choice, Quot.sound]
'Series05.WS5.ws5_contraction_insufficient' : [propext, Classical.choice, Quot.sound]

-- WS6
'Series05.WS6.ws6_crosslevel_never_annihilate' : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_descent_nonterminating' : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_carrier_descent_nonterminating' : [propext, Classical.choice, Quot.sound]  -- #2 CLOSED: descent at the tower carrier Winf
'Series05.WS6.ws6_carrier_descent_crosslevel' : [propext, Classical.choice, Quot.sound]  -- #2: strictly-decreasing tower levels (no-least-index)
'Series05.WS6.lcomp_lstr'             : [propext, Classical.choice, Quot.sound]  -- composition is a faithful section of observation
'Series05.WS6.ws6_relating_is_composition_coincidence' : [propext, Classical.choice, Quot.sound]  -- #12 CLOSED: genuine coincidence (not Iff.rfl)
'Series05.WS6.ws6_relating_is_composition' : [propext, Classical.choice, Quot.sound]  -- old alias, retained as a non-load-bearing remark
'Series05.WS6.ws6_lawvere_incomplete' : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_omega_nonterminating' : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_tower_unknowable'   : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_no_strict_graded_law' : [propext, Classical.choice, Quot.sound]
'Series05.WS6.ws6_graded_obs_coherent_shift_exists' : [propext, Classical.choice, Quot.sound]  -- pass-2 R4 rename

-- WS7
'Series05.WS7.ws7_double_unboundedness' : [propext, Classical.choice, Quot.sound]
'Series05.WS7.ws7_setindexed_walls'   : [propext, Classical.choice, Quot.sound]  -- now [Small.{u} Idx]
'Series05.WS7.ws7_properclass_index_cofinal' : [propext, Classical.choice, Quot.sound]
'Series05.WS7.ws7_no_du_tower'        : [propext, Classical.choice, Quot.sound]  -- now [Small.{u} Idx]
-- WS7 — the S1 antecedent DISCHARGED: a genuinely built doubly-unbounded tower (charter §9)
'Series05.WS7.ws7_cardinalTower_du'   : [propext, Classical.choice, Quot.sound]  -- cardinalTower ⊨ DoubleUnboundedness
'Series05.WS7.ws7_notop_unconditional' : [propext, Classical.choice, Quot.sound]  -- no open antecedent
'Series05.WS7.ws7_payoffs_unconditional' : [propext, Classical.choice, Quot.sound]  -- no open antecedent
'Series05.WS7.ws7_payoffs_hold'       : [propext, Classical.choice, Quot.sound]
'Series05.WS7.ws7_leakfree_NOT_from_du' : [propext, Classical.choice, Quot.sound]
'Series05.WS7.ws7_notop_vs_collapse_distinct' : [propext, Classical.choice, Quot.sound]
'Series05.WS7.ws7_verdict_eq'         : (no axioms — `rfl`)
'Series05.WS7.ws7_not_trivialized'    : (no axioms — `decide`)
```

*`Classical.choice` enters via the transcribed QPF `repr` / terminal-coalgebra machinery,
exactly as in Series 04/03; it is a Mathlib-base axiom, not a new one. This log is regenerated
whenever `AxiomCheck.lean` or its dependencies change.*
