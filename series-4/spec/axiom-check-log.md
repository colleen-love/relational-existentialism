# Series 4 — machine-checked axiom log

Output of `#print axioms` (via `series-4/formal/AxiomCheck.lean`) over every
headline theorem of WS1–WS7, run against the pinned toolchain. Every theorem rests
only on Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`), or
on no axioms; there is no `sorryAx` and no custom `axiom`.

```
Toolchain : leanprover/lean4:v4.15.0
Mathlib   : rev v4.15.0 (see lake/lakefile.toml)
Build     : cd lake && lake build Series4 AxiomCheck  →  Build completed successfully
sorryAx   : none
```

## Axiom report (one line per headline theorem)

```
'Series4.WS1.ws1_weak_pullback_inherited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS1.ws1_face_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS1.ws1_omega_face' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS2.ws2_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS2.ws2_leak' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS2.ws2_leak_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS2.ws2_botfree_safe' does not depend on any axioms
'Series4.WS2.ws2_forced_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS2.carrier_card_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_loopface_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_same_succ_diff_face' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_plurality_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_plurality_core_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_loop_nonatomic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.lcomp_dest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS3.ws3_faces_never_annihilate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_no_top_cardinal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_no_top_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_faces_inject' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_no_global_observer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_view_is_positioned' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_substantive_standpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS4.ws4_pole_coincidence_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS5.ws5_contraction_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS5.ws5_quotient_insufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS5.ws5_global_groundless_collapses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS5.ws5_omega_endogenous_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS5.ws5_endogenous_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_selfface_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_selfface_proper_nonselfrelating' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_lawvere_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_blindspot_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_omega_nonterminating' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS6.ws6_selfmodel_is_attention_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_finitude_of_facing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_payoffs_hold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_incompleteness_off_from_finitude' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_deductions_dont_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_plurality_vs_collapse_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Series4.WS7.ws7_not_trivialized' does not depend on any axioms
'Series4.WS7.ws7_verdict_eq' does not depend on any axioms
```
