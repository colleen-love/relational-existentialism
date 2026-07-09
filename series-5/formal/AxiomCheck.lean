/-
`series-5/formal/AxiomCheck.lean`

Imports the whole Series 5 build and emits a `#print axioms` record for the headline
theorem of every workstream. The bar (charter §7, inherited from Series 4): **sorry-free
and no new axioms.** A clean pass shows every headline theorem rests only on Mathlib's
standard three — `propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no
custom `axiom`. (`Classical.choice` enters via the transcribed QPF `repr` and the
middle-selection machinery, as in Series 4/3; it is a Mathlib-base axiom, not a new one.)
-/
import Series5

-- WS1 — the colimit, the gate, Ω recovered, the local bound
#print axioms Series5.WS1.ws1_colim_equiv
#print axioms Series5.WS1.ws1_bisim_eq_colim
#print axioms Series5.WS1.ws1_omega_selfloop
#print axioms Series5.WS1.ws1_local_bound

-- WS2 — the collapse, the Explosion Dilemma, the ℤ index, the forced answer
#print axioms Series5.WS2.ws2_collapse
#print axioms Series5.WS2.ws2_explosion_dilemma
#print axioms Series5.WS2.ws2_no_least
#print axioms Series5.WS2.ws2_no_great
#print axioms Series5.WS2.ws2_self_dual
#print axioms Series5.WS2.ws2_forced_answer

-- WS3 — no-top on the colimit, the coincidence, the labelled carrier bound
#print axioms Series5.WS3.ws3_no_top
#print axioms Series5.WS3.ws3_wall_vs_grain
#print axioms Series5.WS3.nuLk_card_ge

-- WS4 — groundless-no-collapse, poles, no-completing-view, the coincidence
#print axioms Series5.WS4.ws4_groundless_no_collapse
#print axioms Series5.WS4.ws4_singly_bounded_collapses
#print axioms Series5.WS4.ws4_poles_coincide
#print axioms Series5.WS4.ws4_no_completing_view
#print axioms Series5.WS4.ws4_unknowable_eq_noview

-- WS5 — endogenous tower, the M1/M2 adjudication, the standing negative
#print axioms Series5.WS5.ws5_endogenous_tower
#print axioms Series5.WS5.ws5_stratification_frees_bound
#print axioms Series5.WS5.ws5_contraction_insufficient

-- WS6 — leak-free transport, descent, the incompletenesses, the distributive laws
#print axioms Series5.WS6.ws6_crosslevel_never_annihilate
#print axioms Series5.WS6.ws6_descent_nonterminating
#print axioms Series5.WS6.ws6_relating_is_composition
#print axioms Series5.WS6.ws6_lawvere_incomplete
#print axioms Series5.WS6.ws6_omega_nonterminating
#print axioms Series5.WS6.ws6_tower_unknowable
#print axioms Series5.WS6.ws6_no_strict_graded_law
#print axioms Series5.WS6.ws6_graded_weak_law_exists

-- WS7 — double-unboundedness, the S1 obstruction, the payoffs, the anchors, the verdict
#print axioms Series5.WS7.ws7_double_unboundedness
#print axioms Series5.WS7.ws7_setindexed_walls
#print axioms Series5.WS7.ws7_no_du_tower
#print axioms Series5.WS7.ws7_payoffs_hold
#print axioms Series5.WS7.ws7_leakfree_NOT_from_du
#print axioms Series5.WS7.ws7_notop_vs_collapse_distinct
#print axioms Series5.WS7.ws7_verdict_eq
#print axioms Series5.WS7.ws7_not_trivialized
