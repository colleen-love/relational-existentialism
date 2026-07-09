/-
`series-4/formal/AxiomCheck.lean`

Imports the whole Series 4 build and emits a `#print axioms` record for the headline
theorem of every workstream. The bar for this design (charter §7): **sorry-free and
no new axioms.** A clean pass shows every theorem below rests only on Mathlib's
standard three — `propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and
no custom `axiom`. (`Classical.choice` enters via the QPF `repr` and the
middle-selection in weak-pullback preservation, as in Series 3; it is a Mathlib-base
axiom, not a new one.)
-/
import Series4

-- WS1 — the carrier, the face, the inherited gate, Ω's face
#print axioms Series4.WS1.ws1_weak_pullback_inherited
#print axioms Series4.WS1.ws1_face_forced
#print axioms Series4.WS1.ws1_omega_face

-- WS2 — collapse, leak, forced answer, carrier bound
#print axioms Series4.WS2.ws2_collapse
#print axioms Series4.WS2.ws2_leak
#print axioms Series4.WS2.ws2_leak_witness
#print axioms Series4.WS2.ws2_botfree_safe
#print axioms Series4.WS2.ws2_forced_answer
#print axioms Series4.WS2.carrier_card_ge

-- WS3 — the labelled carrier, plurality without atoms, and composition-closure
#print axioms Series4.WS3.ws3_loopface_ne
#print axioms Series4.WS3.ws3_same_succ_diff_face
#print axioms Series4.WS3.ws3_plurality_core
#print axioms Series4.WS3.ws3_plurality_core_concrete
#print axioms Series4.WS3.ws3_loop_nonatomic
#print axioms Series4.WS3.lcomp_dest
#print axioms Series4.WS3.ws3_faces_never_annihilate

-- WS4 — the no-top wall (cardinal wall; reach form) and positioned views
#print axioms Series4.WS4.ws4_no_top_cardinal
#print axioms Series4.WS4.ws4_no_top_reach
#print axioms Series4.WS4.ws4_faces_inject
#print axioms Series4.WS4.ws4_no_global_observer
#print axioms Series4.WS4.ws4_view_is_positioned
#print axioms Series4.WS4.ws4_substantive_standpoints
#print axioms Series4.WS4.ws4_pole_coincidence_residue

-- WS5 — the self-bounding thesis
#print axioms Series4.WS5.ws5_contraction_insufficient
#print axioms Series4.WS5.ws5_quotient_insufficient
#print axioms Series4.WS5.ws5_global_groundless_collapses
#print axioms Series4.WS5.ws5_omega_endogenous_point
#print axioms Series4.WS5.ws5_endogenous_bound

-- WS6 — the two incompletenesses (self-face is trivial on R2; A1 scoped)
#print axioms Series4.WS6.ws6_selfface_trivial
#print axioms Series4.WS6.ws6_selfface_proper_nonselfrelating
#print axioms Series4.WS6.ws6_lawvere_incomplete
#print axioms Series4.WS6.ws6_blindspot_nonempty
#print axioms Series4.WS6.ws6_omega_nonterminating
#print axioms Series4.WS6.ws6_selfmodel_is_attention_fixedpoint

-- WS7 — the anti-trivialization audit and verdict
#print axioms Series4.WS7.ws7_finitude_of_facing
#print axioms Series4.WS7.ws7_payoffs_hold
#print axioms Series4.WS7.ws7_incompleteness_off_from_finitude
#print axioms Series4.WS7.ws7_deductions_dont_collapse
#print axioms Series4.WS7.ws7_plurality_vs_collapse_distinct
#print axioms Series4.WS7.ws7_not_trivialized
#print axioms Series4.WS7.ws7_verdict_eq
