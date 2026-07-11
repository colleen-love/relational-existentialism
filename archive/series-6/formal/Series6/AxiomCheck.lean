/-
`series-6/formal/AxiomCheck.lean`

Imports the whole Series 6 build and emits a `#print axioms` record for the headline theorem
of every workstream. The bar (charter §7, inherited from Series 4/5): **sorry-free and no new
axioms.** A clean pass shows every headline theorem rests only on Mathlib's standard three —
`propext`, `Classical.choice`, `Quot.sound` — with no `sorryAx` and no custom `axiom`.
(`Classical.choice` enters via the finiteness bound `toPk` and `Cardinal` machinery, as in
Series 4/5; it is a Mathlib-base axiom, not a new one.)
-/
import Series6

-- WS1 — the carrier, Ω, and the gate (Ω is the unique productive thread; no productive plurality)
#print axioms Series6.WS1.proc_ext
#print axioms Series6.WS1.ws1_process_exists
#print axioms Series6.WS1.ws1_no_collapse
#print axioms Series6.WS1.ws1_omega_process
#print axioms Series6.WS1.ws1_productive_unique
#print axioms Series6.WS1.ws1_no_productive_plurality

-- WS2 — the Static Collapse Theorem, escapes-are-imports, subsumptions, the forced answer
#print axioms Series6.WS2.ws2_static_collapse
#print axioms Series6.WS2.ws2_escapes_are_imports
#print axioms Series6.WS2.ws2_subsumes_parmenides
#print axioms Series6.WS2.ws2_subsumes_tower
#print axioms Series6.WS2.ws2_forced_answer

-- WS3 — the engine: residue = Cantor diagonal, drives uniquely; the engine identity; Ω orbit
#print axioms Series6.WS3.ws3_incompleteness
#print axioms Series6.WS3.ws3_residue_is_diagonal
#print axioms Series6.WS3.ws3_fpf_eq_incompleteness_eq_nontermination
#print axioms Series6.WS3.ws3_residue_new
#print axioms Series6.WS3.ws3_diagonal_drives
#print axioms Series6.WS3.ws3_omega_orbit

-- WS4 — the arrow: lossy survey, one-to-many residue, strict order; the endogeneity failure
#print axioms Series6.WS4.ws4_survey_lossy
#print axioms Series6.WS4.ws4_residue_one_to_many
#print axioms Series6.WS4.ws4_arrow_strict
#print axioms Series6.WS4.ws4_no_return
#print axioms Series6.WS4.ws4_arrow_has_first_moment
#print axioms Series6.WS4.ws4_arrow_from_properness

-- WS5 — relativity: agreement-is-collapse, the laundering finding, the Ω-frame branch
#print axioms Series6.WS5.ws5_agree_iff_eq
#print axioms Series6.WS5.ws5_agreement_is_collapse
#print axioms Series6.WS5.ws5_plurality_forbids_agreement
#print axioms Series6.WS5.ws5_causal_partial_order
#print axioms Series6.WS5.ws5_incomparability_is_bare_poset
#print axioms Series6.WS5.ws5_omega_absolute_frame

-- WS6 — inherited incompleteness, groundlessness, no-view; the achievement Impossibility
#print axioms Series6.WS6.ws6_incompleteness_inherited
#print axioms Series6.WS6.ws6_groundlessness_from_diagonal
#print axioms Series6.WS6.ws6_no_view_from_nowhere
#print axioms Series6.WS6.ws6_atomless_and_plural_impossible
#print axioms Series6.WS6.ws6_plurality_costs_an_atom
#print axioms Series6.WS6.ws6_one_engine_obstructed

-- WS7 — the audit and the typed verdict
#print axioms Series6.WS7.ws7_one_incompletion
#print axioms Series6.WS7.ws7_payoffs_hold
#print axioms Series6.WS7.ws7_engine_not_painted_on
#print axioms Series6.WS7.ws7_distinctness_anchors
#print axioms Series6.WS7.ws7_strip_ledger
#print axioms Series6.WS7.ws7_c2_collapses
#print axioms Series6.WS7.ws7_verdict_eq
#print axioms Series6.WS7.ws7_not_trivialized
