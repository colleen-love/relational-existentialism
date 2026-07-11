/-
`series-03/formal/AxiomCheck.lean`

**In-build axiom verification for the whole Series-03 development (WS1–WS8).**

This file imports the entire development and runs `#print axioms` on one
representative top-level deliverable from each workstream. Building it emits, for
every listed theorem, the line

  `… depends on axioms: [propext, Classical.choice, Quot.sound]`

i.e. **no custom axioms** beyond Mathlib's standard three (`propext`,
`Classical.choice`, `Quot.sound`) — and the whole build is `sorry`-free (a `sorry`
would surface here as `sorryAx`). The `Łₙ` quantitative witness is even
choice-free (`[propext, Quot.sound]`).

This is a build-time record that the formalization "works": every workstream's
headline result rests only on the sanctioned axiom base. It is a root of the
`Series03` lean_lib (see `lake/lakefile.toml`) so `lake build` compiles it.
-/
import Series03

/-! ### WS1 — Groundless carrier (terminal coalgebra of `P_κ`) -/
#print axioms Series03.WS1.exists_terminal_coalg
#print axioms Series03.WS1.ws1_C1
#print axioms Series03.WS1.ws1_C2

/-! ### WS2 — `νP_κ` and its bisimulation theory -/
#print axioms Series03.WS2.ws2_characterization

/-! ### WS3 — bidirectional constitution (no strict law + weak bialgebra) -/
#print axioms Series03.WS3.ws3_no_distributive_law
#print axioms Series03.WS3.ws3_weak_bialgebra

/-! ### WS4 — graded parthood over a good quantale (Łₙ) -/
#print axioms Series03.WS4.ws4_graded_coherence_Luk
#print axioms Series03.WS4.Luk.ws4_quantitative_witness

/-! ### WS5 — finite attention (incompleteness + plurality floor) -/
#print axioms Series03.WS5.ws5_incompleteness_and_floor

/-! ### WS6 — no poles, no outside -/
#print axioms Series03.WS6.ws6_split_and_no_maximal

/-! ### WS7 — non-collapse (the collector) -/
#print axioms Series03.WS7.ws7_band_and_retro
#print axioms Series03.WS7.ws7_attention_fixed_point

/-! ### WS8 — filling the holes (A–E) + Lemma B convergence + exp-fitness exploration -/
#print axioms Series03.WS8.wq_preserves_weak_pullback
#print axioms Series03.WS8.ws3_weak_law_canonical
#print axioms Series03.WS8.ws7_general_branching_false
#print axioms Series03.WS8.ws7_iv_branching
#print axioms Series03.WS8.ws6_no_global_observer
#print axioms Series03.WS8.ws6_substantive_standpoints
#print axioms Series03.WS8.ws8_replicator_converges
#print axioms Series03.WS8.exp_lip
#print axioms Series03.WS8.expR_coord_lipschitz
#print axioms Series03.WS8.ws8_exp_replicator_converges
#print axioms Series03.WS8.ws8_exp_replicator_converges_band
#print axioms Series03.WS8.ws8_noncollapse_partial_band

/-! ### WS9 — the convergence boundary (full stratification: false / conditional / true) -/
#print axioms Series03.WS9.ws9_multistable
#print axioms Series03.WS9.ws9_no_unique_attention
#print axioms Series03.WS9.ws9_no_contraction
#print axioms Series03.WS9.ws9_two_cycle
#print axioms Series03.WS9.ws9_nonexpansive_converges
#print axioms Series03.WS9.ws9_center_fixed_all
#print axioms Series03.WS9.ws9_multistable_interval
#print axioms Series03.WS9.ws9_bifurcation
#print axioms Series03.WS9.coordIndF_hasDerivAt_center

/-! ### WS10 — statement–gloss reconciliation (carrier-cardinality keystone + fallout) -/
#print axioms Series03.WS10.carrier_card_ge
#print axioms Series03.WS10.ws10_concrete_tuple
#print axioms Series03.WS10.ws10_bounded_self_model
#print axioms Series03.WS10.ws10_standpoint_proper
#print axioms Series03.WS10.ws10_carrier_attention_converges
#print axioms Series03.WS10.ws10_unlabeled_atomless_collapses
#print axioms Series03.WS10.ws10_grounded_core_subsingleton
#print axioms Series03.WS10.ws10_center_globally_attracting
#print axioms Series03.WS10.ws10_center_unique_above

/-! ### WS11 — the identity split (extensional ⇒ downward; the upward witness) -/
#print axioms Series03.WS11.ws11_identity_split
#print axioms Series03.WS11.ws11_no_upward_identity
#print axioms Series03.WS11.ws11_upward_witness
#print axioms Series03.WS11.ws11_terminal_identifies

/-! ### WS12 — hereditary non-domination (the `2^ℵ₀` spine keystone) -/
#print axioms Series03.WS12.ws12_hereditary_scope
#print axioms Series03.WS12.ws12_reachable_card_le
#print axioms Series03.WS12.ws12_carrier_card_continuum
#print axioms Series03.WS12.ws12_carrier_card_gt
#print axioms Series03.WS12.ws12_no_hereditary_maximal
#print axioms Series03.WS12.ws12_no_hereditary_observer

/-! ### WS13 — pairs and relations as states -/
#print axioms Series03.WS13.ws13_reification
#print axioms Series03.WS13.ws13_pair_inj
#print axioms Series03.WS13.ws13_reify_inj
#print axioms Series03.WS13.ws13_reify_mem

/-! ### WS14 — the graded carrier defeats the collapse -/
#print axioms Series03.WS14.ws14_graded_core
#print axioms Series03.WS14.ws14_loop_ne
#print axioms Series03.WS14.ws14_loops_not_bisim
#print axioms Series03.WS14.ws14_wq_card_ge
#print axioms Series03.WS14.ws14_graded_core_Luk

/-! ### WS15 — constitutive attention (self-model + exact coordination count) -/
#print axioms Series03.WS15.ws15_constitutive_attention
#print axioms Series03.WS15.ws15_selfModel_eq_iff
#print axioms Series03.WS15.ws15_selfModel_view_proper
#print axioms Series03.WS15.ws15_multistable_iff
#print axioms Series03.WS15.ws15_multistable_below_half
#print axioms Series03.WS15.ws15_orbit_floor
