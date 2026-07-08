/-
`series-3/formal/AxiomCheck.lean`

**In-build axiom verification for the whole Series-3 development (WS1–WS8).**

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
`Series3` lean_lib (see `lake/lakefile.toml`) so `lake build` compiles it.
-/
import Series3

/-! ### WS1 — Groundless carrier (terminal coalgebra of `P_κ`) -/
#print axioms Series3.WS1.exists_terminal_coalg
#print axioms Series3.WS1.ws1_C1
#print axioms Series3.WS1.ws1_C2

/-! ### WS2 — `νP_κ` and its bisimulation theory -/
#print axioms Series3.WS2.ws2_characterization

/-! ### WS3 — bidirectional constitution (no strict law + weak bialgebra) -/
#print axioms Series3.WS3.ws3_no_distributive_law
#print axioms Series3.WS3.ws3_weak_bialgebra

/-! ### WS4 — graded parthood over a good quantale (Łₙ) -/
#print axioms Series3.WS4.ws4_graded_coherence_Luk
#print axioms Series3.WS4.Luk.ws4_quantitative_witness

/-! ### WS5 — finite attention (incompleteness + plurality floor) -/
#print axioms Series3.WS5.ws5_incompleteness_and_floor

/-! ### WS6 — no poles, no outside -/
#print axioms Series3.WS6.ws6_split_and_no_maximal

/-! ### WS7 — non-collapse (the collector) -/
#print axioms Series3.WS7.ws7_band_and_retro
#print axioms Series3.WS7.ws7_attention_fixed_point

/-! ### WS8 — filling the holes (A–E) + Lemma B convergence + exp-fitness exploration -/
#print axioms Series3.WS8.wq_preserves_weak_pullback
#print axioms Series3.WS8.ws3_weak_law_canonical
#print axioms Series3.WS8.ws7_general_branching_false
#print axioms Series3.WS8.ws7_iv_branching
#print axioms Series3.WS8.ws6_no_global_observer
#print axioms Series3.WS8.ws6_substantive_standpoints
#print axioms Series3.WS8.ws8_replicator_converges
#print axioms Series3.WS8.exp_lip
#print axioms Series3.WS8.expR_coord_lipschitz
#print axioms Series3.WS8.ws8_exp_replicator_converges
#print axioms Series3.WS8.ws8_exp_replicator_converges_band
#print axioms Series3.WS8.ws8_noncollapse_partial_band

/-! ### WS9 — the convergence boundary (full stratification: false / conditional / true) -/
#print axioms Series3.WS9.ws9_multistable
#print axioms Series3.WS9.ws9_no_unique_attention
#print axioms Series3.WS9.ws9_no_contraction
#print axioms Series3.WS9.ws9_two_cycle
#print axioms Series3.WS9.ws9_nonexpansive_converges
#print axioms Series3.WS9.ws9_center_fixed_all
#print axioms Series3.WS9.ws9_multistable_interval
#print axioms Series3.WS9.ws9_bifurcation
#print axioms Series3.WS9.coordIndF_hasDerivAt_center

/-! ### WS10 — statement–gloss reconciliation (carrier-cardinality keystone + fallout) -/
#print axioms Series3.WS10.carrier_card_ge
#print axioms Series3.WS10.ws10_concrete_tuple
#print axioms Series3.WS10.ws10_bounded_self_model
#print axioms Series3.WS10.ws10_standpoint_proper
#print axioms Series3.WS10.ws10_carrier_attention_converges
