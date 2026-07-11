/-
`series-10/formal/Series10/AxiomCheck.lean`

The axiom pass over the whole Series 10 build. Each `#print axioms` confirms the headline reduces to
Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`) — no `sorry`, no custom axiom.

The two most important records (protocol §C):
- `#print axioms Series10.WS1.ws1_free_reification` reduces to the standard three, and its proof term
  routes through `ws1_no_self_total_hold` (freeness is the diagonal, not a fresh assumption — but of the
  residue content, `reify` absent, R1).
- `#print axioms Series10.WS2.ws2_reify_bisim_embeds` reduces to the standard three, and it proves the
  reified `SHNE` relatum bisim-embeds (growth is BOOKKEEPING, the moving-hole re-hit, S1).
-/
import Series10

-- WS1 — the reifying carrier and productive blindness (the spine; R1: residue-freeness, reify absent)
#print axioms Series10.WS1.ws1_reify_injective
#print axioms Series10.WS1.ws1_free_reification
#print axioms Series10.WS1.ws1_close_forbidden_local
#print axioms Series10.WS1.ws1_diagonal_forbids_closure
#print axioms Series10.WS1.ws1_reification_is_free_label
#print axioms Series10.WS1.ws1_no_self_total_hold
#print axioms Series10.WS1.ws2_residue_is_import

-- WS2 — the payoff, RELABELLED BOOKKEEPING (S1): the tower bisim-embeds (moving-hole re-hit)
#print axioms Series10.WS2.ws2_growth_is_bookkeeping
#print axioms Series10.WS2.ws2_reify_bisim_embeds
#print axioms Series10.WS2.ws2_free_label_survives
#print axioms Series10.WS2.ws2_label_free_import
#print axioms Series10.WS2.ws2_plain_collapse_persists

-- WS3 — the reification tower and its order (the seed)
#print axioms Series10.WS3.ws3_reify_preserves_SHNE
#print axioms Series10.WS3.ws3_tower_monotone
#print axioms Series10.WS3.ws3_order_endogenous
#print axioms Series10.WS3.ws3_imported_order_refuted
#print axioms Series10.WS3.ws3_tower_monotone_family

-- WS4 — close-or-fold: the dichotomy and CLOSE-forbidden (the structural heart)
#print axioms Series10.WS4.ws4_close_forbidden
#print axioms Series10.WS4.ws4_dichotomy
#print axioms Series10.WS4.ws4_diagonal_forbids_closure
#print axioms Series10.WS4.ws4_fold_is_reflexivity
#print axioms Series10.WS4.ws4_close_forbidden_not_fold

-- WS5 — the fold-or-fatal fork (Partial: Discharged-on-scaffold per-step, universal/κ-removal open)
#print axioms Series10.WS5.ws5_step_fold
#print axioms Series10.WS5.ws5_fold_on_scaffold
#print axioms Series10.WS5.ws5_fold_not_cardinality
#print axioms Series10.WS5.ws5_verdict_justified

-- WS6 — the heuristic ceiling and the Series 11 handoff
#print axioms Series10.WS6.ws6_provable_core
#print axioms Series10.WS6.ws6_fold_scope
#print axioms Series10.WS6.ws6_series11_handoff

-- WS7 — the audit, the promoted checks, and the typed verdict (RE-GRADED: bookkeeping, S1)
#print axioms Series10.WS7.ws7_audit
#print axioms Series10.WS7.ws7_verdict
#print axioms Series10.WS7.ws7_verdict_eq
#print axioms Series10.WS7.ws7_audited_is_bookkeeping
#print axioms Series10.WS7.ws7_audited_not_reificationEstablished
#print axioms Series10.WS7.ws7_bookkeeping_check
#print axioms Series10.WS7.ws7_kappa_discipline
#print axioms Series10.WS7.ws7_close_forbidden_inspection_level
#print axioms Series10.WS7.ws7_spine_is_residue_freeness
#print axioms Series10.WS7.ws7_strip_ledger
