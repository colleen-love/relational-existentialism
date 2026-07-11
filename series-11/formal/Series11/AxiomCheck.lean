/-
`series-11/formal/Series11/AxiomCheck.lean`

The axiom pass over the whole Series 11 build. Each `#print axioms` confirms the headline reduces to
Mathlib's standard three (`propext` / `Classical.choice` / `Quot.sound`) — no `sorry`, no custom axiom.

The two most important records (protocol §D), honestly stated after the Phase E re-grade (S1):
- `#print axioms Series11.WS1.ws1_attention_makes_real` reduces to the standard three — but the term IS
  `ws4_free_label_is_import`, a fact about the FIXED `labelLoop` coalgebra (`reify`/`reifyStep`/`towerN`
  absent). The distinction is on `labelLoop`, NOT the reification tower, so the spine is Series 10's
  Bookkeeping RE-HIT; the WS7 verdict is `bookkeepingReHit` (`ws7_verdict_eq`), the honest negative.
- `#print axioms Series11.WS3.ws3_no_total_attention` reduces to `propext` alone — the diagonal uses no
  choice and no cardinal, so the bound is holding-not-size, κ-free (the κ-readmitted check PASSES; the one
  half Series 11 delivers cleanly).
-/
import Series11

-- WS1 — finite attention, the κ-removal, and the attention-reality spine (the reader Series 10 lacked)
#print axioms Series11.WS1.ws1_attention_makes_real
#print axioms Series11.WS1.ws1_attention_distinction_free
#print axioms Series11.WS1.ws1_attention_not_plain_quotient
#print axioms Series11.WS1.ws1_attention_routes_through_diagonal
#print axioms Series11.WS1.ws1_kappa_free_recheck
#print axioms Series11.WS1.ws1_attention_is_finite_hold
#print axioms Series11.WS1.ws1_no_self_total_hold
#print axioms Series11.WS1.ws4_free_label_is_import
#print axioms Series11.WS1.ws4_labelLoop_not_recoverable

-- WS2 — reification rescued from Bookkeeping (the rescue at the attended level, on a witness)
#print axioms Series11.WS2.ws2_bookkeeping_transcribed
#print axioms Series11.WS2.ws2_attention_embed_fails
#print axioms Series11.WS2.ws2_rescue_where_bisim_collapses
#print axioms Series11.WS2.ws2_reified_real_for_attention
#print axioms Series11.WS2.ws2_plain_collapse_persists

-- WS3 — no total attention (the diagonal at tower scale, an Impossibility, κ-free)
#print axioms Series11.WS3.ws3_no_total_attention
#print axioms Series11.WS3.ws3_no_total_attention_kappa_free
#print axioms Series11.WS3.ws3_attention_reads_full_relata
#print axioms Series11.WS3.ws3_bounded_holding_endogenous
#print axioms Series11.WS3.ws3_unbounded_yet_unassembled

-- WS4 — the endogenous bound, κ removed (holding-not-size, finite stages)
#print axioms Series11.WS4.ws4_no_completed_totality
#print axioms Series11.WS4.ws4_bound_is_holding_not_size
#print axioms Series11.WS4.ws4_no_russell_blowup
#print axioms Series11.WS4.ws4_kappa_free
#print axioms Series11.WS4.ws4_bound_finite_stages

-- WS5 — the crown-vs-tragic fork (Partial: finite Discharged, transfinite/carrier-κ open)
#print axioms Series11.WS5.ws5_crown_on_finite_stages
#print axioms Series11.WS5.ws5_kill_condition_shape
#print axioms Series11.WS5.ws5_crown_verdict_justified

-- WS6 — the heuristic ceiling and the program's close
#print axioms Series11.WS6.ws6_provable_core
#print axioms Series11.WS6.ws6_unification

-- WS7 — the audit, the promoted checks, and the typed verdict (RE-GRADED: bookkeepingReHit, S1)
#print axioms Series11.WS7.ws7_audit
#print axioms Series11.WS7.ws7_verdict
#print axioms Series11.WS7.ws7_verdict_eq
#print axioms Series11.WS7.ws7_tower_collapses
#print axioms Series11.WS7.ws7_audited_is_bookkeepingReHit
#print axioms Series11.WS7.ws7_audited_not_attentionEstablished
#print axioms Series11.WS7.ws7_audited_not_kappaReadmitted
#print axioms Series11.WS7.ws7_audited_not_tragic
#print axioms Series11.WS7.ws7_bookkeeping_rehit_check
#print axioms Series11.WS7.ws7_kappa_readmitted_check
#print axioms Series11.WS7.ws7_no_bookkeeping_rehit
#print axioms Series11.WS7.ws7_not_import
#print axioms Series11.WS7.ws7_strip_ledger
