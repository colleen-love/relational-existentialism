/-
`series-11/formal/Series11.lean`

Series 11 — **Finite attention is the reader and the bound.** The aggregator root. The program's terminal
series, and the response to Series 10's proved Bookkeeping.

Series 10 built the reification tower and proved it BOOKKEEPING at the plain level: a reified relatum
`reify s` is bisimilar to every prior `SHNE` relatum (via `ws1_atomless_bisim`, the Series 07 engine), so
`Ω_{α+1}` bisim-embeds into `Ω_α` and the plain quotient sees no growth, even though `reify` genuinely
carries its pattern (`IsReify`). The diagnosis: the many lives at the labelled level, but nothing READS the
label. Series 11's answer: finite attention is the reader (rescuing Bookkeeping) and the bound (replacing
the scaffold κ), because the same incompletability that generates the many (the diagonal) prevents any hold
from grasping the whole (no-total-attention at tower scale).

**Verdict: `attentionEstablished` on the mechanized core; the spine Discharged-on-witness / universal
Partial; the crown Partial.**

- The spine (WS1) is **attention-reality, Discharged on a witness** (`ws1_attention_makes_real =
  ws4_free_label_is_import`): a finite attention distinguishes the reified relatum WHERE THE PLAIN
  BISIMULATION COLLAPSES (`plainOf`-bisimilar but not label-bisimilar), and the distinction is FREE
  (`ws1_attention_distinction_free = ws4_labelLoop_not_recoverable`, not recoverable). This is the reader
  Series 10 lacked — the free label, now READ, by something the plain quotient is not
  (`ws1_attention_not_plain_quotient`). The witness is the FIXED `labelLoop` coalgebra; the tower-level tie
  (`reifyStep`) and the universal are Partial, Bookkeeping-re-hit the pre-registered live negative. The
  label-is-the-residue routing (`ws1_attention_routes_through_diagonal`) is interpretive at the residue-
  freeness level, flagged not hidden (as Series 10 disclosed for `ws1_free_reification`).
- The payoff (WS2) is **the rescue at the attended level, Discharged on a witness**
  (`ws2_attention_embed_fails`): the reified relatum bisim-embeds at the plain level
  (`ws2_bookkeeping_transcribed`, Series 10's Bookkeeping, unappealed) but does NOT attention-embed
  (`ws2_rescue_where_bisim_collapses`, for the SAME pair). The plain collapse PERSISTS
  (`ws2_plain_collapse_persists`) — the rescue is a new reader, not a new plain fact.
- No-total-attention (WS3) is **`ws3_no_total_attention = ws1_no_self_total_hold`, an Impossibility**, the
  bound's engine, and **κ-free** (`ws3_no_total_attention_kappa_free`, the proof uses no cardinal — the
  genuine κ-removal). (NL) holds (`ws3_attention_reads_full_relata`), bounded-holding is endogenous
  finitude (`ws3_bounded_holding_endogenous`, on a possibly-infinite tower — holding, not size).
- The bound (WS4) is **holding-not-size, Discharged on finite stages**: no completed totality
  (`ws4_no_completed_totality`), no Russell blowup (`ws4_no_russell_blowup`), κ-free (`ws4_kappa_free`).
  The residual carrier branching-κ is disclosed as the section's existence condition (§2.7), not a bound.
- The crown (WS5) is **Partial** (`ws5_crown_verdict = .partialV`): Discharged on finite stages
  (`ws5_crown_on_finite_stages`), the transfinite limit and carrier-κ open, the TRAGIC horn pre-registered
  and live via a three-horn kill condition (`ws5_kill_condition_shape`).
- The ceiling (WS6): the universals are theses floored by the core (`ws6_provable_core`,
  `ws6_universal_theses`); the unification is a theorem-and-thesis (`ws6_unification`).
- The verdict (WS7) is **`attentionEstablished`** (`ws7_verdict`), a function of a discharged `Audit` whose
  flagship fields carry the two promoted checks (Bookkeeping-re-hit, κ-readmitted), never hand-set.

This file is SELF-CONTAINED: every Series 10/09/08/07/04 lemma is transcribed into `Series11/wsNN.lean` and
re-namespaced `Series11.WSn` — nothing is imported from `series-10/`, `series-09/`, `series-08/`,
`series-07/`, `series-04/`, or `archive/`. `Series11.AxiomCheck` runs `#print axioms` over every headline.
Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series11.ws1
import Series11.ws2
import Series11.ws3
import Series11.ws4
import Series11.ws5
import Series11.ws6
import Series11.ws7
