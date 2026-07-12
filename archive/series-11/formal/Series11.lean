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

**Verdict (after Phase E / series-review-1): `bookkeepingReHit` on the reality axis; κ-removal Discharged
on the bound axis.** Series 11 set out to do two things with one mechanism — make Series 10's reified label
REAL by supplying a reader (rescue Bookkeeping), and BOUND the tower by the finitude of that reader (remove
κ). It delivered the second and re-hit Bookkeeping on the first. Reported honestly, this is the pre-registered
terminus (charter §5.5, §7, §8 criterion 1), the direct analogue of Series 10's honest close.

- The spine (WS1) is **BOOKKEEPING RE-HIT** (`ws1_attention_makes_real = ws4_free_label_is_import`): a fact
  about the FIXED `labelLoop` coalgebra (`⟨true⟩` vs `⟨false⟩`), with `reify`/`reifyStep`/`towerN` absent from
  every attention theorem. "Attention" is Series 10's free label relabelled; the distinction is drawn on two
  fixed Booleans, not on the tower's reified relata (which bisim-embed, `ws7_tower_collapses`). The freeness
  (`ws1_attention_distinction_free`) and residue-routing (`ws1_attention_routes_through_diagonal`) are genuine
  but about objects different from the tower, so they do not earn the rescue. The Phase C "Discharged-on-witness
  / universal Partial" framing was the §0.2a-forbidden third theorem and is retracted.
- The payoff (WS2) is **the same `labelLoop` fact** (`ws2_attention_embed_fails` etc.), with the
  `FiniteAttention` argument discarded in `ws2_reified_real_for_attention`. The specified target (`Ω_{α+1}`
  does not ATTENTION-embed into `Ω_α`) is NOT built; the tower collapses (`ws2_bookkeeping_transcribed` =
  Series 10's `ws2_reify_bisim_embeds`), and the plain collapse persists (`ws2_plain_collapse_persists`).
- No-total-attention (WS3) is **`ws3_no_total_attention = ws1_no_self_total_hold`, an Impossibility, κ-free**
  — an INSPECTION-LEVEL diagonal (`insp` a free parameter; the "tower scale" reading interpretive, R1). (NL)
  holds (`ws3_attention_reads_full_relata`, the one place `reify` does real work); bounded-holding is
  endogenous finitude on a possibly-infinite carrier (holding, not size).
- The bound (WS4) is **holding-not-size, κ genuinely removed** (`ws4_no_completed_totality`,
  `ws4_no_russell_blowup`, `ws4_kappa_free`) — the inspection-level diagonal, tower-independent (R1). The
  κ-readmitted check PASSES; the residual carrier branching-κ is disclosed, not used as a bound. **This is the
  half of the charter's ambition Series 11 delivers cleanly.**
- The crown (WS5) is **Partial, floored on the genuine bound** (`ws5_crown_verdict = .partialV`): the κ-free
  diagonal (NT/EB) is genuine; the attention-READER is Bookkeeping re-hit; so self-bounding VIA ATTENTION is
  not established. `ws5_kill_condition_shape` is a pre-registration marker (`⟨id, id⟩`), not a run.
- The ceiling (WS6): the universals are theses floored by the core; the "unification" (`ws6_unification`) is
  a bare projection, so Consequence 3 is a DEFENDED THESIS, not a theorem (R2).
- The verdict (WS7) is **`bookkeepingReHit`** (`ws7_verdict`), a function of a discharged `Audit`, never
  hand-set; `ws7_audited_not_attentionEstablished` proves the success verdict is NOT returned, and
  `ws7_tower_collapses` proves the Bookkeeping antecedent. The verdict machinery is sound; it now carries the
  honest label. The κ-removal, (NL), and the diagonal stand on their own.

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
