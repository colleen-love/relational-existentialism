# WS1 design — Strict identity fails across a tick (the ground) (2.6)

**Prove that STRICT relational identity fails across a tick: the reified successor moment is plain-bisimilar to
its constituent (the collapse engine makes every atomless pair plain-bisimilar) yet NOT bisimilar over the rank
lift that fixes strict identity, because the reified successor outranks its constituent. This is the trivial
ground (charter §2, §4.a): a true fact about relational identity that is a COSTUME, not the finding. The series
earns its keep on the WEAK continuity (WS2) and the linearization import (WS3). WS1 also fixes the tick-successor
relation, the candidate carrier of the weak continuity.**

## 1. Candidate constructions

1. **Assert "the self changes, so it is a new relatum" as the headline.** REJECTED: the costume (charter §4.a).
   That is the trivial fact; if it carries the verdict with no weak-continuity and no linearization content, the
   series is a costume. Here it is explicitly labelled the trivial GROUND, and the verdict (WS5) does NOT rest on
   it (it rests on WS2/WS3).
2. **Strict identity = plain non-bisimilarity.** REJECTED: on the atomless tick carrier the collapse engine
   (`ws1_atomless_bisim`) makes EVERY pair plain-bisimilar, so plain non-bisimilarity is unsatisfiable here.
   Strict identity must live at the LABELLED (rank) level.
3. **Strict identity = label-bisimilarity of the rank lift; its failure across a tick via `ws2_many_general`
   (CHOSEN).** The reified successor `kC` (rank 2) and its constituent `kA` (rank 1) are plain-bisimilar (the
   collapse engine) yet NOT bisimilar over `rankLift (outDest attendsT) rankT` (the reified relatum outranks its
   constituent, the `ws2_many_general` / `firstOther_label_sep` mechanism): exactly `AttentionDistinguishes`.
   Strict identity fails across the tick; the pair stays plain-alike. This is the honest reading of "strict
   identity" consistent with the imported machinery, and it is trivial by design.

## 2. Triage

- **The costume, made explicit (audit c).** WS1 is the COSTUME of relational identity, named as such. Its payoff
  `ws1_strict_fails` is `AttentionDistinguishes …` (strict fails, plain holds). The verdict does not rest on it:
  `verdict` returns a decided outcome only with the WS3 line-import flag and the WS2/WS4 weak-continuity flags
  (WS5 §3). Strip WS1 alone and nothing is decided.
- **Strip test.** `ws1_strict_fails` → "a reified relatum is plain-bisimilar to its constituent yet separated by
  the rank lift"; `ws1_succ_witnessed` → "a reification-dependency edge exists." Bare `AttentionDistinguishes` /
  membership facts, no interpretation load-bearing.
- **Names-not-terms (audit e).** `succDep`, `ws1_strict_fails`, `ws1_succ_witnessed` embed no forbidden
  content-word as a whole word.

## 3. Winning construction — typed signatures

```
-- The tick-successor relation: u consumes the produced moment t (both produced), reusing P2S1's `causal`.
@[reducible] def succDep (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u

-- The tick-successor is witnessed (a produced moment consumed by the next): the reification-dependency edges.
theorem ws1_succ_witnessed : succDep kA kC ∧ succDep kB kC

-- STRICT IDENTITY FAILS ACROSS A TICK (the trivial ground). The reified successor kC and its constituent kA are
-- plain-bisimilar (the collapse engine) yet NOT bisimilar over the rank lift (kC outranks kA): AttentionDistinguishes.
theorem ws1_strict_fails {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA
```

`AttentionDistinguishes destL x y` unfolds to `(∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL
R ∧ R x y)`. The first conjunct is `ws1_atomless_bisim` after `plainOf_rankLiftT` (both `SHNE` via
`ws1_tcar_SHNE`); the second is the rank-separation (mirrors `P2S1.ws4_linearization_import`'s separation arm,
reading the edge `kA ∈ attendsT kC` whose source label is `rankT kC = 2` against `kA`'s edges labelled
`rankT kA = 1`).

## 4. Why it is the ground, not the finding

Strict identity failing is FORCED the moment relational identity is forged and the tick reifies: the successor
carries a strictly higher tower rank than its constituent, so no rank-bisimulation relates them. This is
near-certain and interpretively empty on its own ("you are not exactly who you were"). The series' content is
whether a COARSER continuity survives the tick recoverably (WS2) and whether the single line of moments is an
import (WS3). WS1 is written to be trivial, labelled the costume, and walled out of the verdict.

## 5. Outcome classes

WS1 has no fork of its own; it is the near-certain ground. If, implausibly, the reified successor were bisimilar
to its constituent over the rank lift (strict identity did NOT fail), the whole series would be degenerate
(`partial'`), reported as such. That does not obtain: rank strictly rises across the tick.

## 6. Strip annotation

- `ws1_strict_fails` → "a reified relatum is plain-bisimilar to a constituent but rank-lift-separated."
- `ws1_succ_witnessed` → "a reification-dependency edge holds on the finite carrier."
