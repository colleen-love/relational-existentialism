# Blind seed — Phase F (code review), MONOTONE-ONLY rebuild

You are reviewing the Lean 4 sources of Series 2.7 against a fixed contract. You are BLIND to motivating prose.
Judge ONLY whether the CODE proves the claimed signatures and whether the verdict is HONESTLY earned (not a
costume). Do NOT read `charter.md`, `charter-status.md`, `charter-extension.md`, `measure-derisking.md`,
`spec/README.md`, `summary*.md`, or the narrative sections of `spec/ws*-design.md`.

Read ONLY: this file, and the built sources `program-2/series-7/formal/P2S7/ws1.lean`, `ws2.lean`, `ws3.lean`,
`ws4.lean`, `ws5.lean`, `AxiomCheck.lean`, `program-2/series-7/formal/P2S7.lean`. You MAY read
`program-2/formal/P1/Core.lean`, `Reader.lean` to confirm imported machinery.

## Context: this is a REBUILD after a prior verdict was rejected as a costume

The prior landing computed CONSERVED-RELATIVE. An independent review found that a COSTUME: its "in-sight
conservation" (`ws2_tick_conserves`) proved only that the tick's product is plain-bisimilar to its constituent —
the COLLAPSE ENGINE, which holds for ANY measure because in-sight the atomless carrier is one bisimulation class —
NOT a `Q`-specific invariance. And its free-lunch fork was decided by a `Finset.card` counter (`insert 0 ∅` grows,
`insert 0 {0}` doesn't) disconnected from the diagonal. The rebuild claims the HONEST verdict MONOTONE-ONLY: the
measure rises and nothing is conserved. YOUR JOB is to check the rebuild is genuine and did not smuggle in a new
costume.

## 1. Imported machinery (given, built, axiom-clean)

```
Recoverable destL ; ws1_atomless_bisim (collapse engine) ; ws4_recoverable_not_import (Series 07)
rankLift dest rank ; AttentionDistinguishes destL x y := (plain-bisim) ∧ ¬(label-bisim)
outDest hinf attends ; Hold dest ; residue insp ; ResidueRecoverable insp
ws2_residue_free dest insp : ¬ ResidueRecoverable insp     -- the residue is free, for EVERY inspection
```

## 2. What the code must prove (check each theorem body establishes its stated type)

```
-- WS1: rankM is a non-trivial measure whose differences are genuine imports
theorem ws1_rank_nontrivial (hinf) :
    rankM e1 ≠ rankM e0 ∧ AttentionDistinguishes (destML hinf) e1 e0 ∧ (∃ x y, rankM x ≠ rankM y)
-- WS2: the tick RAISES the measure (the arrow), Q-specifically
theorem ws2_tick_raises (hinf) :
    rankM (reifyM {e0}) = rankM e0 + 1 ∧ rankM (reifyM {e1}) = rankM e1 + 1
  ∧ AttentionDistinguishes (destML hinf) (reifyM {e0}) e0
-- WS3: the measure is NOT conserved; every change is a genuine import
theorem ws3_not_conserved (hinf) :
    ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (∀ f : MCar → ℕ, (∀ x y, (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R x y) → f x = f y) → f e1 = f e0)
theorem ws3_change_is_source (hinf) :
    (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y) ∧ ¬ Recoverable (destML hinf)
-- WS4: the rise is internal creation; conservation-from-within is IMPOSSIBLE (the crux settled by proof)
theorem ws4_rise_is_internal (hinf) :
    (∀ insp, ¬ ResidueRecoverable insp) ∧ AttentionDistinguishes (destML hinf) e1 e0
theorem ws4_no_lossless_tick (hinf) : rankM (reifyM {e0}) ≠ rankM e0
theorem ws4_conservation_impossible (hinf) :
    (rankM (reifyM {e0}) ≠ rankM e0) ∧ (∀ insp, ¬ ResidueRecoverable insp)
-- WS5: verdict computes monotoneOnly, discriminating; flags earned; audits
theorem ws5_verdict_eq : verdict true false true true false false = Outcome.monotoneOnly
theorem ws5_verdict_discriminates : (reaches all six Outcome constructors)
theorem ws5_flags_justified (hinf) : (WS1 nonTrivial ∧ WS2 arrow ∧ WS3 not-conserved ∧ WS4 internal)
theorem ws5_audit_not_conserved (hinf) :
    ((∃ R, IsBisim (plainOf (destML hinf)) R ∧ R e1 e0) ∧ rankM e1 ≠ rankM e0)
  ∧ (∀ f : MCar → ℕ, (plain-invariant f) → f e1 = f e0)
  ∧ (verdict true false true true false false = Outcome.monotoneOnly)
theorem ws5_audit_conservation_impossible (hinf) :
    (rankM (reifyM {e0}) ≠ rankM e0) ∧ (∀ insp, ¬ ResidueRecoverable insp)
  ∧ (verdict true false true true false false = Outcome.monotoneOnly)
theorem ws5_audit_no_global (hinf) : (not even local conservation) ∧ (verdict … true true = Outcome.global)
theorem ws5_audit_arrow_genuine (hinf) : (rankM e1 ≠ rankM e0) ∧ (rankM (reifyM {e0}) = rankM e0 + 1) ∧ (not conserved)
theorem ws5_audit_source_is_diagonal (hinf) : (∀ insp, ¬ ResidueRecoverable insp) ∧ AttentionDistinguishes (destML hinf) e1 e0
theorem ws5_audit_change_is_source (hinf) : (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes …) ∧ ¬ Recoverable (destML hinf)
theorem ws5_audit_names_not_terms : True
```

## 3. The checks (the honesty bar — this is the point of the review)

- **Verdict is monotoneOnly, computed.** `ws5_verdict_eq` must be `verdict true false … = Outcome.monotoneOnly` by
  `rfl`, i.e. the SECOND flag (`inSightConserved`) is FALSE. Confirm the function returns `monotoneOnly` when
  `inSightConserved = false`. SERIOUS if the verdict is hand-set or does not compute.
- **`inSightConserved = false` is EARNED, not hand-set.** `ws3_not_conserved` / `ws5_audit_not_conserved` must prove
  a genuine DISPROOF of conservation: a plain-bisimilar pair `e1 ~ e0` with `rankM e1 ≠ rankM e0` (so `rankM` is not
  plain-invariant), AND that any plain-invariant `f` agrees on `e1`,`e0` (so conserved measures are trivial on the
  tick pair). Confirm the proof establishes this. SERIOUS if `inSightConserved`'s falsity is asserted without proof.
- **The arrow is Q-specific (not the collapse).** `ws2_tick_raises` must prove `rankM (reifyM {e0}) = rankM e0 + 1`
  — a fact about `rankM` RISING, not "the two states are bisimilar". Confirm it is a genuine `rankM` increase.
- **No costume conservation.** Confirm NO theorem proves a `rankM`-conservation (`rankM (reifyM s) = rankM
  constituent`) and calls it in-sight conservation. The rebuild should prove the OPPOSITE (rankM rises). SERIOUS if a
  collapse-based "conservation" is present and feeds a conserved verdict.
- **The impossibility is genuine.** `ws4_conservation_impossible` should combine (rankM rises) with (the residue is
  always free, `ws2_residue_free`) — a real proof that the diagonal always creates, so no conserved side. Confirm it
  is `ws2_residue_free` (the diagonal) plus the rise, not a `Finset.card` counter. Confirm there is NO `Qc`/`diagStep`
  counter anywhere deciding the verdict.
- **change-is-import via Series 07.** `ws3_change_is_source`'s `¬ Recoverable` routes through `ws4_recoverable_not_import`.
- **names-not-terms.** No identifier/parameter embeds a whole word from {energy, conservation, information, measure,
  creation, self, import, god, choice, subjectivity}. (Docstring prose and `import` keyword exempt.)
- **axioms.** `AxiomCheck` shows only propext / Classical.choice / Quot.sound (or fewer).

You may run `cd /home/user/relational-existentialism/lake && lake build P2S7 P2S7.AxiomCheck` and grep. Do NOT modify files.

## 4. Grading

- **SERIOUS:** a theorem does not prove its type; a `sorry`/`axiom`; the verdict is hand-set or a new costume (a
  collapse-based conservation feeding a conserved verdict; a counter deciding the verdict); `inSightConserved=false`
  unproven; a forbidden identifier; a non-standard axiom; an undisclosed narrowing.
- **REAL:** a genuine gap correctly labelled once fixed.
- **COSMETIC/ACCEPTABLE:** a nominal overclaim, over-hypothesis (e.g. an unused `hinf`), naming nit, disclosed placeholder.

Return findings with stable IDs (`Fn-Sm`), grade, location, defect. If nothing is SERIOUS, say so explicitly. The
central question: **is MONOTONE-ONLY honestly earned, or is there a new costume?**
