# Blind seed — Phase F (code review)

You are reviewing the Lean 4 sources of Series 2.7 against a fixed contract. You are BLIND to any motivating prose.
Judge ONLY whether the CODE proves the claimed signatures, survives the strip test, and passes the audit and
names checks below. Do NOT read `charter.md`, `charter-status.md`, `charter-extension.md`, `measure-derisking.md`,
`spec/README.md`, any `summary*.md`, or the narrative sections (1/2/4) of the `spec/ws*-design.md` files.

Read ONLY: this file, and the built sources
`program-2/series-7/formal/P2S7/ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean`, `AxiomCheck.lean`, and
`program-2/series-7/formal/P2S7.lean`. You MAY read the foundation `program-2/formal/P1/Core.lean`, `Reader.lean`
to confirm the imported machinery (given, not under review). Docstrings/comments in the sources are prose — you may
read them to locate code, but judge the THEOREM STATEMENTS and PROOFS, not the prose claims.

## 1. The imported machinery (given, already built and axiom-clean)

```
Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R
ws1_atomless_bisim dest x y (SHNE x) (SHNE y) : ∃ R, IsBisim dest R ∧ R x y      -- collapse engine
ws4_recoverable_not_import destL (Recoverable destL) x y (∃ R, IsBisim (plainOf destL) R ∧ R x y)
    : ∃ R, IsBisimL destL R ∧ R x y
rankLift dest (rank : X → ℕ) : X → LkObj κ (ULift ℕ) X ; AttentionDistinguishes destL x y := (plain-bisim) ∧ ¬(label-bisim)
outDest hinf (attends : X → Finset X) : X → PkObj κ X
residue insp := diag insp := fun h => ¬ insp h h ; ResidueRecoverable insp := ∃ h, insp h = residue insp
ws2_residue_free dest insp : ¬ ResidueRecoverable insp
ws1_coincidence_not_identity_witness dest (h₀ : Hold dest) :
    ∃ insp₁ insp₂, ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂
```

## 2. What the code must prove (the contract; check each theorem body actually establishes its statement)

```
-- WS1 (ws1.lean): the measure rankM is non-trivial, the difference a genuine import
theorem ws1_rank_nontrivial (hinf) :
    rankM e1 ≠ rankM e0 ∧ AttentionDistinguishes (destML hinf) e1 e0 ∧ (∃ x y : MCar, rankM x ≠ rankM y)
theorem rankM_sep_general (dest) (lab) (x y) (lab x ≠ lab y) ((dest x).1 ≠ ∅) : ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y

-- WS2 (ws2.lean): the tick conserves the measure in-sight (product plain-bisimilar to constituent)
theorem ws2_tick_conserves (hinf) :
    attendsM (reifyM {e0}) = {e0} ∧ reifyM {e0} = e1 ∧ (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)

-- WS3 (ws3.lean): every change in the measure is an import (Series 07), the source non-vacuous
theorem ws3_change_is_source (hinf) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y) ∧ ¬ Recoverable (destML hinf)
theorem ws3_source_nonvacuous (hinf) : AttentionDistinguishes (destML hinf) e1 e0 ∧ rankM e1 ≠ rankM e0

-- WS4 (ws4.lean): the free-lunch fork, both reachable, on the diagonal
theorem ws4_free_lunch_reachable (hinf) :
    (∃ insp₁ insp₂, ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂)
  ∧ Qc (diagStep ∅ 0) = Qc ∅ + 1
theorem ws4_conserved_reachable (hinf) :
    (∀ insp, ¬ ResidueRecoverable insp) ∧ Qc (diagStep ({0}) 0) = Qc ({0})
theorem ws4_crux_both_reachable (hinf) : (Qc (diagStep ∅ 0) = Qc ∅ + 1) ∧ (Qc (diagStep ({0}) 0) = Qc ({0}))

-- WS5 (ws5.lean): verdict computed, discriminating, flags justified, audit a-e
theorem ws5_verdict_eq : verdict true true true true true false = Outcome.conservedRel
theorem ws5_verdict_discriminates : (reaches all six Outcome constructors)
theorem ws5_flags_justified (hinf) : (WS1 nonTrivial ∧ WS2 inSight ∧ WS3 changeIsSource ∧ WS4 freeLunch ∧ WS4 conserved)
theorem ws5_audit_no_global (hinf) :
    (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)
  ∧ (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ (verdict true true true true true true = Outcome.global)
theorem ws5_audit_fork_genuine (hinf) : (Qc rises) ∧ (Qc holds) ∧ rankM e1 ≠ rankM e0
theorem ws5_audit_knot_is_diagonal (hinf) :
    (verdict true true true false true false = Outcome.partial') ∧ (verdict true true true false false false = Outcome.partial')
  ∧ (∀ insp, ¬ ResidueRecoverable insp)
theorem ws5_audit_change_is_source (hinf) :
    (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y) ∧ ¬ Recoverable (destML hinf)
theorem ws5_audit_names_not_terms : True
```

## 3. Success criteria (restated without motivating clauses)

The code must compile sorry-free; each theorem body must actually prove its stated type (no `sorry`, no `admit`, no
`axiom`); `rankM` must be defined as a fixed `MCar → ℕ` with NO conservation/rise clause; `verdict` must compute
`conservedRel` on the certified flags by `rfl`/`decide` and reach all six `Outcome` constructors; the deciding flags
in `ws5_flags_justified` must be the actual WS1–WS4 theorem payoffs (not restated bare).

## 4. Audit checks (mechanical, on the CODE)

- **(a) no global conservation.** Confirm no theorem body proves `rankM (reifyM s) = rankM (constituent)` or any
  globally-invariant-`rankM` claim. `ws2_tick_conserves` must give only plain-bisimilarity, NOT rank-equality (indeed
  `rankM e1 = 1 ≠ 0 = rankM e0`). `global` is returned by `verdict` only under `globalForced = true`. SERIOUS if a
  global conservation is proved.
- **(b) rankM not rigged.** Confirm `rankM`'s DEFINITION (`ws1.lean`) is structural (`if x = e1 then 1 else …`), not
  a conservation/rise clause. SERIOUS if rigged.
- **(c) knot is the diagonal, not import-ness.** Confirm `ws4_free_lunch_reachable`/`ws4_conserved_reachable` route
  through `ws2_residue_free` / `ws1_coincidence_not_identity_witness` (the residue), and `ws5_audit_knot_is_diagonal`
  proves `verdict … false true false = partial'` and `verdict … false false false = partial'` (import-ness alone
  never yields `conservedRel`/`freeLunch`). SERIOUS if the verdict rests on import-ness.
- **(d) change is an import.** Confirm `ws3_change_is_source`'s `¬ Recoverable` half routes through
  `ws4_recoverable_not_import` (Series 07). SERIOUS if asserted without it.
- **(e) fork not by fiat.** Confirm both `ws4_free_lunch_reachable` and `ws4_conserved_reachable` are proved (not
  `sorry`), neither branch excluded by construction.

## 5. Strip test (on the CODE)

For each payoff, mentally delete the interpretive term and confirm the theorem still states a bare fact:
WS1 → distinct-valued function + a plain-bisimilar/label-separated pair; WS2 → `reifyM {e0}` plain-bisimilar to
`e0`; WS3 → different rank + plain-bisimilar ⇒ `¬ Recoverable`; WS4 → two distinct free residues + a `Finset.card`
that rises in one branch, holds in the other; WS5 → a discriminating `Bool⁶ → Outcome`. A payoff that strips to
vacuity is a finding. The WS4 `Qc`/`diagStep` count is a DECIDABLE SKELETON — judge whether the residue facts
(`ws2_residue_free`, the distinct-residues witness) are genuinely conjoined (they are the load-bearing content), not
whether the count "derives" them (it does not, and is not claimed to — this is disclosed).

## 6. Names-not-terms (run this grep mentally over the sources)

No definition, theorem, or PARAMETER name may embed, as a whole word, any of: `energy`, `conservation`,
`information`, `measure`, `creation`, `self`, `import`, `god`, `choice`, `subjectivity`. Check every `def`, `theorem`,
`lemma`, `abbrev`, `inductive`, constructor, and the `verdict` parameter list. Docstring/comment PROSE and the Lean
`import` keyword statements (`import P2S6`, `import P2S7.ws1`) are EXEMPT — those are not identifiers. Flag any
IDENTIFIER that embeds a forbidden word.

## 7. Grading rubric

- **SERIOUS:** a theorem does not prove its stated type; a `sorry`/`axiom`; a global conservation proved; the knot
  rests on import-ness not the diagonal; `rankM` rigged; a fork side excluded by fiat; a forbidden word names an
  identifier; a non-standard axiom (beyond `propext`/`Classical.choice`/`Quot.sound`); an undisclosed narrowing
  between the contract §2 and the code.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed docstring vs a weaker theorem, an
  assumed-and-returned hypothesis, the count skeleton doing work the residue facts should).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, naming nit, or a disclosed skeleton.

Return a structured list of findings, each with a stable ID (`Fn-Sm`), grade, exact location (file + theorem), and
the defect. If nothing is SERIOUS, say so explicitly.
