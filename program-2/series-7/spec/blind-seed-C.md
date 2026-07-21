# Blind seed — Phase C (design review)

You are reviewing a set of Lean 4 design signatures for coherence and non-vacuity. You are BLIND to any motivating
prose. Judge ONLY the mathematical contracts below. Do not read `charter.md`, `charter-status.md`,
`charter-extension.md`, `measure-derisking.md`, `README.md`, any `summary*.md`, or any file with motivating prose.
Read ONLY this file and, if you wish to confirm signatures, `spec/ws1-design.md`…`spec/ws5-design.md` §3 (the typed
signatures) — NOT their narrative sections.

## 1. The imported machinery (given, already built and axiom-clean, transitively available)

```
-- coalgebras and bisimulation
PkObj κ X ; LkObj κ Q X ; SHNE dest x ; IsBisim dest R ; IsBisimL destL R
plainOf : (X → LkObj κ Q X) → (X → PkObj κ X)          -- forgets the label
Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R
ws1_atomless_bisim dest x y (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y   -- collapse engine
ws4_recoverable_not_import destL (hrec : Recoverable destL) x y
    (h : ∃ R, IsBisim (plainOf destL) R ∧ R x y) : ∃ R, IsBisimL destL R ∧ R x y
rankLift dest (rank : X → ℕ) : X → LkObj κ (ULift ℕ) X   -- broadcasts rank x on x's edges
AttentionDistinguishes destL x y := (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)
outDest hinf (attends : X → Finset X) : X → PkObj κ X    -- finite out-attention as a coalgebra
-- the diagonal (P1)
Hold dest ; HoldPred dest := Hold dest → Prop
diag insp := fun h => ¬ insp h h ; residue insp := diag insp
ResidueRecoverable insp := ∃ h, insp h = residue insp
ws2_residue_free dest insp : ¬ ResidueRecoverable insp        -- the residue is free, for every inspection
ws1_coincidence_not_identity_witness dest (h₀ : Hold dest) :
    ∃ insp₁ insp₂, ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂
```

## 2. The new definitions under review

```
abbrev MCar : Type := Fin 4
def e0 : MCar := 0   def e0' : MCar := 1   def e1 : MCar := 2   def e2 : MCar := 3
def attendsM : MCar → Finset MCar    -- e0,e0' self-loop; e1 → e0; e2 → e1
def rankM : MCar → ℕ                 -- e0,e0' ↦ 0; e1 ↦ 1; e2 ↦ 2      ← THE MEASURE under review
def reifyM : Finset MCar → MCar      -- {e0} ↦ e1; {e1} ↦ e2; else e0
noncomputable def destML (hinf : ℵ₀ ≤ κ) : MCar → LkObj κ (ULift ℕ) MCar := rankLift (outDest hinf attendsM) rankM
def Qc (B : Finset (Fin 2)) : ℕ := B.card
def diagStep (B : Finset (Fin 2)) (d : Fin 2) : Finset (Fin 2) := insert d B
def h0 (hinf : ℵ₀ ≤ κ) : Hold (outDest hinf attendsM)    -- e0 self-loops, so inhabited

inductive Outcome | conservedRel | monotoneOnly | freeLunch | global | disconnected | partial'
def verdict (nonTrivial inSightConserved changeIsSource freeLunchReachable conservedReachable globalForced : Bool) :
    Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if globalForced then Outcome.global
  else if !inSightConserved then Outcome.monotoneOnly
  else if !changeIsSource then Outcome.partial'
  else if freeLunchReachable && !conservedReachable then Outcome.freeLunch
  else if !freeLunchReachable then Outcome.partial'
  else Outcome.conservedRel
```

## 3. The theorem signatures under review

```
theorem ws1_rank_nontrivial (hinf) :
    rankM e1 ≠ rankM e0 ∧ AttentionDistinguishes (destML hinf) e1 e0 ∧ (∃ x y : MCar, rankM x ≠ rankM y)

theorem ws2_tick_conserves (hinf) :
    attendsM (reifyM {e0}) = {e0} ∧ reifyM {e0} = e1 ∧ (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)

theorem rankM_sep_general (dest : MCar → PkObj κ MCar) (lab : MCar → ℕ) (x y : MCar)
    (hlab : lab x ≠ lab y) (hne : (dest x).1 ≠ ∅) : ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y
theorem ws3_change_is_source (hinf) :
    (∀ x y : MCar, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y) ∧ ¬ Recoverable (destML hinf)
theorem ws3_source_nonvacuous (hinf) : AttentionDistinguishes (destML hinf) e1 e0 ∧ rankM e1 ≠ rankM e0

theorem ws4_free_lunch_reachable (hinf) :
    (∃ insp₁ insp₂, ¬ ResidueRecoverable insp₁ ∧ ¬ ResidueRecoverable insp₂ ∧ residue insp₁ ≠ residue insp₂)
  ∧ Qc (diagStep ∅ 0) = Qc ∅ + 1
theorem ws4_conserved_reachable (hinf) :
    (∀ insp, ¬ ResidueRecoverable insp) ∧ Qc (diagStep ({0}) 0) = Qc ({0})
theorem ws4_crux_both_reachable (hinf) :
    (Qc (diagStep ∅ 0) = Qc ∅ + 1) ∧ (Qc (diagStep ({0}) 0) = Qc ({0}))

theorem ws5_verdict_eq : verdict true true true true true false = Outcome.conservedRel
theorem ws5_verdict_discriminates : (six equalities reaching all six Outcome constructors)
theorem ws5_flags_justified (hinf) : (the WS1 nonTrivial ∧ WS2 inSight ∧ WS3 changeIsSource ∧ WS4 freeLunch ∧ WS4 conserved conjuncts)
theorem ws5_audit_no_global (hinf) :
    (∃ R, IsBisim (plainOf (destML hinf)) R ∧ R (reifyM {e0}) e0)
  ∧ (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y)
  ∧ (verdict true true true true true true = Outcome.global)
theorem ws5_audit_fork_genuine (hinf) :
    (Qc (diagStep ∅ 0) = Qc ∅ + 1) ∧ (Qc (diagStep ({0}) 0) = Qc ({0})) ∧ rankM e1 ≠ rankM e0
theorem ws5_audit_knot_is_diagonal (hinf) :
    (verdict true true true false true false = Outcome.partial')
  ∧ (verdict true true true false false false = Outcome.partial')
  ∧ (∀ insp, ¬ ResidueRecoverable insp)
theorem ws5_audit_change_is_source (hinf) :
    (∀ x y, rankM x ≠ rankM y → AttentionDistinguishes (destML hinf) x y) ∧ ¬ Recoverable (destML hinf)
theorem ws5_audit_names_not_terms : True
```

## 4. Success criteria (restated without motivating clauses)

1. `rankM` is not constant, and its value-difference `rankM e1 ≠ rankM e0` coincides with a genuine
   `AttentionDistinguishes` (plain-bisimilar yet label-separated). [WS1]
2. The reification map's product `reifyM {e0}` is plain-bisimilar to its constituent `e0`, and `reifyM` sections its
   pattern. [WS2]
3. Any two states with different `rankM` are `AttentionDistinguishes`, and the lift is not `Recoverable`. [WS3]
4. Two branches on the diagonal count: one strictly increases `Qc`, one leaves it unchanged; both are backed by the
   residue being free (`ws2_residue_free`) and producing ≥ 2 distinct residues from one position. [WS4]
5. `verdict` computes `conservedRel` on the certified flags, reaches all six `Outcome` constructors, and the deciding
   flags equal the WS1–WS4 payoffs. [WS5]

## 5. Audit checks (mechanical instructions)

- **(a) no global conservation.** Confirm NO signature asserts `rankM` (or `Q`) globally invariant under `reifyM`
  (e.g. a claim `rankM (reifyM s) = rankM (constituent)`). Conservation must be only via plain-bisimilarity (in-sight)
  or the count skeleton; the label `rankM` may change. Flag SERIOUS if a global invariance is asserted.
- **(b) `Q` not rigged.** Confirm `rankM` is defined structurally (a fixed `MCar → ℕ`), NOT as "invariant" or
  "increasing". Its conservation (WS2) and diagonal status (WS4) must be separate theorems, not definitional. Flag
  SERIOUS if `rankM`'s definition embeds its own conservation/rise.
- **(c) the knot is the diagonal, not import-ness.** Confirm WS4's two payoffs quantify over the RESIDUE / holds
  (`ResidueRecoverable`, `residue`, `ws2_residue_free`), NOT over boundary imports; and that `verdict` returns
  `partial'` when `changeIsSource = true` but `freeLunchReachable = false` (import-ness alone must not yield
  `conservedRel`/`freeLunch`). Flag SERIOUS if the verdict rests on import-ness (WS3) rather than the WS4 diagonal fork.
- **(d) change is an import.** Confirm `ws3_change_is_source` / `ws3_source_nonvacuous` route through
  `ws4_recoverable_not_import` (Series 07). Flag if the import claim is asserted without the Series 07 route.
- **(e) fork not by fiat.** Confirm both `ws4_free_lunch_reachable` and `ws4_conserved_reachable` are provable (the
  count facts are `decide`, the residue facts are the given theorems) and neither branch is excluded by construction.

## 6. Strip test (mechanical)

For each payoff, delete the interpretive term ("measure", "conservation", "import", "creation", "free-lunch") and
check the statement still goes through as a bare fact:
- WS1 → "a function taking two distinct values, the difference a plain-bisimilar-yet-label-separated pair".
- WS2 → "`reifyM {e0}` and `e0` are plain-bisimilar".
- WS3 → "different rank + plain-bisimilar ⇒ not label-bisimilar (`¬ Recoverable`)".
- WS4 → "self-inspection yields two distinct free residues; a count rises in one branch and not the other".
- WS5 → "a discriminating `Bool⁶ → Outcome`".
A payoff that strips to NOTHING (vacuous) or to a bare restatement with no content is a finding. NOTE explicitly: the
WS4 count (`Qc`, `diagStep`) is a decidable SKELETON; judge whether the genuine residue facts (`ws2_residue_free`,
the distinct-residues witness) are conjoined so the skeleton is not doing the work alone — if the skeleton is the
ONLY content and the residue facts are decorative, that is a REAL finding (grade it, do not pass it).

## 7. Names-not-terms (forbidden identifier list)

No definition or theorem NAME may embed, as a whole word, any of: `energy`, `conservation`, `information`, `measure`,
`creation`, `self`, `import`, `god`, `choice`, `subjectivity`. (The names above — `MCar`, `rankM`, `destML`, `Qc`,
`diagStep`, `Outcome`, `verdict`, `ws*` — must be checked against this list. Docstring prose is exempt; this is about
identifiers.) Flag any identifier that embeds a forbidden word.

## 8. Grading rubric

- **SERIOUS:** the verdict rests on it; a global conservation is asserted; the knot rests on import-ness not the
  diagonal; `Q` conserves or rises by construction (rigged); a fork side is excluded by fiat; a name is a forbidden
  content-term; an undisclosed narrowing.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaim, an assumed-and-returned hypothesis, the count
  skeleton doing work the residue facts should).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings, each with a stable ID (`Cn-Sm`), grade, exact location, and the defect. If you
find nothing SERIOUS, say so explicitly.
