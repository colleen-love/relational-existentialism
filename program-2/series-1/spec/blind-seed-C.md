# Blind seed, Phase C (design review), PASS 2. Series 2.1.

*(Pass 2: the signatures below incorporate the pass-1 repairs. Review them afresh.)*


**You are reviewing a set of proposed Lean 4 theorem signatures against a fixed mathematical bar. You are NOT
told what the work is "about." Judge each signature only against the contracts, the success criteria, the audit
checks, and the strip test below. Do NOT read `charter.md`, `charter-status.md`, `summary*.md`, or any file
containing motivating prose. You MAY read `spec/README.md` §1-§3 and §6-§7 (the carrier API, the witness table,
the checks, the outcomes) and the `spec/wsNN-design.md` signature/triage sections. Report findings; propose no
fixes.**

---

## 0. The carrier (what is given, not under review)

An imported ground `P2S0` provides, over a finite-out-attention coalgebra `outDest hinf attends : X → PkObj κ X`
(where `attends : X → Finset X`):
- `FinReify attends reify := ∀ s, attends (reify s) = s` (a section; total form unsatisfiable on a finite
  carrier, so used pointwise), `ws1_bound_is_finite_attention` (out-neighborhoods `< ℵ₀`, uniform in κ).
- The collapse engine `ws1_atomless_bisim dest x y (SHNE x) (SHNE y) : ∃ R, IsBisim dest R ∧ R x y`.
- Labelled functor `LkObj κ Q X`, `IsBisimL`, `plainOf`, `Recoverable`, `rankLift dest lab` (label edges by
  `lab x`), `plainOf (rankLift dest lab) = dest`.
- `FiniteAttention dest` (a bounded reader: `focus`, `reads`, `fin`, `grounded`), `AttentionDistinguishes dest
  x y := (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ ¬ ∃ R, IsBisimL dest R ∧ R x y`, `RealFor dest att x := ∃ y
  ∈ att.reads, AttentionDistinguishes dest x y`.
- The diagonal residue `residue`, `ResidueRecoverable`, `ws2_residue_free dest insp : ¬ ResidueRecoverable insp`.
- The import `impLift hinf f : Bool → LkObj κ Q Bool`, `ws4_import_breaks_baseline`, `ws4_import_quantified`.

The witness carrier `TCar := Fin 7` with `attendsT`, `reifyT`, `rankT` is defined in `spec/README.md` §3 (nodes
`p0 p1 q0 q1 kA kB kC`; cycles `p0⇄p1`, `q0⇄q1`; `attendsT kA = {p0,p1}`, `attendsT kB = {q0,q1}`,
`attendsT kC = {kA,kB}`; `rankT` = 0 on bases, 1 on `kA`/`kB`, 2 on `kC`). `cycleA := {p0,p1}`.

## 1. The signatures under review (copied from the design docs, motivation stripped)

**WS1.**
```lean
theorem ws1_cycle_reifies :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1) ∧ reifyT cycleA = kA
  ∧ attendsT (reifyT cycleA) = cycleA
  ∧ (reifyT cycleA ≠ reifyT cycleB ∧ reifyT cycleA ≠ reifyT ({kA,kB} : Finset TCar)
       ∧ reifyT cycleB ≠ reifyT ({kA,kB} : Finset TCar))
theorem ws1_composite_attention_finite (hinf : ℵ₀ ≤ κ) :
    (∀ x, Cardinal.mk (↥((outDest hinf attendsT x).1)) < Cardinal.aleph0)
  ∧ attendsT kA = cycleA ∧ (∀ z ∈ attendsT kA, z = p0 ∨ z = p1)
```

**WS2.**
```lean
theorem ws2_composite_distinguishes (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kA p0
theorem ws2_composite_residue (hinf : ℵ₀ ≤ κ) (insp : Hold (outDest hinf attendsT) → HoldPred _) :
    (¬ ResidueRecoverable insp) ∧ (∃ h : Hold (outDest hinf attendsT), h.1.1 = kA)
theorem ws2_composite_real_for (hinf : ℵ₀ ≤ κ) :
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsT) rankT),
      RealFor (rankLift (outDest hinf attendsT) rankT) att kA
theorem ws2_tick_irreversible (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsT) rankT)
```

**WS3.**
```lean
theorem ws3_stream_exogenous (hinf : ℵ₀ ≤ κ) :
    ∀ {Q} (f : Bool → Q), f true ≠ f false →
        (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R true false)
      ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false)
theorem ws3_tick_needs_stream (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (impLift hinf (id : Bool → Bool))) R ∧ R true false)
  ∧ (¬ Recoverable (impLift hinf (id : Bool → Bool)))
```

**WS4.**
```lean
def isTick (x : TCar) : Prop := x = kA ∨ x = kB ∨ x = kC
def causal (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u
theorem ws4_causal_order_endogenous :
    (causal kA kC ∧ causal kB kC) ∧ (∀ t u, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA)
theorem ws4_linearization_import (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB
      ∧ (¬ Recoverable (rankLift (outDest hinf attendsT) ord))
theorem ws4_two_zone (hinf : ℵ₀ ≤ κ) :
    (causal kA kC ∧ ¬ causal kA kB ∧ ¬ causal kB kA)
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
```

**WS5.**
```lean
inductive Outcome | twoZone | endogenous | causalImport | partial' | disconnected
def verdict (wf arrow exo causEndo linImport : Bool) : Outcome := …  -- see ws5-design.md C1
theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoZone := rfl
theorem ws5_verdict_discriminates :
    verdict true true true true false = Outcome.endogenous
  ∧ verdict true true true false true = Outcome.causalImport
  ∧ verdict false true true true true = Outcome.disconnected
  ∧ verdict true false true true true = Outcome.partial'
-- ws5_flags_justified: five conjuncts = the WS1 section (wf), the named-reader RealFor (arrow), the WS3
--   label-separation (exo), the FULL ws4_causal_order_endogenous headline incl. the rank clause (causEndo),
--   the WS4 ord-lift non-recoverability (linImport).  -- ws5-design.md C3
-- five audit theorems: ws5_audit_no_smuggled_index (a), ws5_audit_stream_exogenous (b),
--   ws5_audit_reader_loadbearing (c), ws5_audit_fork_genuine (d), ws5_audit_names_not_terms : True (e).
```

## 2. The success criteria (mathematical obligation only)

1. A finite pattern reifies into a relatum of the SAME carrier `TCar` with a genuine composed finite `attends`
   set (WS1); no new type, the section discharged pointwise, not posited.
2. The composite carries a residue non-recoverable from the plain relating; it is `RealFor` a NAMED
   `FiniteAttention` (the reader bound and used, not quantified out); its rank label is `¬ Recoverable` (WS2).
3. An exogenous `impLift`-choice is non-recoverable and load-bearing (the plain projection identifies the
   options) (WS3).
4. A `causal` order defined from `attendsT` is exhibited on a witnessed pair, is rank-constrained, and leaves a
   witnessed pair incomparable (partial, not total); every `ord`-lift distinguishing the incomparable pair is
   `¬ Recoverable` (WS4). Both exercised on `TCar`.
5. The verdict is a COMPUTED total function of the flags that DISCRIMINATES (a different flag pattern gives a
   different outcome), and the flags are each a built theorem (WS5).

## 3. The audit checks (mechanical)

- (a) NO SMUGGLED CLOCK: every temporal statement must strip (delete "time/tick/clock/before/after/order") to a
  reification, attention, `causal`-membership, or `Recoverable`/import fact. Confirm no signature uses a `Nat`
  step counter or a background index to order ticks. `rankT` is a reification-tower height; confirm it is used
  only to separate a composite from its base, NEVER to order the incomparable pair `kA`,`kB` (`rankT kA = rankT
  kB`, so it cannot).
- (b) STREAM EXOGENOUS: `ws3_stream_exogenous` / the (b) audit are `¬`-recoverability propositions, not glosses.
- (c) READER LOAD-BEARING: `ws2_composite_real_for` binds `att : FiniteAttention` and uses `att.reads`; confirm
  `Many` is NOT the payoff template.
- (d) FORK GENUINE: confirm a concurrent pair (`kA ≠ kB`, incomparable in `causal`) AND a causal pair
  (`causal kA kC`) are BOTH witnessed on `TCar`, and the order carries a structural constraint (`causal t u →
  rankT t < rankT u`). A concurrency that is empty or an order total by construction is the defect.
- (e) NAMES-NOT-TERMS: no definition/theorem is named, as content, `time`, `now`, `clock`, `before`, `after`,
  `moment`, `self`, `other`, `chance`, `choice`, or `subjectivity`.

## 4. The strip test and the forbidden names

For EACH payoff, delete the structural words ("cycle", "tick", "composite", "moment", "before", "after",
"clock", "time", "order", "stream", "self", "other") and check the statement still reads as a bare fact about
`FinReify`/section, `AttentionDistinguishes`, `RealFor`, `residue`, `Recoverable`, `causal`-membership,
`rankLift`, or standard Lean/Mathlib. A payoff that only makes sense WITH the word is doing illegitimate work.
Forbidden content-names (grep target): `time`, `now`, `clock`, `before`, `after`, `moment`, `self`, `other`,
`chance`, `choice`, `subjectivity`.

## 5. The grading rubric

- **SERIOUS:** the verdict rests on it; a smuggled clock/step-counter does the work of succession; the stream is
  assumed rather than proved exogenous; the reader is quantified out (the composite a point-tag, `Many` used as
  payoff); the fork is a tautology (empty concurrency, or an order total by construction, PR1-S1); a name is a
  proof term; an undisclosed narrowing between the success criteria and the signatures.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed conjunct, a hypothesis assumed and
  returned, an over-strong name, a bare conjunction of non-interacting facts presented as one payoff).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, an over-hypothesis, a naming nit.

Return a structured list of findings, each with a stable ID (`C1-S1`, `C1-S2`, …), a grade, the exact
obligation/signature it concerns, and the defect. Also judge, per signature, whether the design is COHERENT and
NON-VACUOUS (could it be discharged as stated on the given witness, or is it unsatisfiable / trivially true?).
Propose no fixes; report only.
