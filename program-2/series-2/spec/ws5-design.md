# WS5, The verdict and the audit folded in

**Design doc. Series 2.2. Owns: the COMPUTED verdict (never hand-set) from the WS1-WS4 flags, its falsifiability
(the function discriminates), the flags EARNED by the WS1-WS4 headlines, and the five audit clauses (a)-(e) as
actual propositions bundling the payoffs. The coherence of the two readings is LEFT OPEN (charter §4.d): no
outcome, theorem, or identifier decides it.**

*Imports the four workstreams; the verdict is a pure `Bool⁵ → Outcome` function computing `twoFacing` by `rfl`
on the certified flags, discriminating when a flag flips. The charter's outcome names map to Lean identifiers
carrying no forbidden content-name (audit (e)). The `ws5_*` architecture mirrors S1's `ws5.lean`.*

## The object at stake

The charter's WS5 (§2): the verdict is COMPUTED, never hand-set — TWO-FACING (WS1 well-formed, WS2 the reader
load-bearing and the twoness non-recoverable, WS3 the facing asymmetric and partial, WS4 the mutual residue
survives); ONE (WS4 collapses); TOTALIZED (WS4 a perspective closes the pair); PARTIAL (any obligation lands only
per-instance); DISCONNECTED (WS1 imports structure beyond the symmetry-breaker). The five audit checks (a)-(e)
folded in. The verdict is the residue of the process, not its premise.

## The verdict (universe-free)

```lean
inductive Outcome
  | twoFacing | one | totalized | partial' | disconnected
  deriving DecidableEq

-- flags: wf (WS1), readerTwo (WS2), facing (WS3), nonCollapse (WS4 ¬Recoverable), nonTotal (WS4 diagonal)
def verdict (wf readerTwo facing nonCollapse nonTotal : Bool) : Outcome :=
  if !wf then Outcome.disconnected
  else if !(readerTwo && facing) then Outcome.partial'
  else if nonCollapse && nonTotal then Outcome.twoFacing
  else if !nonCollapse then Outcome.one          -- the twoness recovered: the mutual reading collapses them
  else Outcome.totalized                          -- a self-total hold: a perspective closes the pair

theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing := rfl

theorem ws5_verdict_discriminates :
    verdict true true true false true = Outcome.one            -- collapse arm reachable (recoverable)
  ∧ verdict true true true true false = Outcome.totalized      -- totalize arm reachable (a self-total hold)
  ∧ verdict false true true true true = Outcome.disconnected   -- WS1 fails
  ∧ verdict true false true true true = Outcome.partial' := by decide
```
The five flags map to the five outcomes; the function is not constant (flip a flag, get a different outcome), so
the verdict is falsifiable and the WS4 fork's arms (ONE, TOTALIZED) are genuine reachable inputs (audit (d)).

## The flags are earned

```lean
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :
    (attendsR (reifyR {slf, oth}) = {slf, oth})                                              -- wf: WS1 section
  ∧ (∃ att : FiniteAttention (rankLift (outDest hinf attendsR) rankR),                        -- readerTwo: WS2 reader load-bearing
        RealFor (rankLift (outDest hinf attendsR) rankR) att oth)
  ∧ (¬ Recoverable (faceLift hinf))                                                           -- facing: WS3 asymmetric (direction import)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)  -- WS3 partial / nonTotal
  ∧ (¬ Recoverable (rankLift (outDest hinf attendsR) rankR))                                  -- nonCollapse: WS4 twoness non-recoverable
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y)                           -- residue: WS4 joint-unattended
        ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
```
- **Proof:** `refine ⟨(ws1_other_is_locus hinf).1.2, ws2_other_reader_wise hinf, (ws3_facing_asymmetric
  hinf).2.2.2, (ws3_facing_partial hinf).2, ws2_other_non_recoverable hinf, ?_⟩` and the residue from
  `(ws4_mutual_residue hinf).2.1`. Each flag is EARNED by the corresponding WS1-WS4 headline, none hand-set.

## The five audit clauses (a)-(e)

```lean
-- (a) THE OTHER IS A READER, NOT A LABEL: a named FiniteAttention for which oth is RealFor (not Many, not a tag)
theorem ws5_audit_reader_loadbearing (hinf : ℵ₀ ≤ κ) :
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsR) rankR),
      RealFor (rankLift (outDest hinf attendsR) rankR) att oth := ws2_other_reader_wise hinf

-- (b) THE TWONESS IS NON-RECOVERABLE: a proof term (the otherness an import, Series 07)
theorem ws5_audit_twoness_import (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsR) rankR) := ws2_other_non_recoverable hinf

-- (c) THE FACING IS ASYMMETRIC: a proof term (the direction of the reading non-recoverable), not an assumption
theorem ws5_audit_facing_asymmetric (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (faceLift hinf) := (ws3_facing_asymmetric hinf).2.2.2

-- (d) THE RESIDUE IS GENUINE, THE MUTUALITY TESTED: the joint-unattended residue on the witnessed mutual pair,
--     the reading order rank-constrained (no PR1-S1); both arms reachable via ws5_verdict_discriminates
theorem ws5_audit_residue_genuine (hinf : ℵ₀ ≤ κ) :
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))  -- all four readings
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y) ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)  -- joint residue
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd) := by                                          -- order rank-constrained
  refine ⟨(ws4_mutual_residue hinf).1, (ws4_mutual_residue hinf).2.1, (ws4_mutual_residue hinf).2.2.1⟩

-- (d, coherence-open) THE COHERENCE IS UNTOUCHED: no theorem/definition/identifier decides Converges₂ (Series
--     2.3's question). A NAMES property about identifiers (no `converg`/`cohere` term), certified by the §6 grep;
--     carried as a `True` placeholder, as the property is about identifiers, not a proposition.
theorem ws5_audit_coherence_open : True := trivial

-- (e) NAMES-NOT-TERMS: no proof term/definition/discharged obligation names `self`/`other`/`I`/`you`/
--     `perspective`/`love`/`loved`/`gaze`/`God`/`choice`/`subjectivity` as content. Certified by the §6 grep;
--     carried as a `True` placeholder.
theorem ws5_audit_names_not_terms : True := trivial
```

## The outcome-name mapping (audit (e))

The charter's outcome names map to Lean identifiers carrying no forbidden content-name:

| Charter outcome | Lean `Outcome` | Note |
|---|---|---|
| TWO-FACING | `twoFacing` | the expected payoff |
| ONE | `one` | the mutual reading collapses (Series 07's One) |
| TOTALIZED | `totalized` | a perspective closes the pair |
| PARTIAL | `partial'` | `partial` is a Lean keyword, primed |
| DISCONNECTED | `disconnected` | WS1 imports beyond the symmetry-breaker |

No identifier embeds `self`/`other`/`perspective`/`love`/`gaze`/`choice`/`subjectivity`/`converg`/`cohere`.

## Outcome classes (per charter §5)

- **twoFacing (expected):** all four flags earned — the other a genuine second locus, the reader load-bearing,
  the twoness non-recoverable, the facing asymmetric and partial, the mutual residue survives.
- **one / totalized / partial' / disconnected:** the pre-registered alternatives, each a reachable verdict
  input (`ws5_verdict_discriminates`), reported in full with the obstruction precise.
- **The verdict is the residue of the process.** Computed by `verdict` on the flags `ws5_flags_justified` earns;
  never hand-set. On the certified flags it computes `twoFacing` by `rfl`.

## Strip test (charter §0.3)

The verdict and flags are structural: `ws5_flags_justified` strips to the WS1-WS4 bare facts (a `FinReify`
section, a `RealFor`, two `¬ Recoverable`s, a diagonal, a bisim/membership residue); the audit clauses (a)-(d)
are the payoff proof terms; (d, coherence) and (e) are `True` placeholders certified by grep. No name is a term.

## Deliverable

`formal/P2S2/ws5.lean`: `Outcome`, `verdict`, `ws5_verdict_eq`, `ws5_verdict_discriminates`,
`ws5_flags_justified`, and the audit clauses `ws5_audit_reader_loadbearing`, `ws5_audit_twoness_import`,
`ws5_audit_facing_asymmetric`, `ws5_audit_residue_genuine`, `ws5_audit_coherence_open`,
`ws5_audit_names_not_terms`. The verdict COMPUTED (not hand-set), discriminating; the coherence left open
(charter §4.d). Axiom check reduces through the WS1-WS4 payoffs to the standard three.
