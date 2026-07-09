# WS7 — The anti-trivialization audit

**Design doc. Series 4, the honesty workstream. Owns the program verdict: whether the payoffs genuinely reduce to one finitude (the finitude of facing), or whether the unification is an artifact of an over-strong definition. Can return *Trivialized*.**

*References all Series 4 workstreams (WS1–WS6) and, for the audit method, the Series 3 discipline that a bundle must be named by its parts and never `*_resolved` when a hole remains (the `ws4_graded_coherence_Luk` / `ws5_incompleteness_and_floor` naming discipline, ws4/ws5).*

## What WS7 is auditing

The charter's signature risk (§1, §5, §9): one idea — quality as restriction — answers for plurality (WS3), the endogenous bound (WS5), no-top/no-view (WS4), and the two incompletenesses (WS6). If each holds only in its *definitional* form, the five are one definition in five costumes, and the interdependence is *assumed*, not *found*. WS7 does not prove new mathematics about the object; it proves a **meta-fact about the other proofs**: that each payoff's cheap form and forced form are distinct statements shown to coincide.

## The audit is itself decidable-on-paper per workstream

For each payoff, the coincidence rule (charter §7) requires two separately-stated theorems and a proof they are equal. WS7's method is a **checklist with a decidable criterion per row**: *does the forced form's proof avoid the definitional form's defining move?* If yes, they are independent and the coincidence is real. If the forced form secretly unfolds to the definition, it is laundering.

| Payoff | Definitional (cheap) form | Forced (independent) form | Decidable independence criterion |
|---|---|---|---|
| Plurality (WS3) | `ws3_loopface_ne`: distinct faces ⇒ distinct states | `ws2_collapse`: without faces, same states are **equal** (`ws10` bisimulation) | Does the forced form invoke `ws10_unlabeled_atomless_collapses` (a pre-existing impossibility, no face notion)? If yes, independent. |
| No-top (WS4) | `ws4_view_is_positioned`: a view is a face, so positioned | `ws4_no_top_facing`: face-counting wall via `FacingInjective` + `ws12` cardinalities | Does the wall's proof route through `FacingInjective` and *not* reduce to `ws12_no_hereditary_maximal`'s bare cap? |
| No-view (WS4) | `ws4_view_is_positioned` (V1) | `ws4_no_global_observer` (V2) | Are V1 and V2 separately stated, with V2 proving an *impossibility* V1 does not mention? |
| Endogenous bound (WS5) | defining `faceRank` and asserting it bounds | M1/M2 negatives + exhibited `GroundlessDiagonal` witness | Do the M1/M2 negatives show faces *don't* tame branching/state-count, so the rank does non-trivial work the cap did? |
| Incompleteness off-diagonal (WS6) | `ws6_selfface_proper`: self-face is a proper part | `ws6_lawvere_incomplete`: the diagonal (`ws5`, no face notion) | Does `ws6_blindspot_is_diagonal` equate two *independently defined* objects (face-complement vs Lawvere witness)? |
| Incompleteness on-diagonal (WS6) | — (no cheap form) | `ws6_omega_nonterminating` | Genuinely new; passes trivially (nothing to launder). |

**Every criterion in the last column is checkable by inspecting a proof's dependency list** — decidable on paper once the WS1–WS6 Lean exists.

## Candidates for the verdict statement

### T1 — Per-payoff pass/fail only (weakest)
Report each row's independence check, no aggregate claim. **Paper triage:** honest but under-delivers; the charter promised a *program verdict* on whether the five are one finitude. Insufficient as the sole deliverable.

### T2 — The one-finitude reduction (target)
State and prove that the five forced forms all *instantiate a single lemma* — the **finitude of facing**: that a face is a proper sub-object of its source except on the self-loop diagonal.
```lean
/-- The single fact beneath the payoffs: facing is proper off the diagonal,
    improper on it. -/
def FinitudeOfFacing : Prop :=
  (∀ x y, y ∈ succ x → x ≠ y → face x y ⊊ ReachSet x)         -- proper off-diagonal
  ∧ (∀ x, x ∈ succ x → (self-loop x) → face x x = ReachSet x) -- improper on-diagonal

/-- The reduction: each forced payoff follows from FinitudeOfFacing, and each
    uses a DIFFERENT consequence of it (so they are not the same theorem). -/
theorem ws7_one_finitude (h : FinitudeOfFacing) :
    Plurality ∧ NoTop ∧ NoView ∧ EndogenousBound ∧ IncompleteOffDiag ∧ IncompleteOnDiag
```
**Paper triage — the crux.** This is the *good* outcome the charter hopes for, but stating it this way is **also the trivialization the charter fears**: if all five follow from one `FinitudeOfFacing`, are they not "one definition in five costumes"? The resolution, decidable on paper: the theorem is honest *iff* each conjunct uses a **genuinely different consequence** of `FinitudeOfFacing` (plurality uses off-diagonal difference; no-top uses the sub-object count; incompleteness-off uses the proper-part-equals-diagonal; incompleteness-on uses the improper-diagonal + coinductivity). If the five deductions are *mathematically distinct* (different intermediate lemmas, no shared reduction), then "one finitude, many consequences" is a *discovery* — the finitude is rich, not trivial. If two or more conjuncts collapse to the *same* deduction, that pair is trivialized. **So T2 must be accompanied by a distinctness ledger (T3).**

### T3 — The distinctness ledger (the guard that makes T2 honest)
For each pair of payoffs, show their deductions from `FinitudeOfFacing` do not factor through a common intermediate. **Paper triage:** decidable by dependency inspection; this is what converts T2 from "everything is one definition" (trivial) to "one finitude has five distinct mathematical consequences" (substantive). **T2 + T3 together are the winner.**

### T4 — The Trivialized verdict (the pre-registered negative)
If the distinctness ledger (T3) *fails* — if the payoffs do collapse to a common deduction — WS7 returns **Trivialized**: the unification was definitional.
```lean
theorem ws7_trivialized (evidence : two payoffs share their entire deduction) :
    ProgramVerdict.Trivialized
```
**Paper triage:** this is a *success* per charter §5/§7 (a sharp negative about the conjecture), not a failure. Must be reportable with the same weight as T2. The design ensures WS7 *can* return it — the workstream is not built to only confirm.

**Winner: T2 + T3 (one finitude with a distinctness ledger) as the hoped-for verdict; T4 (Trivialized) as the equally-weighted alternative outcome.**

## The self-audit hazard (charter §9)

WS7's own risk: being *too lenient* (passing definitional-only rows as coincidences) or *too strict* (demanding independence between forms that are legitimately related). The guard, per the Series 3 blind-review disclosure discipline: WS7 must **state, per row, why the forced form is independent**, in prose a skeptic could check, and must disclose that the audit is Claude-auditing-Claude (as Series 3's ws9/ws10 review disclosed — not claimed independence). The distinctness ledger (T3) is the objective anchor: it is a dependency-graph fact, not a judgement call.

## Relationship to the charter's success criteria

WS7 delivers the charter §8 "verdict, either way": *one finitude, substantively* (T2+T3) or *Trivialized* (T4). Both are program successes. WS7 also aggregates the per-payoff statuses from WS3–WS6 into the final report, named by parts (never `series4_resolved`) if any hole remains — the naming discipline inherited from ws4/ws5.

## Outcome classes

- **Discharged — one finitude, substantively:** T2 proved and T3's distinctness ledger complete. The headline: the five payoffs are distinct consequences of the single finitude of facing.
- **Discharged — Trivialized:** T4 proved. The conjecture's elegant unification was definitional; a sharp, honest negative.
- **Partial:** some rows pass the independence check, others are definitional-only (inheriting WS3–WS6 Partials); the verdict is mixed and stated per payoff.

## Deliverable

`series-4/formal/ws7.lean`: `FinitudeOfFacing`, `ws7_one_finitude` (T2), the distinctness ledger `ws7_distinct_deductions` (T3), and `ws7_trivialized` (T4, the typed alternative outcome). Prose deliverable: the per-row independence checklist with skeptic-checkable justifications and the Claude-auditing-Claude disclosure. Final aggregate report named by parts. This workstream closes the program.
