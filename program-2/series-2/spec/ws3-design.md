# WS3, The four readings, asymmetric and partial (the facing)

**Design doc. Series 2.2. Owns: the FOUR readings (self of self, self of other, other of self, other of other),
typed and all witnessed; the facing ASYMMETRIC (the directed reading non-recoverable from the symmetric
relating, the S0 asymmetry-of-knowing lifted to two perspectives); the facing PARTIAL (no perspective totalizes
itself, the diagonal at each self-reading). The readings are TYPED but never EVALUATED. The sin (charter §4.a):
an inert direction tag (the Series 11 Bookkeeping failure).**

*Imports `P2S1`; the direction of the facing is a new labelled lift `faceLift` (tag each edge with whether the
reading goes strictly UP the constitution tower), whose plain reduct is the symmetric relating and which is
`¬ Recoverable` — the `ws3_direction_not_recoverable` mechanism (S0) with the label the reading-direction; the
partiality is the imported diagonal `ws1_no_self_total_hold` at each perspective's genuine self-reading.*

## The object at stake

The charter's WS3 (§2): type the four readings and prove the facing has the two structural properties the ground
forces. ASYMMETRIC: the self's reading of the other and the other's reading of the self are not interchangeable,
and their difference is non-recoverable from the symmetric relating (S0's `ws3_direction_not_recoverable` lifted
to two perspectives). PARTIAL: no perspective totalizes itself; each self-reading leaves the diagonal residue.
The readings are TYPED but never EVALUATED — every theorem is quantified over the perspectives' attentions; none
selects, constructs, or reads off a particular reading.

## The four readings (typed, all witnessed)

```lean
def faces (x y : RCar) : Prop := y ∈ attendsR x   -- x READS y (the directed reading; the knowing `knows`)

theorem ws3_four_readings :               -- the four readings are all genuine, typed not evaluated
    faces slf slf ∧ faces slf oth ∧ faces oth slf ∧ faces oth oth := by decide
```
`faces` is S0's `knows` (directed attention); the four readings are the four ordered pairs among the two loci,
all holding on the witness (`decide`). They are TYPED (a `Prop` over quantified attentions), never EVALUATED (no
theorem selects a particular reading's content).

## The direction lift (`faceLift`, the asymmetry engine)

```lean
-- tag each edge (x,y) with whether the reading is strictly UPWARD the constitution tower (rankR x < rankR y)
noncomputable def faceLift (hinf : ℵ₀ ≤ κ) : RCar → LkObj κ (ULift.{0} Bool) RCar :=
  fun x => PkMap κ (fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) (outDest hinf attendsR x)

lemma faceLift_val (hinf) (x : RCar) :
    (faceLift hinf x).1 = (fun z => ((⟨decide (rankR x < rankR z)⟩ : ULift.{0} Bool), z)) '' (↑(attendsR x) : Set RCar) := rfl
lemma plainOf_faceLift (hinf) : plainOf (faceLift hinf) = outDest hinf attendsR   -- the symmetric relating forgets direction
```
The plain reduct forgets the direction bit (`plainOf_faceLift`, `image_image` + `simp`, the `plainOf_rankLiftR`
pattern), so it is exactly the symmetric out-relating. The self reads UP (`slf → oth`, `decide (0 < 1) = true`);
the other has NO strictly-upward edge (`oth → slf` down, `oth → oth` flat). So `slf` carries an up-labelled edge
`oth` cannot match: `faceLift` label-separates them.

## Candidates

### C1, the facing is asymmetric (the directed reading non-recoverable, the lead)

```lean
theorem ws3_facing_asymmetric (hinf : ℵ₀ ≤ κ) :
    (oth ∈ attendsR slf ∧ slf ∈ attendsR oth)              -- self-of-other and other-of-self both witnessed
  ∧ (∃ z ∈ attendsR slf, rankR slf < rankR z)              -- the self reads UP the tower (to the other)
  ∧ (¬ ∃ z ∈ attendsR oth, rankR oth < rankR z)            -- the other has NO upward reading (knowing is directed)
  ∧ ¬ Recoverable (faceLift hinf)                          -- the direction is non-recoverable from the symmetric relating
```
- **Ambient:** `attendsR`, `rankR`, `faceLift`, `plainOf_faceLift`, `ws1_atomless_bisim`, `ws1_rcar_SHNE`, the
  label-separation lemma `face_label_sep` (`¬ ∃ R, IsBisimL (faceLift hinf) R ∧ R slf oth`, the
  `firstOther_label_sep` argument on the up-edge).
- **Success condition:** the first three conjuncts by `decide`; `¬ Recoverable` by the
  `ws3_direction_not_recoverable` proof (the plain-bisim relating `slf`,`oth` via the engine on `plainOf faceLift
  = outDest`, made a label-bisim by `Recoverable`, contradicting `face_label_sep`).
- **Failure mode:** *an inert direction tag (Series 11 Bookkeeping, SERIOUS)* or *the asymmetry recoverable.*
  Foreclosed: the direction is read by `IsBisimL` and is `¬ Recoverable` (a genuine structural distinction, not a
  tag on the symmetric relating); the structural asymmetry (`slf` reads up, `oth` does not) is `decide`. **Winner
  (asymmetric).**

**Distinct from WS2's twoness.** WS2 separates WHICH perspective (the SOURCE rank, `rankLift`); WS3 separates the
DIRECTION of the reading (SOURCE-vs-TARGET rank, `faceLift`). The self and the other read the SAME shared field
but face it from opposite directions of the constitution tower, and that direction is the non-recoverable
content — the asymmetry of knowing (S0 `ws3_direction_not_recoverable`), lifted from the passive witness to the
two mutual perspectives.

### C2, the facing is partial (the diagonal at each self-reading)

```lean
theorem ws3_facing_partial (hinf : ℵ₀ ≤ κ) :
    (slf ∈ attendsR slf ∧ oth ∈ attendsR oth)              -- both self-readings genuine (non-vacuity, load-bearing)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
```
- **Ambient:** `attendsR`, `Hold`, `HoldPred`, `SelfTotal`, `ws1_no_self_total_hold`.
- **Success condition:** the first conjunct by `decide` (both perspectives have genuine self-loops, so the
  self-readings self-of-self and other-of-other are real holds); the second by `ws1_no_self_total_hold` (the
  diagonal, independent of relational identity).
- **DISCLOSED (charter §0.3, honesty):** the second conjunct is the imported diagonal `ws1_no_self_total_hold`,
  the SAME diagonal fact for every inspection. It is load-bearing here PAIRED with the non-vacuity (both
  perspectives have genuine self-readings the diagonal applies to), which is exactly the charter's WS3-partial
  ("each self-reading leaves the diagonal residue"). This is the EXPECTED shape per charter §2 (WS3 partial IS
  the diagonal); the PR1-S1 tautology concern is WS4's burden (the MUTUAL residue), not WS3's. Recorded as a
  disclosed conjunction, as P1's `ws2_attention_subtractive` records the diagonal-plus-distinctness conjunction.
- **Failure mode:** *the diagonal asserted with no genuine self-reading (vacuous).* Foreclosed: both self-loops
  witnessed (`decide`). **Winner (partial).**

### C3, the direction by a background index (the tag to avoid)

```lean
def ws3_dir_bad (x : RCar) : ℕ := if x = slf then 0 else 1   -- direction as a source label, inert on the symmetric relating
```
- **Failure mode:** *a source-only tag is the twoness (WS2) again, not the DIRECTION; a background index the
  symmetric relating never reads is the Series 11 Bookkeeping tag (SERIOUS).* **Reject.** The direction must be
  the SOURCE-vs-TARGET relation read by `IsBisimL` and `¬ Recoverable` (C1).

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| four readings | all four `faces` hold | `attendsR` | yes, `decide` | **win** |
| C1 | facing asymmetric, direction `¬ Recoverable` | `faceLift`, engine | yes (S0 pattern) | **win** |
| C2 | facing partial, diagonal at each self-reading | `ws1_no_self_total_hold` | yes | **win (disclosed)** |
| C3 | direction a source/background tag | — | Bookkeeping | reject (SERIOUS) |

## Winning candidates: four_readings + C1 + C2

**Proof architecture.** `ws3_four_readings` is `decide`. C1's structural asymmetry is `decide`; its
`¬ Recoverable` is the `ws3_direction_not_recoverable` proof with the label the reading-direction (the up-edge
`slf → oth` that `oth` cannot match). C2 is `decide` (the self-readings) plus `ws1_no_self_total_hold` (the
diagonal). Lands `facing = true` for WS5. **Dependencies:** `faceLift`, `face_label_sep`, `plainOf_faceLift`
(built here); `ws1_atomless_bisim`, `ws1_no_self_total_hold`, `Recoverable` (imported); `ws1_rcar_SHNE` (WS1).

## Outcome classes (per charter §5)

- **facing = true (the expected WS3 payoff):** the four readings typed, the facing asymmetric (direction
  `¬ Recoverable`) and partial (the diagonal at each self-reading).
- **PARTIAL (pre-registered):** if the asymmetry landed only per-instance (some reading recovered the direction),
  reported PARTIAL. Foreclosed by C1's `¬ Recoverable`.

## Strip test (charter §0.3)

`ws3_facing_asymmetric` strips (delete "facing," "self," "other," "reading," "direction") to *"`oth ∈ attendsR
slf ∧ slf ∈ attendsR oth`; some `attendsR slf` edge strictly raises `rankR`; no `attendsR oth` edge does; and
`faceLift` (the up-edge label over `outDest attendsR`) is `¬ Recoverable`"* — a bare attention/rank/import fact.
`ws3_facing_partial` strips to *"both self-loops hold, and no inspection of `outDest attendsR` has a self-total
hold"* — a bare diagonal fact (the charter's SHOULD per §0.3: "under inspection no self-total hold, by the
diagonal"). Both survive: no name is a term.

## Deliverable

`formal/P2S2/ws3.lean`: `faces`, `ws3_four_readings`, `faceLift`, `faceLift_val`, `plainOf_faceLift`,
`face_label_sep`, `ws3_facing_asymmetric`, `ws3_facing_partial`. The four readings typed not evaluated; the
facing asymmetric (direction `¬ Recoverable`, the S0 asymmetry lifted) and partial (the diagonal); the direction
read by `IsBisimL`, never an inert tag (audit (c)). Axiom check reduces through the engine, `faceLift`, the
diagonal, and `decide` to the standard three.
