# WS7 — The anti-trivialization audit

**Design doc. Series 05, the honesty workstream. Owns the program verdict: whether boundlessness, groundlessness, cross-level relating, and non-collapse genuinely reduce to one fact — the double-unboundedness of the tower — or whether that unification is an artifact of the construction.**

*Standalone. Depends on all of WS1–WS6. Transcribes the Series 04 verdict machinery `ProgramVerdict` (`payoffsEstablished` / `oneFinitude` / `trivialized`) and the distinctness-anchor pattern (`ws7_deductions_dont_collapse`, `ws7_plurality_vs_collapse_distinct`). This is Claude-auditing-Claude, a disclosed limitation (charter §9); the distinctness anchor is the objective part.*

## The object at stake

Series 05's signature risk (charter §8, §9): that the payoffs of §5.4 are *one construction restated* — the interconnection assumed, not found. Series 04's WS7 was honestly downgraded from `oneFinitude` to `payoffsEstablished` after adversarial review (R1) showed `ws7_payoffs_hold` was a *conjunction*, not a derivation from `FinitudeOfFacing`. Series 05 must not repeat that laundering: the analogous single fact is **DoubleUnboundedness** (the index has no least and no greatest element, with unbounded cardinals), and WS7 must ask whether the payoffs *derive from it* or are merely *conjoined with it*. The design also carries the **anti-laundering strip tests** pre-registered across WS3/WS4/WS6 (the "delete face/view/level and see if it still goes through" checks), aggregating them into the verdict.

**Ambient theory.** No new mathematics — WS7 consumes WS1–WS6. The verdict is a typed inductive (transcribed Series 04). The distinctness anchors are structural impossibilities (objective); the reduction claims are the subjective part, disclosed.

## Part A — The single fact beneath the payoffs

### Candidates for "the one fact"

- **F1 — DoubleUnboundedness (the target).**
```lean
/-- The single fact the payoffs are meant to be consequences of: the index has no
    least and no greatest element, and the cardinals are unbounded. -/
def DoubleUnboundedness (T : Tower Q) : Prop :=
  (∀ a, ∃ b, T.le a b ∧ a ≠ b)              -- no last level
  ∧ (∀ a, ∃ b, T.le b a ∧ a ≠ b)            -- no first level
  ∧ (∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card)  -- unbounded cardinals
theorem ws7_double_unboundedness (T : Tower Q) (h_ℤ_index) : DoubleUnboundedness T
```
**Paper triage.** Decidable — for the `ℤ` index it is `ws2_no_least ∧ ws2_no_great ∧ hunb`. This is the exact analogue of Series 04's `FinitudeOfFacing`. Winner as the candidate single fact. **But note immediately (the honest worry):** `DoubleUnboundedness` is a fact about the *index*, so any payoff that reduces to it *transparently* is at risk of being a bare index fact with carrier vocabulary painted on — precisely the WS4 no-view laundering. So the reduction, if it holds, may be evidence *for* trivialization rather than against it. WS7 must distinguish "derives from double-unboundedness *through the face/carrier structure*" from "is double-unboundedness relabelled."

- **F2 — DoubleUnboundedness + leak-free composition (a two-fact base).**
```lean
def TowerCore (T : Tower Q) : Prop := DoubleUnboundedness T ∧ CrossLevelLeakFree T
```
**Paper triage.** Series 05 has *two* genuine ingredients, not one: the index's double-openness (WS2/WS4) *and* the inherited leak-free composition (WS6, `ws3_faces_never_annihilate` transported). Some payoffs (no-top, non-collapse) lean on the former; others (cross-level relating, non-termination) lean on the latter. **So the honest "single fact" may actually be two** — and if so, the "one double-unboundedness" thesis is *already* partly false, exactly the finding WS7 exists to surface. Keep F2 as the realistic base; it pre-empts an over-strong `oneFactReduction`.

**Winner: F1 as the *claimed* single fact, F2 as the *actual* base — the gap between them is the verdict's content.**

## Part B — The payoffs, and whether they derive or are conjoined

```lean
/-- **T2 — the payoffs hold (a conjunction, NOT a derivation).** Boundlessness (WS3),
    groundlessness-without-collapse (WS4), cross-level leak-free relating (WS6),
    non-degeneracy/plurality (WS3), and the incompletenesses (WS6). Following Series 04
    review R1: this is a CONJUNCTION of independently-established facts; it does not
    take `DoubleUnboundedness` as hypothesis and derive them. Named `ws7_payoffs_hold`,
    not `ws7_one_double_unboundedness`, to say only what it proves. -/
theorem ws7_payoffs_hold (T : Tower Q) (hdu : DoubleUnboundedness T) :
    (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y)                       -- no-top (WS3)
  ∧ ((∀ x, ∃ y, RelatesInf T y x ∧ StrictlyLower T y x) ∧ (∃ a b : Winf T, a ≠ b))  -- groundless+plural (WS4)
  ∧ (∀ t, t.1.Nonempty → (∀ p ∈ t.1, NonAtomic p.2) → NonAtomic (crossEdge_lcomp T t))  -- leak-free (WS6)
  ∧ (∀ v : ViewAt T, ∃ y, ¬ FaceReaches T v y)                    -- no completing view (WS4/WS6)

/-- The genuine (partial) derivations from double-unboundedness — the payoffs that DO
    follow from `hdu`, mechanized. Expected: no-top (uses no-last-level) and
    descent-non-termination (uses no-first-level) genuinely derive; leak-freeness does
    NOT (it derives from the inherited composition, F2's second fact). -/
theorem ws7_notop_from_du (T : Tower Q) (hdu : DoubleUnboundedness T) :
    ∀ x : Winf T, ¬ ∀ y, RelatesInf T x y
theorem ws7_descent_from_du (T : Tower Q) (hdu : DoubleUnboundedness T) (x : Winf T) :
    ∀ d : ℤ, ∃ finer d', d' < d ∧ RelatesAtGrade T x finer d'
theorem ws7_leakfree_NOT_from_du (T : Tower Q) :
    -- leak-freeness holds WITHOUT double-unboundedness (it is the inherited composition)
    CrossLevelLeakFree T ∧ ¬ (CrossLevelLeakFree T → DoubleUnboundedness T)
```
**Paper triage.** `ws7_payoffs_hold` conjoins the WS3/WS4/WS6 payoffs — decidable, a conjunction. `ws7_notop_from_du` and `ws7_descent_from_du` are the *genuine* derivations (no-top from no-last-level, descent from no-first-level) — these are real reductions, mechanizable. `ws7_leakfree_NOT_from_du` is the honest counterweight: leak-freeness is the *inherited* fact (F2's second ingredient), independent of double-unboundedness. **So the mechanized picture: two payoffs derive from double-unboundedness, one (leak-freeness) does not — the reduction is partial, and WS7 says so.** This is the Series 04 pattern exactly (`ws7_incompleteness_off_from_finitude` was the *one* genuine derivation there). Winner.

## Part C — The distinctness anchors (the objective guard against trivialization)

```lean
/-- **T3a — no-top and non-collapse live on provably different structures.** No-top is
    about the colimit `W_∞` (unbounded), non-collapse is the failure of the
    single-carrier collapse hypothesis (`ws5_global_groundless_collapses`). They are
    consequences on different objects, not one deduction restated. -/
theorem ws7_notop_vs_collapse_distinct (T : Tower Q) (hdu) (κ) (hinf : ℵ₀ ≤ κ) :
    (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y)
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X)

/-- **T3b — boundlessness (tower) and the Explosion Dilemma (single carrier) are
    distinct.** The tower is boundless-and-plural; a single carrier provably cannot be
    (WS2 `ws2_explosion_dilemma`). Different objects, contradictory properties — not
    one statement. -/
theorem ws7_tower_vs_carrier_distinct (T : Tower Q) (hdu) (κ) (hinf : ℵ₀ ≤ κ) :
    (∃ x y : Winf T, x ≠ y ∧ ¬ ∀ z, RelatesInf T x z)
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X)

/-- **T3c — the poles are an index fact, the payoffs are carrier facts.** Pole
    coincidence (WS4 P1) survives stripping the carrier (it is order self-duality);
    no-top (WS3) does not (strip the carrier and there is nothing to relate). So they
    are genuinely different in kind — the strip test mechanized as a distinctness. -/
theorem ws7_poles_vs_notop_distinct (T : Tower Q) (hdu) : ...
```
**Paper triage.** These are the objective anchors — structural impossibilities and strip-test results, not subjective independence claims. `ws7_notop_vs_collapse_distinct` and `ws7_tower_vs_carrier_distinct` mirror Series 04's `ws7_plurality_vs_collapse_distinct` (different carriers, contradictory properties). `ws7_poles_vs_notop_distinct` mechanizes the WS4 strip test as a distinctness (poles survive stripping, no-top does not). **Decidable; these are the honest core.** Winner — mechanize as many rows as WS3/WS4/WS6 support (Series 04 managed two rows; Series 05 should target three or four, given the sharper strip-test discipline).

## Part D — The typed verdict

```lean
/-- Transcribed Series 04 verdict type. -/
inductive ProgramVerdict
  | payoffsEstablished     -- payoffs hold, distinct where mechanized, common origin argued not mechanized
  | oneDoubleUnboundedness -- STRONGER: all payoffs derived from double-unboundedness
  | trivialized            -- the unification is definitional / the payoffs are index facts relabelled
  deriving DecidableEq

/-- **The verdict.** Given the paper triage: TWO payoffs derive from double-unboundedness
    (`ws7_notop_from_du`, `ws7_descent_from_du`), ONE does not (`ws7_leakfree_NOT_from_du`,
    it is inherited composition), the distinctness anchors refute `trivialized`, and the
    full reduction of ALL payoffs to one fact is not mechanized (leak-freeness is a second
    fact, F2). So the honest verdict is the middle: `payoffsEstablished`. -/
def ws7_verdict : ProgramVerdict := ProgramVerdict.payoffsEstablished

theorem ws7_not_trivialized : ws7_verdict ≠ ProgramVerdict.trivialized := by decide
theorem ws7_not_one_du : ws7_verdict ≠ ProgramVerdict.oneDoubleUnboundedness := by decide
theorem ws7_verdict_eq : ws7_verdict = ProgramVerdict.payoffsEstablished := rfl
```
**Paper triage.** The verdict follows deterministically from Parts A–C: distinctness anchors refute `trivialized`; the incomplete reduction (leak-freeness is a second fact) refutes `oneDoubleUnboundedness`; `payoffsEstablished` is the honest middle. **This is decidable given the mechanized rows** — exactly Series 04's outcome, and for the same structural reason (a conjunction with partial derivation and mechanized distinctness). Winner.

### The candidate that would force a different verdict

- **`trivialized`** would be forced if the strip tests (WS4 V2, and any payoff that survives only as a bare index fact) showed *all* payoffs are double-unboundedness relabelled. The WS4 triage already found V2 (no-view) launders and must be replaced by V3 (which survives). **If V3 also failed the strip test**, the no-view payoff would be index-only, and combined with the poles (index-only by design) the verdict would tilt toward `trivialized` for the "totality" payoffs — a sharp negative, a success per §7. WS7 must run the strip test on V3 explicitly and report.
- **`oneDoubleUnboundedness`** would be forced only if leak-freeness *also* derived from double-unboundedness — which `ws7_leakfree_NOT_from_du` refutes (it is inherited). So this verdict is unreachable given the honest base F2.

## The aggregated anti-laundering ledger (the deliverable that makes the verdict honest)

WS7 collects the per-workstream strip tests into one table, each row DECIDABLE ON PAPER:

| Payoff | Statement | Strip test (delete face/view/level) | Survives? | Earned or index-fact |
|---|---|---|---|---|
| No-top (WS3 B2) | no object relates to everything | delete "no last level" (give index a top) → falls to single-carrier cardinal wall | **yes** | earned (uses no-last-level load-bearingly) |
| Groundless-no-collapse (WS4 A2) | descent unbounded, `W_∞` not a point | delete plurality of objects → non-collapse vacuous | **yes** | earned (uses object plurality) |
| Poles coincide (WS4 P1) | no-first ≡ no-last | delete carrier → still true (order self-duality) | **no** | index fact; philosophical reading flagged interpretation |
| No-view V2 (WS4) | no view at an extremal level | delete View wrapper → "no extremal index element" | **no** | LAUNDERS — not reported as payoff |
| No-completing-view V3 (WS4/WS6) | a view's face misses an object | delete face → nothing to miss | **yes** | earned (uses the face's reach) |
| Leak-free (WS6 A) | composition never annihilates | delete grade → Series 04's real theorem | **yes** | earned (inherited, genuine) |
| Attention grade-shift (WS6 D) | attend = reindex | delete carrier → bare reindexing, no dynamics | **no** | Trivialized unless AT2/AT3 |

**This table IS the triage collapsed into a decision** (per the user's instruction that the framing choice is downstream of the triage): the payoffs that survive their strip test (no-top, non-collapse, no-completing-view, leak-free) are the earned content; those that do not (poles, V2, attention) are reported as index facts / laundering / Trivialized. The verdict `payoffsEstablished` is exactly "the surviving payoffs hold and are distinct; the reduction to one fact is partial; some totality-payoffs are index facts, honestly flagged."

## Definitions and lemmas needed

```lean
namespace Series05.WS7
-- transcribed: ProgramVerdict (Series 04)
def DoubleUnboundedness (T : Tower Q) : Prop := ...   -- Part A
def CrossLevelLeakFree (T : Tower Q) : Prop := ...     -- from WS6
-- consumes: ws3_no_top, ws4_groundless_no_collapse, ws4_no_completing_view,
--   ws6_crosslevel_never_annihilate, ws6_descent_nonterminating, ws2_explosion_dilemma,
--   ws5_global_groundless_collapses (transcribed)
```

**Dependencies on imported upstream theorems.** Everything: WS1 (`Winf`), WS2 (`ws2_no_least`, `ws2_no_great`, `hunb`, `ws2_explosion_dilemma`), WS3 (`ws3_no_top`), WS4 (`ws4_groundless_no_collapse`, `ws4_no_completing_view`, `ws4_poles_coincide`), WS6 (`ws6_crosslevel_never_annihilate`, `ws6_descent_nonterminating`, `attend`). Transcribed Series 04: `ProgramVerdict`, the distinctness-anchor pattern, `ws5_global_groundless_collapses`.

## What counts as failure

- *All totality-payoffs launder:* if the strip test shows no-top, non-collapse, and no-completing-view are all bare index facts, the verdict is `trivialized` — a sharp negative, a success per §7. (The paper triage expects three of four to survive, so `payoffsEstablished` is expected.)
- *Self-audit blind spot:* WS7 is Claude-auditing-Claude (disclosed). The distinctness anchors (Part C) are the objective guard; the reduction claims (Part B) are the subjective part. If the anchors were themselves definitional, the audit would be circular — so each anchor must be a structural impossibility (contradictory properties on different objects), checkable independent of intent.

## Outcome classes (per charter §7)

- **Discharged:** the audit itself — the strip-test ledger, the partial-derivation theorems, the distinctness anchors, and the typed verdict, all mechanized where the paper triage says they can be.
- **The verdict:** `payoffsEstablished` — the surviving payoffs hold and are distinct; the reduction to one double-unboundedness is partial (leak-freeness is a second fact); the poles/V2/attention are index facts / laundering / Trivialized, honestly flagged. **Not** `oneDoubleUnboundedness` (reduction incomplete), **not** `trivialized` (anchors refute it).
- **Trivialized (typed, reachable, refuted):** remains a live alternative the mechanized anchors rule out — exactly as Series 04 kept it reachable.

## Deliverable

`series-05/formal/ws7.lean`: `DoubleUnboundedness`, `CrossLevelLeakFree`; `ws7_double_unboundedness` (A), `ws7_payoffs_hold` + `ws7_notop_from_du` + `ws7_descent_from_du` + `ws7_leakfree_NOT_from_du` (B), `ws7_notop_vs_collapse_distinct` + `ws7_tower_vs_carrier_distinct` + `ws7_poles_vs_notop_distinct` (C), `ProgramVerdict` + `ws7_verdict` + `ws7_not_trivialized` + `ws7_not_one_du` + `ws7_verdict_eq` (D), and the aggregated anti-laundering ledger as a doc-comment table. Axiom check owed on the verdict theorems and the distinctness anchors.
