# WS5 — The self-bounding of the world, revisited

**Design doc. Series 5. Owns: the "grain, not wall" thesis that Series 4 could reach only on the Ω-spine, now claimed for the whole tower — each object bounded by its level's grain, the tower bounded by nothing. Adjudicates against the Series 4 M1/M2 negatives: what stratification supplies that contraction-and-quotient-on-one-carrier could not.**

*Standalone. Depends on WS1 (`Tower`, `Winf`, `ws1_local_bound`), WS3 (`ws3_no_top`, `ws3_no_global_cap`), WS4 (`ws4_groundless_no_collapse`). Transcribes the Series 4 negatives `ws5_contraction_insufficient`, `ws5_quotient_insufficient`, the impossibility `ws5_global_groundless_collapses`, and the spine positive `ws5_omega_endogenous_point` / `omegaGroundlessDiagonal`.*

## The object at stake

Series 4's WS5 verdict (charter, and `series-4/formal/ws5.lean`): the endogenous bound holds *only on the Ω-spine* (`ws5_omega_endogenous_point`), and globally it *cannot* hold — global groundlessness collapses the world (`ws5_global_groundless_collapses`), while faces provably cannot free the bound (M1 `ws5_contraction_insufficient`, M2 `ws5_quotient_insufficient`). So "grain, not wall" was reached only on a one-point region and blocked everywhere else. Series 5's claim is that stratification is *exactly* what was missing: the bound moves from *within* a carrier (where M1/M2 proved faces powerless) to *between* levels (where WS3's `ws3_no_top` makes it endogenous). The design question is which statement of "the bound is now endogenous, tower-wide" (a) is provable on the colimit, (b) genuinely answers the M1/M2 negatives rather than sidestepping them, and (c) does not smuggle a fiat back in through the index or the colimit cardinal (charter §6, WS5: "reports honestly if the tower's bound smuggles a fiat back in").

**Ambient theory.** WS1's `Winf T` with level-local bounds; index `ℤ` (WS2) with unbounded cardinals. The M1/M2 negatives are transcribed and stand *unchanged* — Series 5 does not refute them (they are true: within a level, faces still cannot bound branching); it *contextualizes* them (the bounding was never supposed to happen within a level). No monad/distributive law.

## Candidates for "the bound is endogenous, tower-wide"

### G1 — The bound is endogenous because it is between-levels, not within-a-carrier (the honest form)

```lean
/-- **Grain, not wall — tower-wide.** Every object's bound is its level's grain
    (`< κ_α`, `ws1_local_bound`), and the tower has no imposed cardinal
    (`ws3_no_global_cap`). The M1/M2 negatives are respected, not refuted: within any
    single level faces still cannot bound branching; the bound was relocated BETWEEN
    levels, where WS3's no-last-level supplies it. -/
theorem ws5_endogenous_tower (T : Tower Q) (hunb : ∀ c, ∃ a, c < (T.lvl a).card) :
    -- each object bounded by its level's grain
    (∀ x : Winf T, ∃ a y, x = toColim T y ∧ Cardinal.mk ↥(lstr y).1 < (T.lvl a).card)
    -- the tower bounded by no cardinal
  ∧ (∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card)
    -- and this is NOT the within-carrier bounding M1/M2 forbid: faces still don't
    -- bound branching at any level (the negatives transcribed, standing)
  ∧ (∀ κ, ℵ₀ ≤ κ → κ ≤ Cardinal.mk (νPk κ).X)
```
- **Success condition:** the three conjuncts are `ws1_local_bound`, `ws3_no_global_cap` (WS3), and the transcribed M1 `ws5_contraction_insufficient` — all in hand.
- **Failure mode:** the third conjunct is *supposed* to hold (M1 is true); if instead one tried to make faces bound within a level, it would fail. The real failure would be conjunct 2 failing — a set-supremum on the cardinals — reducing to WS3's §4.1 wall.

**Paper triage.** This is the correct thesis statement: it *asserts M1/M2 as standing truths* and locates the endogeneity between levels. Decidable — it conjoins three proved/transcribed facts into the "grain, not wall, and here is why the old obstruction does not apply" claim. **Winner**, but it needs the adjudication (below) to be more than a conjunction.

### G2 — Direct adjudication: what stratification supplies that contraction/quotient could not

```lean
/-- **The M1/M2 adjudication.** Contraction (M1) failed because it acted within one
    carrier, leaving `#carrier ≥ κ`; quotient (M2) failed because same-face
    identification did not collapse distinct states. Stratification supplies the third
    thing: the bound is not a property of one carrier to be contracted or quotiented,
    but a relation between levels. Formally: the single-carrier bound `κ ≤ #carrier`
    (M1) and the tower's no-global-cap (`ws3_no_global_cap`) are BOTH true, of
    different objects — the carrier and the tower — so the tower does what one carrier
    provably cannot. -/
theorem ws5_stratification_frees_bound (T : Tower Q) (hunb : ∀ c, ∃ a, c < (T.lvl a).card)
    (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    -- M1 standing: one carrier is bounded below by its own κ (contraction insufficient)
    (κ ≤ Cardinal.mk (νPk κ).X)
    -- tower free: no cardinal bounds the tower (what M1 could not achieve)
  ∧ (∀ c, ∃ a, c < (T.lvl a).card) :=
  ⟨ws5_contraction_insufficient, hunb⟩
```
**Paper triage.** This is the *coincidence-style* statement pairing the standing negative (M1, on one carrier) with the recovered payoff (no-global-cap, on the tower) — the direct analogue of WS3's `ws3_wall_vs_grain` and Series 4's `ws3_same_succ_diff_face`. Decidable; it is the honest core of the adjudication the charter asks for. **Winner alongside G1** — G2 is the earned form, G1 the full thesis statement.

### G3 — Endogenous via the improper self-face, extended off the spine (the Series 4 route, retried)

```lean
/-- Attempt to extend Series 4's spine result: find a region larger than {Ω} where the
    self-face is improper and every point groundless, giving an endogenous bound
    carrying plurality. -/
theorem ws5_endogenous_off_spine (T : Tower Q) :
    ∃ (region : Winf T → Prop), (∃ a b, region a ∧ region b ∧ a ≠ b) ∧
      (∀ x, region x → GroundlessAndImproper T x)
```
**Paper triage.** This is Series 4's *named open residue* ("extending the endogenous bound off the loop-spine to carry plurality is open, and globally impossible"). On a *single* carrier it is globally impossible (`ws5_global_groundless_collapses`). Does the tower change this? **Decidable-on-paper: partially.** The improper-self-face route (`face x x = ReachSet x`) still requires self-loops, and off the spine self-faces are trivial (Series 4 `ws6_selfface_trivial`) — stratification does not change the *within-level* self-face triviality. So G3 does *not* succeed via improper self-faces even on the tower. **Reject the improper-self-face route; the tower's endogeneity comes from G1/G2 (between-levels), not from extending the spine.** Record this as: Series 5 achieves endogeneity by a *different mechanism* than Series 4's spine, precisely because the spine mechanism provably does not generalize.

### G4 — Endogenous but fiat-in-the-index (the failure to report honestly)

```lean
/-- The skeptical reading: the tower's "no imposed cardinal" is itself imposed — the
    UNBOUNDEDNESS of the index cardinals is a choice, so the fiat moved from κ to the
    shape of the cardinal assignment. -/
theorem ws5_fiat_relocated_to_index (T : Tower Q) : IndexCardinalsChosen T
```
**Paper triage.** This is the honest-hazard the charter flags (§6 WS5, §9). It is *not a theorem to prove* but a **question to adjudicate**: is the index's unboundedness a fiat? The paper adjudication: the index `ℤ` and "no greatest element" are *forced* by the Explosion Dilemma (WS2) — a single carrier *provably* walls or collapses, so *something* unbounded is necessary; the unboundedness is not a free stylistic choice but the unique escape (WS2 `ws2_forced_answer`). *However*, the specific cardinal *values* `κ_α` and their cofinality *are* chosen. **So the honest verdict: the NECESSITY of unboundedness is earned (WS2); the PARTICULAR cardinal assignment is a residual fiat.** WS5 reports this split explicitly rather than claiming total freedom from fiat. This is the "reports honestly if the bound smuggles a fiat back in" clause discharged. **Keep as the honest-limit report, not a payoff.**

## Winner: G1 (the full thesis) + G2 (the earned adjudication), with G3's spine-route rejected and G4's residual-fiat reported honestly

### The relationship to Series 4, stated precisely

Series 5's WS5 does **not** refute Series 4's WS5 — it completes its story:
- M1 (`ws5_contraction_insufficient`) stands: within a level, faces do not bound branching. **True, transcribed, unchanged.**
- M2 (`ws5_quotient_insufficient`) stands: same-face quotient does not collapse plurality. **True, transcribed, unchanged.**
- M3-impossibility (`ws5_global_groundless_collapses`) stands: within one carrier, global groundlessness collapses. **True, transcribed** — and it is *exactly* the hypothesis the tower avoids (WS4 `ws4_groundless_no_collapse`).
- M3-positive (`ws5_omega_endogenous_point`): Series 4 got endogeneity on the spine only. **Series 5 gets it tower-wide** — but by the between-levels mechanism (G1/G2), not by extending the spine (G3 rejected).

The one-line summary WS5 delivers: *Series 4 proved faces cannot free the bound within a carrier and got endogeneity only on the one-point spine; Series 5 frees the bound by refusing to have one carrier, so the M1/M2 negatives are respected (they were about the wrong locus) and the endogeneity is real tower-wide — modulo a residual fiat in the choice of cardinal values, reported honestly.*

### Definitions and lemmas needed

```lean
namespace Series5.WS5

/-- Transcribed Series 4 negatives (standing, unrefuted). -/
theorem ws5_contraction_insufficient {κ} (hinf : ℵ₀ ≤ κ) : κ ≤ Cardinal.mk (νPk κ).X  -- = carrier_card_ge
theorem ws5_quotient_insufficient {κ} (hinf : ℵ₀ ≤ κ) : ∃ a b : νLk κ (ULift Bool), a ≠ b
theorem ws5_global_groundless_collapses {κ} (hinf : ℵ₀ ≤ κ)
    (h : ∀ x : (νPk κ).X, HereditarilyNonempty x) : Subsingleton (νPk κ).X

/-- The honest residual-fiat report: unboundedness is forced (WS2), the cardinal
    values are chosen. -/
def UnboundednessForced (T : Tower Q) : Prop := ...   -- via ws2_forced_answer
def CardinalValuesChosen (T : Tower Q) : Prop := ...  -- the residual fiat
```

### Proof architecture

`ws5_endogenous_tower` (G1) and `ws5_stratification_frees_bound` (G2) are both **conjunctions of already-established facts** — `ws1_local_bound`, `ws3_no_global_cap`, transcribed M1. The mathematical content is not in a new proof but in the *statement*: pairing the standing negative with the recovered payoff so the endogeneity is earned against the M1/M2 obstruction. This mirrors exactly how Series 4's `ws7_payoffs_hold` and `ws3_same_succ_diff_face` derive their honesty from *what they conjoin*, not from a new lemma. WS7 audits that G2's two halves are about genuinely different objects (carrier vs tower) — the distinctness anchor.

**Dependencies on imported upstream theorems.** WS1: `ws1_local_bound`. WS2: `hunb` (unbounded cardinals), `ws2_forced_answer` (for `UnboundednessForced`). WS3: `ws3_no_global_cap`. WS4: `ws4_groundless_no_collapse` (the non-collapse the endogeneity relies on). Transcribed Series 4: `carrier_card_ge` (= M1), `ws5_quotient_insufficient` (M2), `ws5_global_groundless_collapses` (M3-impossibility).

## What counts as failure

- *Set-supremum on cardinals:* if `ws3_no_global_cap` fails (the index cardinals have a sup inside the theory), G1's second conjunct fails and the tower walls — report the bound as fiat (§4.1).
- *Endogeneity claimed without adjudication:* if WS5 asserts "grain not wall" without pairing it against the standing M1/M2 (G2), it is trivialization — the coincidence duty unmet.
- *Residual fiat concealed:* if WS5 claims total freedom from fiat while the cardinal values are chosen, that is the dishonest outcome the charter forbids — G4 must be reported.

## Outcome classes (per charter §7)

- **Discharged:** G1 + G2, with the residual-fiat split (G4) reported and G3's spine-route rejection recorded. This is the "grain, not wall" thesis Series 4 could not reach, now reached tower-wide with an honest fiat caveat.
- **Impossibility proved (transcribed, standing):** M1, M2, and M3-impossibility — respected, not refuted; the tower avoids M3's hypothesis rather than defeating it.
- **Partial:** if only the necessity-of-unboundedness (not the particular assignment) is fiat-free, report endogeneity as "earned in kind, residual fiat in the cardinal values" — the expected honest outcome.

## Deliverable

`series-5/formal/ws5.lean`: transcribed `ws5_contraction_insufficient`, `ws5_quotient_insufficient`, `ws5_global_groundless_collapses`; `ws5_endogenous_tower` (G1), `ws5_stratification_frees_bound` (G2), `UnboundednessForced` / `CardinalValuesChosen` (G4 honest report), and the recorded rejection of G3's off-spine improper-face route. Axiom check owed on `ws5_endogenous_tower` and `ws5_stratification_frees_bound`.
