# WS4 — No top, no view from nowhere

**Design doc. Series 04. Owns: no object relates to everything (a real size-wall, not a cap), no observer surveys the whole, and the positive companion that views are positioned. Carries the facing-injectivity crux.**

*References: `νPk`, `Coalg`, `Reaches`, `ReachSet` (ws1/ws12); `carrier_card_ge` and the carrier lower bound (ws10); the hereditary no-observer / no-maximal results `ws12_no_hereditary_maximal`, `ws12_no_hereditary_observer`, `ws12_carrier_card_gt` (ws12); `face` (WS1). WS4's task is to **replace ws12's κ-fiat / cardinality-cap arguments with a self-cost-of-facing argument** that makes the same conclusions hold for a structural reason.*

## The object at stake

Charter §5.3, second payoff, and the disarming of the old "no poles" portmanteau (charter §3.7 discussion in conversation; folded here). Series 03 proved no-maximal (`ws12_no_hereditary_maximal`) and no-global-observer (`ws12_no_hereditary_observer`), but by **cardinality**: the carrier is bigger than κ (`ws12_carrier_card_gt`), so nothing reaches everything. That is true but *external* — it is the size cap doing the work, exactly the "wall not grain" the charter objects to. WS4 must re-derive the same conclusions from: **relating to `y` costs the face `x↾(x,y)`, a part of `x`; facing everything would cost more distinct parts than there are objects; impossible.** The bound becomes endogenous.

## The crux: facing-injectivity (paper-decidable to *state*, hard to *prove*)

Everything turns on:
```lean
/-- Distinct targets require distinguishable faces (at least cofinally). -/
def FacingInjective (x : (νPk κ).X) : Prop :=
  ∀ y z, y ∈ succ x → z ∈ succ x → y ≠ z → face x y ≠ face x z
```
If `FacingInjective x` holds, then `x`'s distinct faces inject into `x`'s sub-objects, so `x` cannot have more successors than it has distinguishable parts — a genuine wall. If it fails (one part of `x` faces many targets), the count collapses and no-maximal falls back to the cardinality cap.

**Why this is the crux and not a lemma:** it is plausibly *false in general* on the R2 carrier, because `face x y` (reach-through-`y`) and `face x z` can coincide if `y` and `z` lead to the same reachable region. So WS4's design must either (a) prove a *cofinal* weakening (enough targets have distinct faces to force the wall) or (b) restrict to states where facing is injective and show maximality would require leaving that class.

## Candidates for the no-top theorem

### N1 — Cardinality import (the thing to beat)
```lean
theorem ws4_no_top_cardinality : ¬ ∃ x, ∀ y, Reaches x y := ws12_no_hereditary_maximal
```
**Paper triage:** already proved (ws12), zero new content, and *exactly the fiat we are trying to eliminate.* Include only as the baseline the endogenous version must match. **Not the winner** — it is the incumbent.

### N2 — Face-counting wall (the target)
```lean
theorem ws4_no_top_facing (x : (νPk κ).X) (hinj : FacingInjective x) :
    ¬ (∀ y, y ∈ succ x) :=
  -- if x faced every object, FacingInjective would inject the whole carrier into
  -- Sub(x) ⊆ ReachSet x, forcing #ReachSet x ≥ #carrier; but ReachSet x is < κ-bounded
  -- (ws12_reachable_card_le) while the carrier is > κ (ws12_carrier_card_gt). Contradiction.
```
**Paper triage:** decidable and the argument is *clean* — it reuses two ws12 facts (`ws12_reachable_card_le`: a state's reachable set is κ-bounded; `ws12_carrier_card_gt`: the carrier exceeds κ) but routes them through `FacingInjective` so the contradiction is "faces would have to outnumber the reachable parts," a **structural** statement about the cost of facing, not a bare cardinality cap. **This is the winner for the conditional form.** Note it still *uses* the cardinality facts — but now they bound `x`'s own reachable parts (`x`'s "self"), which is the endogenous reading: *you are not big enough to face everything* is literally `#Sub(x) < #carrier`.

### N3 — Cofinal face-counting (the unconditional target)
```lean
theorem ws4_no_top_cofinal :
    ¬ ∃ x, ∀ y, Reaches x y   -- proved via: any near-maximal x has cofinally many distinct-faced targets
```
**Paper triage:** drops the `FacingInjective` hypothesis by showing that a *maximal* `x` would in particular face states in distinct `level`s (ws12's stratification), which have distinct faces because they sit at different reach-depths. Decidable-in-principle; the depth-distinctness sublemma is the work. **Attempt after N2 lands; it is N2 with the hypothesis discharged via level-stratification.**

**Winner: N2 (conditional on `FacingInjective`) as the reported result, N3 (cofinal, unconditional) as the reach goal.** Honest status: the endogenous wall is proved *for facing-injective states*, and whether all near-maximal states are facing-injective is the named crux (charter §9).

## Candidates for no-view-from-nowhere

Series 03's `ws6` found `PositionFree` holds *vacuously* on the terminal carrier and had to *manufacture* content (WS8-E). Restriction-quality makes it **structural**: a view *is* a face, and every face is positioned (indexed by whose it is).

### V1 — Definitional positionality (the cheap half)
```lean
theorem ws4_view_is_positioned :
    ∀ (view : Observation), ∃ x y, view = face x y   -- every view is some object's face toward something
```
**Paper triage:** true almost by definition once "observation" is defined as "face" — which is the charter's move (§5.3). Decidable, easy, but *this is the definitional form the coincidence rule forbids reporting as Discharged on its own.* It says positionality holds because we defined views as faces.

### V2 — Forced negative half (the earning)
```lean
theorem ws4_no_global_observer (obs : (νPk κ).X) :
    ¬ (∀ y, face obs (someEdge) ⊇ {y})   -- no observer's faces reach every object
```
**Paper triage:** this is N2/N3 applied to observation: an observer who could view everything would face everything, contradiction by the wall. Decidable; **reuses the no-top argument**, which is the point — no-top and no-view-from-nowhere are *the same wall* seen from object-side and observer-side (the charter's unification of two faces of the old portmanteau). 

### V3 — Positive substantive standpoints (companion)
```lean
theorem ws4_substantive_standpoints :
    ∃ x₁ x₂, (distinct positioned views)   -- distinct objects genuinely see differently
```
**Paper triage:** the analogue of `ws6_substantive_standpoints`, now *free* rather than manufactured, because distinct objects have distinct faces (WS3's P1/P3). Decidable, immediate from WS3.

**Winner: V1 + V2 as a coincidence pair, V3 as the companion.** The coincidence theorem for this payoff: positionality is definitional (V1) *and* the impossibility of an unpositioned total view is forced by the wall (V2). The two together earn it; V1 alone would be laundering.

## The disarmed pole-coincidence (one remark, per the "less is more" decision)

Not a workstream, not a test — a single recorded fact (charter §5.3, and WS1's `ws1_omega_face`): the face is **improper exactly at Ω** (`Ω↾(Ω,Ω) = Ω`), the sole place the part-that-faces equals the whole-faced. This is the honest residue of the old zero-object/pole-coincidence claim. WS4 records it as a one-line corollary of `ws1_omega_face` and notes it recurs in WS5 (bounding) and WS6 (Ω's non-termination); it is *not* elevated to a candidate set.
```lean
theorem ws4_pole_coincidence_residue : face (omegaState) (omegaState) = ReachSet (omegaState) := ...
```

## The coincidence duty (charter §7)

Two coincidence obligations, both routed to WS7:
1. **No-top:** the wall (N2/N3) must be *forced by face-counting*, provably distinct from the bare cardinality cap (N1). WS7 checks that N2's proof genuinely routes through `FacingInjective` / self-cost and does not secretly reduce to `ws12_no_hereditary_maximal`.
2. **No-view:** V1 (definitional) and V2 (forced) must be separate statements proved to coincide — positionality holds *and* an unpositioned total view is impossible.

## Outcome classes

- **Discharged:** N2 (conditional wall) + V1+V2 (coincidence) + V3 + the pole residue.
- **Discharged, unconditional:** additionally N3 (cofinal, hypothesis-free wall) — the headline "grain not wall" result.
- **Partial (likely honest status):** the endogenous wall proved for facing-injective states; `FacingInjective` cofinality the named open crux.
- **Failed (reportable):** if `FacingInjective` is *false cofinally* — then no-top falls back to fiat and the "grain not wall" headline fails, demoting Series 04's flagship to the incompleteness bifurcation (charter §9). A sharp, honest negative.

## Deliverable

`series-04/formal/ws4.lean`: `FacingInjective`, `ws4_no_top_facing` (N2), `ws4_no_top_cofinal` (N3, attempted), `ws4_no_global_observer` (V2), `ws4_view_is_positioned` (V1), `ws4_substantive_standpoints` (V3), `ws4_pole_coincidence_residue`. Explicit `noResortToFiat` note in each proof confirming it routes through face-counting, for WS7's audit. Axiom check owed on the bundle.
