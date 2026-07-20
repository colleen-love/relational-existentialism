# WS2 — The in-sight zone (forced). Design.

**Target (charter §2-WS2).** Define the IN-SIGHT class (valuations that respect the plain relating — agree on
plain-bisimilar states, so the structure can see them). Prove that over the in-sight faithful sub-class,
`Converges₂` is FORCED at `(slf, oth)` (`ws2_converges_decided_in_sight`). The class must be non-vacuous and
genuinely constrained.

## 1. Candidates

- **(A) In-sight = all valuations.** REJECTED: vacuous constraint; the forcing would then hold for all faithful
  valuations, deciding the direction (audit (b) violation) and collapsing the fork.
- **(B) In-sight = the empty class.** REJECTED: the decidability is empty (audit (c): the in-sight zone must be
  inhabited).
- **(C, WINNER) In-sight = bisimulation-invariant valuations** — agree on every plain-bisimilar pair. Series 12's
  `BisimInvariant` (PR2-S1), rebuilt fresh. `dest` is load-bearing (the sight is the structure's sight); inhabited
  by the uniform valuation; PROPERLY contained in the faithful class (the dissenting valuation is out of sight).

## 2. Triage (paper)

| Criterion | (C) verdict |
|---|---|
| Non-vacuity | `ws2_insight_inhabited`: the uniform valuation `cUnif` is faithful and in-sight. |
| Genuinely constrained (audit c) | `ws4_insight_proper` (WS4): `cDiss` is faithful but NOT in-sight, so in-sight ⊊ faithful — a real constraint. |
| Structure load-bearing (anti-PR1-S1) | `dest` appears in `InSight`; the forcing uses `slf`/`oth` plain-bisimilar over `outDest attendsR`. |
| Strip test | Strips to "a valuation agreeing on plain-bisimilar states agrees on `slf`, `oth`, hence `val slf = val oth`." |

## 3. Winning construction (typed signatures)

```lean
/-- The IN-SIGHT class: valuations that agree on every plain-bisimilar pair — what the structure can SEE.
    `dest` is LOAD-BEARING (the sight is the plain relating's sight). -/
def InSight {X Or : Type} (dest : X → PkObj κ X) (c : Valuation X Or) : Prop :=
  ∀ x y : X, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y

/-- `slf` and `oth` are plain-bisimilar over `outDest attendsR` (the collapse engine, Series 07). -/
lemma slf_oth_bisim (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (outDest hinf attendsR) R ∧ R slf oth

/-- **WS2 — CONVERGENCE IS DECIDED WITHIN SIGHT (forced).** Every faithful valuation whose valuation is
    within the structure's sight COHERES at `(slf, oth)`: `slf` and `oth` are plain-bisimilar, so a
    sight-bound valuation is forced to agree on them, and the faithful raising makes convergence hold. -/
theorem ws2_converges_decided_in_sight (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → InSight (outDest hinf attendsR) c →
    Converges₂ c slf oth

/-- **THE IN-SIGHT CLASS IS INHABITED.** The uniform valuation is faithful and in-sight. -/
theorem ws2_insight_inhabited (hinf : ℵ₀ ≤ κ) :
    ∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c

/-- **WITHIN SIGHT IS UNIFORM (disclosed, PR3-R1 analog).** On this every-node-`SHNE` carrier every pair is
    plain-bisimilar, so an in-sight valuation is constant on all of `RCar`. The decided zone is decided
    BECAUSE what the structure sees admits only the uniform valuation (Series 07 at the valuation level). This
    exposes, rather than hides, that in-sight members are valuation-constant. -/
theorem ws2_sight_is_uniform (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), InSight (outDest hinf attendsR) c →
    ∀ x y : RCar, c.val x = c.val y
```

Proof of `ws2_converges_decided_in_sight`: `rw [faithful_converges_iff c hf slf oth]`; then `hin slf oth
(slf_oth_bisim hinf)`. `slf_oth_bisim := ws1_atomless_bisim (outDest hinf attendsR) slf oth (ws1_rcar_SHNE hinf
slf) (ws1_rcar_SHNE hinf oth)`. `ws2_insight_inhabited := ⟨⟨fun _ => ⟨true⟩, fun _ _ o => o⟩, (fun _ _ => rfl),
(fun _ _ _ => rfl)⟩`. `ws2_sight_is_uniform`: `hin x y (ws1_atomless_bisim … x y (ws1_rcar_SHNE …) …)`.

## 4. Outcome classes

- **shapeDrawn contribution:** the in-sight forcing over a genuine (proper, inhabited) class.
- **convergenceDecided:** if the in-sight forcing extended to the FULL faithful class (no faithful dissent), the
  verdict would be `convergenceDecided`. Foreclosed on this witness by `ws4`'s `cDiss` (a faithful dissent).
- **partial':** if the in-sight class were vacuous, the WS2 flag is false and the verdict is `partial'`.
  Pre-registered, not reached (`ws2_insight_inhabited`).

## 5. Strip-test annotation

`ws2_converges_decided_in_sight` strips (delete "convergence"/"in-sight") to: "a valuation `c` with identity
raising, agreeing on every plain-`IsBisim` pair, has `c.val slf = c.val oth`" — a bare `IsBisim`/equality fact.
Survives. The load-bearing content is `slf`/`oth` plain-bisimilar over `outDest attendsR`.
