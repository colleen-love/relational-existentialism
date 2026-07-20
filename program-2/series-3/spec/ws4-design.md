# WS4 — The two-zone fork (SHAPE-DRAWN, the knot). Design.

**Target (charter §2-WS4).** Prove `Converges₂` UNDECIDED by the structure over the full faithful class and
DECIDED over the in-sight sub-class, the two zones separated by Series 07's import boundary
(`ws4_two_zone_convergence`). The fork must genuinely reach BOTH values on witnessed valuations, and the faithful
class must carry a structural constraint (no PR1-S1 tautology). This is the knot, and its danger is precisely
PR1-S1.

## 1. Candidates

- **(A) Unconstrained valuation type decides the fork.** REJECTED: PR1-S1 verbatim. `Converges₂` over an
  unconstrained `Valuation` lands `underdet` on every structure by typing. The class MUST carry `Faithful₂` and
  the two zones MUST be witnessed on the S2 pair.
- **(B) A reflexive-locus fork (`(slf, slf)`).** REJECTED (Series 12 PR2-S1): the reflexive arm is a triviality at
  a non-edge, not falsifiable. The fork must live at the genuine pair `(slf, oth)`.
- **(C, WINNER) The two-zone fork at `(slf, oth)`, boundary = Series 07's import boundary.** (i) full faithful
  class underdetermined (`cUnif` converges, `cDiss` fails, both faithful); (ii) in-sight sub-class decided
  (`ws2_converges_decided_in_sight`); (iii) every faithful dissent an import (`ws3_dissent_is_import`); PLUS the
  class genuinely constrained (`ws4_insight_proper`: in-sight ⊊ faithful). Series 12's corrected fork (PR2-S1),
  fresh on the S2 pair.

## 2. Triage (paper)

| Criterion | (C) verdict |
|---|---|
| Both zones on witnessed valuations at the SAME pair | `cUnif` converges, `cDiss` fails, both faithful, both at `(slf, oth)`. |
| Class structurally constrained (audit c, anti-PR1-S1) | `ws4_insight_proper`: in-sight inhabited (`cUnif`) AND properly contained (`cDiss` faithful, out of sight). |
| Boundary = Series 07 | dissent side is `ws3_dissent_is_import` (`¬ Recoverable`, Series 07). |
| Strip test | Strips to "a discriminating function over the faithful class reaching two values, both witnessed." |

## 3. Winning construction (typed signatures)

```lean
/-- The uniform valuation: constant, identity raising. Faithful, in-sight, converges at `(slf, oth)`. -/
def cUnif : Valuation RCar (ULift.{0} Bool) := ⟨fun _ => ⟨true⟩, fun _ _ o => o⟩
/-- The dissenting valuation: `⟨true⟩` on `slf`, `⟨false⟩` elsewhere, identity raising. Faithful, NOT
    in-sight (separates the plain-bisimilar `slf`, `oth`), fails at `(slf, oth)`. -/
def cDiss : Valuation RCar (ULift.{0} Bool) := ⟨fun z => if z = slf then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩

lemma cUnif_faithful : Faithful₂ cUnif
lemma cDiss_faithful : Faithful₂ cDiss
lemma cUnif_insight (hinf : ℵ₀ ≤ κ) : InSight (outDest hinf attendsR) cUnif
lemma cUnif_converges : Converges₂ cUnif slf oth                    -- rfl
lemma cDiss_not_converges : ¬ Converges₂ cDiss slf oth             -- decide (⟨true⟩ ≠ ⟨false⟩)

/-- **THE IN-SIGHT CLASS IS GENUINELY CONSTRAINED (anti-PR1-S1).** In-sight is inhabited (`cUnif`) and PROPERLY
    contained in the faithful class (`cDiss` is faithful but NOT in-sight — it separates the plain-bisimilar
    `slf`, `oth`), so restricting to in-sight is a real constraint excluding a genuine faithful valuation. -/
theorem ws4_insight_proper (hinf : ℵ₀ ≤ κ) :
    (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
  ∧ (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c)

/-- **WS4 — THE TWO-ZONE FORK, at the genuine pair `(slf, oth)`.** (i) over the full faithful class convergence
    is UNDERDETERMINED (`cUnif` converges, `cDiss` fails, both faithful); (ii) over the in-sight faithful
    sub-class it is DECIDED, forced to hold; (iii) every faithful dissent is a genuine import. The boundary is
    Series 07's import boundary, not a reflexive triviality; both zones reached on witnessed valuations. -/
theorem ws4_two_zone_convergence (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val))
```

`ws4_two_zone_convergence := ⟨⟨cUnif, cDiss, cUnif_faithful, cDiss_faithful, cUnif_converges,
cDiss_not_converges⟩, ws2_converges_decided_in_sight hinf, ws3_dissent_is_import hinf⟩`. `ws4_insight_proper`: the
proper witness `cDiss` — if it were in-sight it would agree on the plain-bisimilar `slf`, `oth` (contradicting
`cDiss_not_converges` via `faithful_converges_iff`).

## 4. Outcome classes

- **shapeDrawn** (expected, this WS): the fork reaches both values on a constrained class.
- **convergenceDecided:** the underdetermination arm's negative witness `cDiss` is what keeps `shapeDrawn` from
  collapsing to `convergenceDecided`; without a faithful dissent the verdict would be `convergenceDecided`
  (reachable, pre-registered — never hand-set on this witness).

## 5. Strip-test annotation

`ws4_two_zone_convergence` strips (delete "convergence"/"two-zone"/"in-sight") to: "(i) two identity-raising
valuations, one agreeing and one disagreeing on `slf`, `oth`; (ii) any identity-raising valuation agreeing on all
plain-bisimilar pairs agrees on `slf`, `oth`; (iii) any identity-raising valuation disagreeing on `slf`, `oth`
has a `¬ Recoverable` lift" — three bare equality/`IsBisim`/`Recoverable` facts, both zones witnessed. Survives.
The direction (whether `slf`, `oth` DO cohere) is never stated: both `cUnif` and `cDiss` are witnesses inside
existentials, deciding nothing about the exogenous valuation.
