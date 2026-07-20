/-
`program-2/series-3/formal/P2S3/ws4.lean`

WS4 - The two-zone fork (SHAPE-DRAWN, the knot). Program 2 Series 3 (2.3).

The genuinely-uncertain obligation, and its danger is precisely PR1-S1 (the tautology). `ws4_two_zone` packages
the fork at the genuine pair `(slf, oth)`: (i) over the full faithful class `Converges₂` is UNDERDETERMINED
(`cUnif` converges, `cDiss` fails, both faithful); (ii) over the in-sight faithful sub-class it is DECIDED, forced
to hold (`ws2_converges_decided_in_sight`); (iii) every faithful dissent is a genuine import
(`ws3_dissent_is_import`). The boundary is Series 07's import boundary, not a reflexive triviality; both zones are
reached on witnessed valuations at the SAME pair. `ws4_insight_proper` is the anti-PR1-S1 certificate: the in-sight
class is INHABITED (`cUnif`) and PROPERLY contained in the faithful class (`cDiss` is faithful but NOT in-sight —
it separates the plain-bisimilar `slf`, `oth`), so restricting to in-sight is a real constraint that excludes a
genuine faithful valuation. The direction (whether `slf`, `oth` DO cohere) is NEVER decided: both witnesses live
inside existentials, deciding nothing about the exogenous valuation (charter §4.a). `ws4_two_zone` is a packaging
lemma over WS2/WS3 plus the underdetermination witnesses (the accepted Series 12 `ws4_two_zone` pattern).

Design docs: `program-2/series-3/spec/ws4-design.md`; shared objects `spec/README.md` §2-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S3.ws3

universe u

namespace P2S3

open P1.Core P1.Reader P2S0 P2S2 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE IN-SIGHT CLASS IS GENUINELY CONSTRAINED (anti-PR1-S1, audit (c)).** The in-sight faithful class is
INHABITED (`cUnif`) and PROPERLY contained in the faithful class (`cDiss` is faithful but NOT in-sight — if it
were, it would agree on the plain-bisimilar `slf`, `oth`, hence converge, contradicting `cDiss_not_converges`), so
restricting to in-sight is a real constraint that excludes a genuine faithful valuation. The fork is therefore not
a tautology of an unconstrained valuation type. -/
theorem ws4_insight_proper (hinf : ℵ₀ ≤ κ) :
    (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
  ∧ (∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c) := by
  refine ⟨⟨cUnif, cUnif_faithful, fun _ _ _ => rfl⟩, ⟨cDiss, cDiss_faithful, ?_⟩⟩
  intro hin
  exact cDiss_not_converges
    ((faithful_converges_iff cDiss cDiss_faithful slf oth).mpr (hin slf oth (slf_oth_bisim hinf)))

/-- **THE TWO-ZONE FORK, at the genuine pair `(slf, oth)` (WS4, the knot).** (i) over the full faithful class
`Converges₂` is UNDERDETERMINED (`cUnif` converges, `cDiss` fails, both faithful); (ii) over the in-sight faithful
sub-class it is DECIDED, forced to hold (`ws2_converges_decided_in_sight`), so `shape-drawn` is FALSIFIABLE at the
pair (restricting to what the structure sees closes the fork); (iii) every faithful dissent at the pair is a
genuine import (`ws3_dissent_is_import`), so the underdetermination is EXACTLY the import Series 07 characterizes.
Both zones reached on witnessed valuations at the SAME pair; the boundary is Series 07's import boundary, not a
reflexive triviality. -/
theorem ws4_two_zone (hinf : ℵ₀ ≤ κ) :
    (∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or : Type) (c : Valuation RCar Or),
        Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val)) :=
  ⟨⟨cUnif, cDiss, cUnif_faithful, cDiss_faithful, cUnif_converges, cDiss_not_converges⟩,
   ws2_converges_decided_in_sight hinf,
   ws3_dissent_is_import hinf⟩

end P2S3
