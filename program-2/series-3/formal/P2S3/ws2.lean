/-
`program-2/series-3/formal/P2S3/ws2.lean`

WS2 - The in-sight zone (forced). Program 2 Series 3 (2.3).

Defines the IN-SIGHT class `InSight` (valuations that agree on every plain-bisimilar pair — what the structure
can SEE; `dest` is LOAD-BEARING, contrast PR1-S1's phantom carrier). Proves that over the in-sight faithful
sub-class, `Converges₂` is FORCED at `(slf, oth)` (`ws2_converges_decided_in_sight`), BECAUSE `slf` and `oth` are
plain-bisimilar over `outDest attendsR` (the collapse engine, Series 07): on a structure where they were not
plain-bisimilar the forcing would fail, so the forcing is a fact about the carrier, not the parameter type. The
class is INHABITED (`ws2_insight_inhabited`, the uniform valuation). DISCLOSED (the S12 PR3-R1 analog): on this
every-node-`SHNE` carrier every pair is plain-bisimilar, so an in-sight valuation is constant on all of `RCar`
(`ws2_sight_is_uniform`) — the decided zone is decided because sight admits only the uniform valuation.

Design docs: `program-2/series-3/spec/ws2-design.md`; shared objects `spec/README.md` §2-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S3.ws1

universe u

namespace P2S3

open P1.Core P1.Reader P2S0 P2S2 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **The IN-SIGHT class.** A valuation is within the structure's sight iff it agrees on every plain-bisimilar
pair: plain bisimilarity (the collapse engine) is exactly what the relating can detect, so an `InSight` valuation
is one the structure fixes. `dest` is LOAD-BEARING. -/
def InSight {X Or : Type} (dest : X → PkObj κ X) (c : Valuation X Or) : Prop :=
  ∀ x y : X, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y

/-- `slf` and `oth` are plain-bisimilar over `outDest attendsR` (the collapse engine identifies all atomless
relata, Series 07; every node is `SHNE` by `ws1_rcar_SHNE`). -/
lemma slf_oth_bisim (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (outDest hinf attendsR) R ∧ R slf oth :=
  ws1_atomless_bisim (outDest hinf attendsR) slf oth (ws1_rcar_SHNE hinf slf) (ws1_rcar_SHNE hinf oth)

/-- **CONVERGENCE IS DECIDED WITHIN SIGHT, FORCED (WS2).** Every faithful valuation whose valuation is within the
structure's sight (`InSight`) COHERES at `(slf, oth)`: `slf` and `oth` are plain-bisimilar, so a sight-bound
valuation is forced to agree on them, and the faithful raising then makes `Converges₂` hold. The forcing genuinely
uses `slf`/`oth` plain-bisimilarity over `outDest attendsR` (audit (c), anti-PR1-S1: it would fail on a carrier
where they are not bisimilar). Universally quantified over the valuation space `Or` and valuation `c`. -/
theorem ws2_converges_decided_in_sight (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → InSight (outDest hinf attendsR) c →
    Converges₂ c slf oth := by
  intro Or c hf hin
  rw [faithful_converges_iff c hf slf oth]
  exact hin slf oth (slf_oth_bisim hinf)

/-- **THE IN-SIGHT CLASS IS INHABITED.** The uniform valuation `cUnif` is faithful and in-sight, so the decided
zone rests on a genuinely inhabited class (not a vacuously-quantified obligation). An existential (witnesses the
class, never discharges a `∀`). -/
theorem ws2_insight_inhabited (hinf : ℵ₀ ≤ κ) :
    ∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c :=
  ⟨cUnif, cUnif_faithful, fun _ _ _ => rfl⟩

/-- **WITHIN SIGHT IS UNIFORM (disclosed, the S12 PR3-R1 analog).** On this every-node-`SHNE` carrier every pair
is plain-bisimilar (the collapse engine merges the whole carrier), so an `InSight` valuation is constant on all of
`RCar`. The decided zone is decided BECAUSE what the structure sees admits only the uniform valuation (Series 07
replayed at the valuation level). This exposes, rather than hides, that in-sight members are valuation-constant. -/
theorem ws2_sight_is_uniform (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), InSight (outDest hinf attendsR) c →
    ∀ x y : RCar, c.val x = c.val y := by
  intro Or c hin x y
  exact hin x y (ws1_atomless_bisim (outDest hinf attendsR) x y (ws1_rcar_SHNE hinf x) (ws1_rcar_SHNE hinf y))

end P2S3
