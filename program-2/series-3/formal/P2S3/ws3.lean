/-
`program-2/series-3/formal/P2S3/ws3.lean`

WS3 - The import zone (dissent is import). Program 2 Series 3 (2.3).

Adds the FRESH labelled lift `valLift` (broadcast a valuation as the successor label; the `val` analog of
`rankLift`, transcribed in spirit from Series 12's `orientLift`, NOT imported — the layered chain forbids it) and
the general mechanism `valLift_not_recoverable` (a valuation-difference on a plain-bisimilar `SHNE` pair is an
import). Proves the WS3 payoff: EVERY faithful valuation that FAILS `Converges₂` at `(slf, oth)` does so by a
genuine import — its valuation, lifted to labels, is `¬ Recoverable` (`ws3_dissent_is_import`, resting on Series
07 as a proof term, via the collapse engine `ws1_atomless_bisim` and the negative import horn
`ws4_recoverable_not_import`). So the failure of coherence lives exactly on Series 07's import boundary.

Design docs: `program-2/series-3/spec/ws3-design.md`; shared objects `spec/README.md` §2-§4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S3.ws2

universe u

namespace P2S3

open P1.Core P1.Reader P2S0 P2S2 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **The valuation lift.** Broadcast a valuation `f` as the successor label (the `val` analog of `rankLift`): a
labelled lift whose plain quotient forgets the valuation. -/
noncomputable def valLift {X Or : Type} (dest : X → PkObj κ X) (f : X → Or) : X → LkObj κ Or X :=
  fun x => PkMap κ (fun z => (f x, z)) (dest x)

lemma plainOf_valLift {X Or : Type} (dest : X → PkObj κ X) (f : X → Or) :
    plainOf (valLift dest f) = dest := by
  funext x
  apply Subtype.ext
  show Prod.snd '' ((fun z => (f x, z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- **Valuation-difference on a plain-bisimilar pair is an import.** If `f` separates two `SHNE` states `x`, `y`
(`f x ≠ f y`) that are plain-bisimilar, then the valuation lift is not recoverable: the plain quotient merges
`x`, `y` but the valuation label distinguishes their edges. The general mechanism (Series 07 read for the
valuation). -/
theorem valLift_not_recoverable {X Or : Type} (dest : X → PkObj κ X) (f : X → Or)
    (x y : X) (hx : SHNE dest x) (hy : SHNE dest y) (hne : f x ≠ f y) :
    ¬ Recoverable (valLift dest f) := by
  intro hrec
  have hplain : ∃ R : X → X → Prop, IsBisim (plainOf (valLift dest f)) R ∧ R x y := by
    rw [plainOf_valLift]; exact ws1_atomless_bisim dest x y hx hy
  obtain ⟨R, hR, hRel⟩ := ws4_recoverable_not_import (valLift dest f) hrec x y hplain
  obtain ⟨hfwd, _⟩ := hR x y hRel
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hx.ne_empty
  have hedge : (f x, w) ∈ (valLift dest f x).1 := by
    show (f x, w) ∈ (fun z => (f x, z)) '' (dest x).1
    exact ⟨w, hw, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  have hq1 : q.1 = f y := by
    obtain ⟨w', _, hw'⟩ := (hq : q ∈ (fun z => (f y, z)) '' (dest y).1); rw [← hw']
  rw [hq1] at hfst
  exact hne hfst

/-- **DISSENT FROM CONVERGENCE IS AN IMPORT (Series 07's work, as a proof term) (WS3).** EVERY faithful valuation
that FAILS `Converges₂` at `(slf, oth)` does so by a genuine import: its valuation, lifted to labels, is
`¬ Recoverable`. From `¬ Converges₂` and `Faithful₂`, `faithful_converges_iff` gives `c.val slf ≠ c.val oth`; then
`valLift_not_recoverable` on the plain-bisimilar `slf`, `oth`. The failure lives exactly on Series 07's import
boundary. Universally quantified over `Or` and `c` (the discipline holds). -/
theorem ws3_dissent_is_import (hinf : ℵ₀ ≤ κ) :
    ∀ (Or : Type) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
    ¬ Recoverable (valLift (outDest hinf attendsR) c.val) := by
  intro Or c hf hdiss
  have hne : c.val slf ≠ c.val oth := fun h => hdiss ((faithful_converges_iff c hf slf oth).mpr h)
  exact valLift_not_recoverable (outDest hinf attendsR) c.val slf oth
    (ws1_rcar_SHNE hinf slf) (ws1_rcar_SHNE hinf oth) hne

end P2S3
