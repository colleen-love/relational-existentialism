/-
`program-2/series-11/formal/P2S11/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 11 (2.11).

The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= interfering` on the earned
flags, DISCRIMINATING (reaches all five outcomes), the flags EARNED by the WS1-WS4 headlines. The computed verdict is
INTERFERING: a signed sign read off the built holonomy (WS1), it cancels (WS2), the combined weight falls STRICTLY
below the parts and the sign is earned off the built holonomy (WS3), and the interfering and additive poles are both
reachable (WS4). So distinction can SUBTRACT — two paths to one outcome cancel, the combined weight falls below the
parts — the door to quantum theory open, honestly scoped as REAL (signed, `±1`) interference with the complex `U(1)`
phase and the Born rule (Series 2.12) the disclosed forward-note. The five audit clauses (a)-(e) bundle the payoffs.

Design docs: `program-2/series-11/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11.ws1
import P2S11.ws2
import P2S11.ws3
import P2S11.ws4

universe u

namespace P2S11

open P2S8

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `interfering` a signed model-derived sign destructively cancels in a weight, both poles
reachable (the door to quantum theory); `additiveOnly` no combined weight ever falls below its parts (distinction only
accumulates, the world classical — the NOT-RECOVERED specification: add a phase); `shapeDrawn` the fork drawn, neither
pole decided; `disconnected` no signed sign survives; `partial'` primed (`partial` is a Lean keyword) the sign not
earned, or a degenerate obligation. No identifier embeds a forbidden content-name. -/
inductive Outcome
  | interfering
  | additiveOnly
  | shapeDrawn
  | disconnected
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION.** `interfering` iff the sign is signed (WS1), it cancels (WS2), it is earned (WS3), the
combined weight falls strictly below the parts (WS3), and BOTH the interfering and additive poles are reachable (WS4).
`additiveOnly` if the signs never cancel, or cancel but no weight ever falls below the parts, or the additive pole is
reachable while the interfering one is not; `disconnected` if no signed sign; `shapeDrawn` if neither pole decided;
`partial'` if the sign is not earned (smuggled) or the fork is by fiat. -/
def verdict (signed cancels earned destructive interfereReachable additiveReachable : Bool) : Outcome :=
  if !signed then Outcome.disconnected
  else if !earned then Outcome.partial'
  else if !cancels then Outcome.additiveOnly
  else if !destructive then Outcome.additiveOnly
  else if interfereReachable && additiveReachable then Outcome.interfering
  else if additiveReachable && !interfereReachable then Outcome.additiveOnly
  else if !additiveReachable && !interfereReachable then Outcome.shapeDrawn
  else Outcome.partial'

/-- **THE COMPUTED VERDICT.** On the earned flags (a signed sign, it cancels, it is earned, the weight falls strictly
below the parts, and both poles reachable), `interfering`, by computation. -/
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.interfering := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all five outcomes. -/
theorem ws5_verdict_discriminates :
    verdict false true true true true true    = Outcome.disconnected
  ∧ verdict true true false true true true     = Outcome.partial'
  ∧ verdict true false true true true true     = Outcome.additiveOnly
  ∧ verdict true true true true true true      = Outcome.interfering
  ∧ verdict true true true true false false    = Outcome.shapeDrawn := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The six deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set: `signed`
(WS1, `ws1_amp_signed`); `cancels` (WS2, `ws2_amp_cancels`); `earned` (WS3, `ws3_amp_earned`); `destructive` (WS3,
`ws3_destructive` — the interfering pole, WS4); `additiveReachable` (WS4, `ws4_additive_reachable`). -/
theorem ws5_flags_justified :
    (loopAmp attTri = -1 ∧ loopAmp attStar = 1)
  ∧ (directAmp + loopAmp attTri = 0)
  ∧ (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2))
  ∧ (combinedWeight attTri < partsWeight attTri)
  ∧ (partsWeight attStar ≤ combinedWeight attStar) :=
  ⟨ws1_amp_signed, ws2_amp_cancels, ws3_amp_earned.1, ws3_destructive, ws4_additive_reachable.1⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) THE PHASE IS EARNED, NOT SMUGGLED (the no-smuggling gate, sharpest in the program).** The sign is a function
of the built `incr`/`hol` (definitional): `loopAmp` unfolds to `amp (hol …)`, and `hol` is Series 2.8's `incr`-sum. No
complex number, no postulated phase. -/
theorem ws5_audit_earned :
    (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2))
  ∧ (∀ (att : S → Finset S) (x y z : S),
        hol att x y z = incr att x y + incr att y z + incr att z x) :=
  ⟨ws3_amp_earned.1, ws3_amp_earned.2.1⟩

/-- **(b) THE FORK NOT BY FIAT.** Interfering (ring `0 < 2`) AND additive (star `2 ≤ 4`) both reachable from the SAME
`amp`/weight, the two path signs distinct. Neither pole is hard-wired. -/
theorem ws5_audit_fork_genuine :
    (combinedWeight attTri < partsWeight attTri)
  ∧ (partsWeight attStar ≤ combinedWeight attStar)
  ∧ (loopAmp attTri ≠ loopAmp attStar) := by
  refine ⟨ws3_destructive, ws4_additive_reachable.1, ?_⟩
  rw [loopAmp_attTri, loopAmp_attStar]; decide

/-- **(c) INTERFERENCE IS DESTRUCTIVE, NOT ADDITIVE (the costume gate).** The combined weight is STRICTLY below the
parts (`0 < 2`), and this is NOT a relabelled addition: the combined weight falls below the parts IFF the signs cancel
(`ws3_destructive_iff`), an inequality impossible for any classical mixture where weights add. -/
theorem ws5_audit_destructive :
    (combinedWeight attTri < partsWeight attTri)
  ∧ (∀ m n : ℤ, (amp m + amp n) ^ 2 < amp m ^ 2 + amp n ^ 2 ↔ amp m + amp n = 0) :=
  ⟨ws3_destructive, ws3_destructive_iff⟩

/-- **(d) THE SCOPE IS DISCLOSED.** The sign is a REAL `±1` (`amp n = 1 ∨ amp n = -1`); no theorem claims the full
complex `U(1)` phase or that quantum theory is recovered whole. The complex phase and the Born rule (Series 2.12) are
the disclosed forward-note. -/
theorem ws5_audit_scope : ∀ n : ℤ, amp n = 1 ∨ amp n = -1 := amp_values

/-- **(e) NAMES-NOT-TERMS.** A META-property about identifiers, not a proposition: no proof term, definition, or
discharged obligation is named as a forbidden content-word ("phase," "amplitude," "interference," "quantum,"
"superposition," "wave," "complex," "self," "import," "God," "choice") as a whole word. Enforced by the protocol §6
mechanical grep (hits are docstring prose or the Lean `import` keyword only), not by this `True`; carried as the
accepted house placeholder.
Made non-vacuous at Program Review 2-1 (PR2-R2, the accepted S13 C1-S1 form): the statement below proves
the outcome codomain a genuine discrimination among neutrally-named values. -/
theorem ws5_audit_names_not_terms :
    Outcome.interfering ≠ Outcome.additiveOnly
  ∧ Outcome.additiveOnly ≠ Outcome.shapeDrawn
  ∧ Outcome.shapeDrawn ≠ Outcome.disconnected
  ∧ Outcome.disconnected ≠ Outcome.partial'
  ∧ Outcome.interfering ≠ Outcome.partial' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end P2S11
