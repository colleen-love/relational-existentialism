/-
`program-2/series-12/formal/P2S12/ws3.lean`

WS3 - The Born form is forced, not named (the anti-costume core). Program 2 Series 12 (2.12).

The clause the series lives or dies on. Two candidate measures assign a weight to a combined outcome from the two path
amplitudes: the SQUARE-then-ADD form (the imported `partsWeight`, a classical additive probability — square each
amplitude, then sum over the ways) and the ADD-then-SQUARE form (the imported `combinedWeight`, the squared modulus of
the summed amplitudes). WS3 adds ONE thing — a FORM-AGNOSTIC consistency predicate `respectsCancel`, the demand that a
measure vanish wherever the amplitudes cancel ("cancellation is absence") — and proves:

- `ws3_classical_fails`: the square-then-add form does NOT respect the cancellation — on the frustrated cycle the
  amplitudes cancel (`ws2_amp_cancels`) yet `partsWeight attTri = 2 ≠ 0`. The classical additive probability
  CONTRADICTS the interference: refuted, not excluded by fiat.
- `ws3_sq_consistent`: the add-then-square form DOES respect the cancellation (it is `0` wherever the amplitudes sum to
  `0`, for every configuration) and is non-negative — a genuine candidate probability.
- `ws3_sq_forced`: the add-then-square form is consistent while the square-then-add form is not, and they DISAGREE on
  the interfering configuration (`0 ≠ 2`). The consistent measure is the squared one, FORCED by the test.
- `ws3_sq_earned`: the add-then-square form is a function of the built `amp`/`hol`/`incr`, definitionally — no complex
  number, no probability defined (the no-smuggling gate, sharpest in the program).

`respectsCancel`'s body mentions NO square: the squared form is the RESIDUE of a form-agnostic test, never a definition.

Design docs: `program-2/series-12/spec/ws3-design.md`; paper gate `spec/born-derisking.md` §3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11

universe u

namespace P2S12

open P2S8 P2S11

set_option linter.unusedVariables false

/-! ## The one added primitive: the form-agnostic consistency predicate -/

/-- **THE CONSISTENCY PREDICATE.** A candidate measure `μ` RESPECTS the cancellation if it assigns weight `0` wherever
the two path amplitudes cancel. The body mentions no square, no `combinedWeight`: it is the bare demand that a
probability vanish on the interference ("cancellation is absence"). The squared form will be SELECTED by this predicate
(it satisfies it while the classical additive form fails it), never defined into it. -/
def respectsCancel (μ : (S → Finset S) → ℤ) : Prop :=
  ∀ att, directAmp + loopAmp att = 0 → μ att = 0

/-! ## The classical additive form is refuted -/

/-- **THE CLASSICAL ADDITIVE FORM IS REFUTED (WS3).** The square-then-add measure `partsWeight` does NOT respect the
cancellation: on the frustrated cycle the amplitudes cancel (`ws2_amp_cancels : directAmp + loopAmp attTri = 0`) yet
`partsWeight attTri = 1^2 + (-1)^2 = 2 ≠ 0`. The classical additive probability insists the outcome occurs (weight `2`)
where the interference has cancelled its amplitude to nothing (weight `0`). It CONTRADICTS the built structure —
refuted by an explicit witness, not excluded by fiat. -/
theorem ws3_classical_fails : ¬ respectsCancel partsWeight := by
  intro h
  have hz : partsWeight attTri = 0 := h attTri ws2_amp_cancels
  unfold partsWeight at hz
  simp only [directAmp_eq, loopAmp_attTri] at hz
  norm_num at hz

/-! ## The add-then-square form is consistent -/

/-- **THE SQUARED FORM IS CONSISTENT (WS3).** The add-then-square measure `combinedWeight` respects the cancellation —
wherever the amplitudes sum to `0`, `combinedWeight att = (directAmp + loopAmp att)^2 = 0^2 = 0`, for EVERY
configuration (not just `attTri`) — and it is non-negative (a square). A genuine candidate probability that vanishes
exactly on the interference. -/
theorem ws3_sq_consistent : respectsCancel combinedWeight ∧ ∀ att, 0 ≤ combinedWeight att := by
  refine ⟨?_, ?_⟩
  · intro att h
    unfold combinedWeight
    rw [h]
    norm_num
  · intro att
    unfold combinedWeight
    exact sq_nonneg _

/-! ## The squared form is FORCED, the classical refuted -/

/-- **THE SQUARED FORM IS FORCED, NOT DEFINED (WS3).** The add-then-square form respects the cancellation while the
square-then-add form does not, and the two DISAGREE on the interfering configuration (`combinedWeight attTri = 0 ≠ 2 =
partsWeight attTri`). The consistent measure is the squared one — the RESIDUE of the form-agnostic test, not its
premise; the classical additive form is refuted. Nothing defines the probability as `|amp|²`. (Scope: this forces the
square as the consistent one of the TWO candidate measures, not the unique one among all `|·|^p` — the disclosed
forward-note; see `ws5_audit_scope`.) -/
theorem ws3_sq_forced :
    respectsCancel combinedWeight
  ∧ ¬ respectsCancel partsWeight
  ∧ combinedWeight attTri ≠ partsWeight attTri := by
  refine ⟨ws3_sq_consistent.1, ws3_classical_fails, ?_⟩
  unfold combinedWeight partsWeight
  simp only [directAmp_eq, loopAmp_attTri]
  norm_num

/-! ## The squared form is earned off the built holonomy -/

/-- **THE SQUARED FORM IS EARNED, NOT SMUGGLED (WS3, the no-smuggling gate, sharpest in the program).** The
add-then-square weight is a function of the built `amp`/`hol`/`incr`, definitionally: (1) `combinedWeight` unfolds to
`(directAmp + loopAmp att)^2`; (2) `loopAmp` unfolds to `amp (hol …)`, itself Series 2.8's `incr`-sum. No complex
number, no postulated probability, no free parameter. The strip test leaves the bare consistency fact on the signs read
off the built holonomy. Mirrors `P2S11.ws3_amp_earned` one level up. -/
theorem ws3_sq_earned :
    (∀ att : S → Finset S, combinedWeight att = (directAmp + loopAmp att) ^ 2)
  ∧ (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end P2S12
