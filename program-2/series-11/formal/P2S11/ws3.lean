/-
`program-2/series-11/formal/P2S11/ws3.lean`

WS3 - Interference, not accumulation (the anti-costume core). Program 2 Series 11 (2.11).

The WEIGHT (defined in `ws1`) is the squared modulus of a combined sign. WS3 proves genuine DESTRUCTIVE INTERFERENCE:
a combined weight STRICTLY below the sum of the parts (`ws3_destructive`: `combinedWeight attTri = 0 < 2 =
partsWeight attTri`), the quantum signature no classical mixture shows (classically weights add, so `combined ≥
parts`). It proves this is NOT additive bookkeeping (`ws3_destructive_iff`: the combined weight falls below the parts
IFF the signs cancel — impossible for a classical mixture, and happening exactly on odd relative holonomy). And it
proves the sign EARNED (`ws3_amp_earned`: the sign is a function of the built `incr`/`hol`, definitionally — no complex
number, the no-smuggling gate, sharpest in the program).

Design docs: `program-2/series-11/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11.ws1

universe u

namespace P2S11

open P2S8

set_option linter.unusedVariables false

/-! ## Destructive interference on the frustrated cycle -/

/-- **DESTRUCTIVE INTERFERENCE (WS3).** On the FRUSTRATED cycle the direct and loop paths carry opposite signs, so the
combined weight is STRICTLY below the sum of the parts: `combinedWeight attTri = (1 + (-1))^2 = 0 < 2 = 1^2 + (-1)^2 =
partsWeight attTri`. Two ways of reaching `p0`, combined, make the arriving LESS likely than either alone — the
signature no classical probability can show. The strict inequality is the whole content. -/
theorem ws3_destructive : combinedWeight attTri < partsWeight attTri := by
  unfold combinedWeight partsWeight
  simp only [directAmp_eq, loopAmp_attTri]
  norm_num

/-! ## The anti-costume theorem: destructive IFF the signs cancel -/

/-- **DESTRUCTIVE IFF THE SIGNS CANCEL (WS3).** Each sign has unit weight (`amp _ ^ 2 = 1`), so the parts weight is `2`
and the combined weight `(amp m + amp n)^2 ∈ {0, 4}`; it falls below `2` IFF `amp m + amp n = 0`. So a combined weight
below the parts is NOT a relabelled addition — it is exactly the cancellation of the signs, impossible for any
classical mixture (where weights add). Combined with `ws2_amp_cancels_general`, destructive interference happens
EXACTLY when the two path holonomies differ in parity (odd relative holonomy). -/
theorem ws3_destructive_iff (m n : ℤ) :
    (amp m + amp n) ^ 2 < amp m ^ 2 + amp n ^ 2 ↔ amp m + amp n = 0 := by
  rcases amp_values m with hm | hm <;> rcases amp_values n with hn | hn <;>
    rw [hm, hn] <;> norm_num

/-! ## The sign is earned off the built holonomy -/

/-- **THE SIGN IS EARNED, NOT SMUGGLED (WS3, the no-smuggling gate, sharpest in the program).** The sign is a function
of the built `incr`/`hol`, definitionally: (1) `loopAmp` unfolds to `amp (hol …)`; (2) `hol` is Series 2.8's
`incr`-sum around the triangle; (3) `incr` is Series 2.8's signed `knows` difference. No complex number, no postulated
phase, no free parameter anywhere. The strip test leaves `(a+b)^2 < a^2 + b^2` for the signs `a, b` read off the built
holonomy. -/
theorem ws3_amp_earned :
    (∀ att : S → Finset S, loopAmp att = amp (hol att p0 p1 p2))
  ∧ (∀ (att : S → Finset S) (x y z : S),
        hol att x y z = incr att x y + incr att y z + incr att z x)
  ∧ (∀ (att : S → Finset S) (x y : S),
        incr att x y = (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)) :=
  ⟨fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end P2S11
