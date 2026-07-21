/-
`program-2/series-11/formal/P2S11/ws2.lean`

WS2 - Cancellation (the raw material). Program 2 Series 11 (2.11).

The sign `amp` (defined in `ws1`) carries Series 2.8's antisymmetry (`incr x y + incr y x = 0`) up to a weight-bearing
sign. WS2 proves two contributions with OPPOSITE sign SUM TO ZERO: in the frustrated world the direct path (`+1`) and
the loop path (`-1`) cancel (`ws2_amp_cancels`), and generally any two integers of opposite parity give signs summing
to zero (`ws2_amp_cancels_general`, so the cancellation is not a coincidence of two chosen carriers). This is the first
subtraction in the program's dynamics carried to a sign — necessary for interference, but NOT sufficient: the WEIGHT
must fall below the parts (WS3).

Design docs: `program-2/series-11/spec/ws2-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11.ws1

universe u

namespace P2S11

open P2S8

set_option linter.unusedVariables false

/-! ## The general cancellation criterion (opposite parity ⇒ the signs cancel) -/

/-- **OPPOSITE PARITY ⇒ THE SIGNS CANCEL (WS2).** For any two integers `m, n` of opposite parity (`(m + n) % 2 = 1`),
one is even (sign `+1`) and the other odd (sign `-1`), so `amp m + amp n = 0`. Genuine subtraction, earned — not two
hand-picked values. -/
theorem ws2_amp_cancels_general (m n : ℤ) (h : (m + n) % 2 = 1) : amp m + amp n = 0 := by
  have hm := Int.emod_two_eq_zero_or_one m
  have hn := Int.emod_two_eq_zero_or_one n
  simp only [amp]
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · exfalso; omega
  · rw [if_pos hm, if_neg (by omega)]; ring
  · rw [if_neg (by omega), if_pos hn]; ring
  · exfalso; omega

/-! ## The concrete cancellation on the frustrated world -/

/-- **THE TWO PATHS CANCEL (WS2).** In the FRUSTRATED world the direct path (`directAmp = +1`) and the loop path
(`loopAmp attTri = -1`) carry opposite signs and SUM TO ZERO: two ways of arriving at `p0` subtract. Carried from
Series 2.8's antisymmetry (`incr x y + incr y x = 0`), now read through the sign. -/
theorem ws2_amp_cancels : directAmp + loopAmp attTri = 0 := by
  rw [directAmp_eq, loopAmp_attTri]; ring

end P2S11
