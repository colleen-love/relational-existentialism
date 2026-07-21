/-
`program-2/series-11/formal/P2S11/ws1.lean`

WS1 - The model-derived sign (the ground). Program 2 Series 11 (2.11), THE PHASE, the decisive quantum test.

Imports its predecessor `P2S8` (reaching `P2S7 / … / P2S0 / P1` transitively; the tier-1 probes `P2S9`/`P2S10` are
NOT imported, their content is not reused). It builds on Series 2.8's transitive API: chiefly the signed
directed-attention increment `incr` (the first quantity that CANCELS, `incr x y + incr y x = 0`) and the holonomy `hol`
(the net translation around a triangle), with the two carriers `attTri` (the frustrated 3-ring, `hol = 3`, odd) and
`attStar` (the gluable star, `hol = 0`, even).

This file fixes the ONE thing Series 2.11 adds, built FRESH and EARNED off the built holonomy, de-risked on paper first
(`spec/phase-derisking.md`):

- the sign `amp` — the parity sign of an integer, `amp n = if n % 2 = 0 then 1 else -1`, a `±1`-valued function; no
  complex number, no postulated phase;
- the two path signs `directAmp` (the direct/do-nothing path, `amp 0 = +1`) and `loopAmp att` (the around-the-ring
  path, `amp (hol att p0 p1 p2)`);
- the WEIGHT (the squared modulus): `combinedWeight` (the two paths combined then weighed) and `partsWeight` (the two
  paths weighed separately then summed).

WS1 proves the sign genuinely SIGNED (`ws1_amp_signed`): it takes both `+1` and `-1` on Series 2.8's carriers, so there
is a real sign to cancel. If no signed sign survived (the holonomy always even), the pre-registered obstruction is
toward ADDITIVE-ONLY / DISCONNECTED; it does not obtain (`attTri` is odd, `attStar` even).

Design docs: `program-2/series-11/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8

universe u

namespace P2S11

open P2S8

set_option linter.unusedVariables false

/-! ## The one added primitive: the parity SIGN read off the built holonomy -/

/-- **THE SIGN read off the holonomy.** `amp n = +1` when `n` is even, `-1` when `n` is odd: the parity sign of an
integer, a `±1`-valued function. Applied to a path's accumulated increment it is the sign that path contributes; along
a closed path the accumulated increment IS Series 2.8's holonomy. No complex number, no postulated phase, no free
parameter: the only input is an integer read off the built `hol`. Named `amp` in code (a neutral name; "amplitude" in
prose is the forbidden whole word, not "amp"). -/
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1

/-- **THE DIRECT-PATH SIGN.** The do-nothing path stays at the basepoint `p0`: accumulated increment `0`, sign
`amp 0 = +1`. -/
def directAmp : ℤ := amp 0

/-- **THE LOOP-PATH SIGN.** The around-the-ring path `p0 → p1 → p2 → p0` accumulates `hol att p0 p1 p2`; its sign is
`amp (hol att p0 p1 p2)`, read off the built holonomy. -/
def loopAmp (att : S → Finset S) : ℤ := amp (hol att p0 p1 p2)

/-- **THE COMBINED WEIGHT** (the squared modulus of the two paths combined). Genuine destructive interference is this
falling strictly below `partsWeight`. -/
def combinedWeight (att : S → Finset S) : ℤ := (directAmp + loopAmp att) ^ 2

/-- **THE PARTS WEIGHT** (the two paths weighed separately, summed). Each single sign has unit weight, so this is `2`. -/
def partsWeight (att : S → Finset S) : ℤ := directAmp ^ 2 + (loopAmp att) ^ 2

/-! ## The sign is a real `±1` (the scope, disclosed) -/

/-- **THE SIGN IS A REAL `±1`.** For every `n`, `amp n = 1 ∨ amp n = -1` (parity is `0` or `1`). The sign this series
earns is a REAL sign, not a complex `U(1)` phase; the complex phase is the disclosed forward-note. -/
theorem amp_values (n : ℤ) : amp n = 1 ∨ amp n = -1 := by
  unfold amp
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [if_pos h]
  · right; rw [if_neg (by omega)]

/-- **THE SQUARED MODULUS OF A SINGLE SIGN IS `1`.** Since `amp n ∈ {+1, -1}`, `(amp n)^2 = 1` — the unit weight each
single contribution carries. -/
theorem amp_sq (n : ℤ) : amp n ^ 2 = 1 := by
  rcases amp_values n with h | h <;> rw [h] <;> norm_num

/-! ## The sign takes both values on the S2.8 carriers -/

/-- The direct-path sign is `+1`. -/
theorem directAmp_eq : directAmp = 1 := by decide

/-- The loop-path sign on the FRUSTRATED ring is `-1` (its holonomy `3` is odd). -/
theorem loopAmp_attTri : loopAmp attTri = -1 := by
  show amp (hol attTri p0 p1 p2) = -1
  rw [ws4_frustrated_reachable.1]; decide

/-- The loop-path sign on the GLUABLE star is `+1` (its holonomy `0` is even). -/
theorem loopAmp_attStar : loopAmp attStar = 1 := by
  show amp (hol attStar p0 p1 p2) = 1
  rw [ws4_gluable_reachable.1]; decide

/-! ## The payoff -/

/-- **THE SIGN IS GENUINELY SIGNED (WS1).** The sign read off the built holonomy takes BOTH values on Series 2.8's
carriers: `-1` on the frustrated ring (odd holonomy `3`) and `+1` on the gluable star (even holonomy `0`). There is a
real sign to cancel; the series is not DISCONNECTED. This is the SAME Series 2.8 fork (frustrated vs gluable) read one
level up as a sign. -/
theorem ws1_amp_signed : loopAmp attTri = -1 ∧ loopAmp attStar = 1 :=
  ⟨loopAmp_attTri, loopAmp_attStar⟩

end P2S11
