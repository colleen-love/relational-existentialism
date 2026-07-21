/-
`program-2/series-12/formal/P2S12/ws1.lean`

WS1 - The outcomes and the imports (the ground). Program 2 Series 12 (2.12), THE WEIGHT, the second half of the
quantum recovery.

Imports its predecessor `P2S11` (reaching `P2S8 / P2S7 / … / P2S0 / P1` transitively; the tier-1 probes
`P2S9`/`P2S10` are NOT imported, their content is not reused). It builds on Series 2.11's transitive API: the sign
`amp`, the two path signs `directAmp`/`loopAmp`, and the two candidate combined weights `combinedWeight` (add-then-
square) and `partsWeight` (square-then-add) — the amplitude-carrying configurations whose weight this series reads as
a probability carried by the imports (the out-of-image differentiator, `P2S0`/`P1`, a permanent open).

WS1 fixes the GROUND: it reads the two Series 2.8 carriers as the OUTCOMES the imports select between and proves the
setup NON-TRIVIAL — there are genuinely distinct outcomes with distinct amplitudes (`ws1_outcomes_nontrivial`), and
the candidate weight over them is non-constant (`ws1_measure_nontrivial`), so there is something to weigh. If the
amplitudes were constant, or the weight constant, the pre-registered obstruction is toward DETERMINISTIC (interference
without chance); it does not obtain (the frustrated/gluable fork gives distinct amplitudes `-1`/`+1` and a non-trivial
weight `0`/`4`).

Design docs: `program-2/series-12/spec/ws1-design.md`; shared objects `spec/README.md` §2; paper gate
`spec/born-derisking.md` §4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S11

universe u

namespace P2S12

open P2S8 P2S11

set_option linter.unusedVariables false

/-! ## The outcomes are genuinely distinct (distinct amplitudes) -/

/-- **THE OUTCOMES ARE NON-TRIVIAL (WS1).** The loop-path sign differs across the two carriers the imports select
between: `loopAmp attTri = -1 ≠ 1 = loopAmp attStar` (Series 2.11's `ws1_amp_signed`, the frustrated/gluable fork read
one level up). There is a real distinction to weigh; the setup is not degenerate. -/
theorem ws1_outcomes_nontrivial : loopAmp attTri ≠ loopAmp attStar := by
  rw [loopAmp_attTri, loopAmp_attStar]; decide

/-! ## The candidate weight over the outcomes is non-constant (the chance question) -/

/-- **THE CANDIDATE WEIGHT IS NON-TRIVIAL (WS1).** The add-then-square weight takes DISTINCT values on the two
possibilities the free differentiator selects between: `combinedWeight attTri = 0 ≠ 4 = combinedWeight attStar`. So the
freedom is genuinely WEIGHTED — a non-trivial candidate measure over the outcomes, the ground of genuine chance. Its
failure (a constant weight) would be the DETERMINISTIC obstruction; it does not obtain. -/
theorem ws1_measure_nontrivial : combinedWeight attTri ≠ combinedWeight attStar := by
  unfold combinedWeight
  simp only [directAmp_eq, loopAmp_attTri, loopAmp_attStar]
  decide

end P2S12
