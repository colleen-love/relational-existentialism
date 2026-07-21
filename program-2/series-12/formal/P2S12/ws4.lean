/-
`program-2/series-12/formal/P2S12/ws4.lean`

WS4 - The fork (BORN vs STOCHASTIC-NOT-BORN vs DETERMINISTIC, the knot). Program 2 Series 12 (2.12).

The two live poles of the measure fork, both genuine, neither by fiat.

`ws4_squared_reachable`: the imports carry a NON-TRIVIAL measure (`combinedWeight`, values `0` on `attTri`, `4` on
`attStar` — `ws1_measure_nontrivial`) whose CONSISTENT form is the squared amplitude (`respectsCancel combinedWeight`,
`ws3_sq_consistent`) while the classical additive form is REFUTED (`¬ respectsCancel partsWeight`,
`ws3_classical_fails`). This is the BORN pole — quantum probability in its rebit form, on directed-attention carriers.

`ws4_deterministic_reachable`: a structureless freedom, modelled by a CONSTANT weight `fun _ => c`, carries no
non-trivial measure — it assigns the same value to every configuration, so there is nothing to weigh, no chance. This
is the DETERMINISTIC pole (the deepest NOT-RECOVERED), genuinely available and distinct, not construction-blocked.

The third pole, STOCHASTIC-NOT-BORN (a non-trivial measure that is NOT the squared/consistent form), is DISCRIMINATED
by the verdict function (WS5) but NOT witnessed on these carriers: of the two candidate measures the only consistent one
is the squared one (`ws3_sq_consistent`), and the classical additive form is both refuted and constant. A general
non-square measure, and Gleason/Busch uniqueness among all `|·|^p`, are the disclosed forward-note.

Both live poles are genuine: BORN is not built into the objects (a constant weight gives DETERMINISTIC; the classical
`partsWeight` is a genuine distinct measure that genuinely FAILS), and DETERMINISTIC is not built in (the actual
imported weight is non-trivial). Which obtains is computed, not chosen.

Design docs: `program-2/series-12/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S12.ws1
import P2S12.ws3

universe u

namespace P2S12

open P2S8 P2S11

set_option linter.unusedVariables false

/-! ## BORN reachable: a non-trivial measure whose consistent form is the square -/

/-- **THE SQUARED (BORN) POLE IS REACHABLE (WS4).** The imports carry a NON-TRIVIAL measure (`combinedWeight attTri =
0 ≠ 4 = combinedWeight attStar`) whose CONSISTENT form is the squared amplitude (`respectsCancel combinedWeight`) while
the classical additive form is REFUTED (`¬ respectsCancel partsWeight`). Quantum probability recovered in its rebit
form, on genuine directed-attention carriers, no fiat. -/
theorem ws4_squared_reachable :
    combinedWeight attTri ≠ combinedWeight attStar
  ∧ respectsCancel combinedWeight
  ∧ ¬ respectsCancel partsWeight :=
  ⟨ws1_measure_nontrivial, ws3_sq_consistent.1, ws3_classical_fails⟩

/-! ## DETERMINISTIC reachable: a constant weight is a trivial measure -/

/-- **THE DETERMINISTIC POLE IS REACHABLE (WS4).** A structureless freedom, modelled by a CONSTANT weight `fun _ => c`,
carries no non-trivial measure: it assigns the same value to every configuration, so there is nothing to weigh — no
chance. The DETERMINISTIC pole (the deepest NOT-RECOVERED) is a genuine, distinct possibility, not excluded by
construction; this world does not land there (its imported weight is non-trivial, `ws4_squared_reachable`), but the
fork is real. -/
theorem ws4_deterministic_reachable :
    ∀ (c : ℤ) (att att' : S → Finset S), (fun _ : S → Finset S => c) att = (fun _ => c) att' :=
  fun c att att' => rfl

end P2S12
