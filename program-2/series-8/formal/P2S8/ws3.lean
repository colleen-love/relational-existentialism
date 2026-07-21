/-
`program-2/series-8/formal/P2S8/ws3.lean`

WS3 - The obstruction is genuinely many-body (the anti-costume core). Program 2 Series 8 (2.8).

The holonomy `hol` (defined in `ws1`) is the net translation of the composed reconciliation around a triangle. WS3
proves it a GENUINE many-body phenomenon on two fronts:
(i) `ws3_two_body_trivial` — it VANISHES for two selves (`incr x y + incr y x = 0`, and any 2-body cycle has zero
    holonomy), so this is not Series 2.3's single edge replayed;
(ii) `ws3_holonomy_model_derived` — `incr` is exactly the signed `knows` difference (a function of the attention
    alone), and if the attention is made SYMMETRIC the holonomy vanishes identically, so the obstruction lives in the
    DIRECTEDNESS (the knowing-asymmetry) and cannot be a bolted-on gadget indifferent to it (the T1-S1 trap); and the
    frustrating carrier `attTri` is genuinely directed.

`hol` never mentions `Recoverable`/`plainOf`/`AttentionDistinguishes`: the obstruction is a network/axis cocycle, not
import-ness. Both costume fronts of the doubled gate are cleared.

Design docs: `program-2/series-8/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8.ws1

universe u

namespace P2S8

open P2S0

set_option linter.unusedVariables false

/-! ## The obstruction vanishes for two selves -/

/-- **THE HOLONOMY VANISHES FOR TWO SELVES (WS3).** `incr` is antisymmetric (`incr x y + incr y x = 0`), and any
two-body cycle (`hol x y x`, `hol x x y`) has zero holonomy — for EVERY attention. The obstruction is invisible on a
single edge: not Series 2.3 replayed. -/
theorem ws3_two_body_trivial (att : S → Finset S) (x y : S) :
    incr att x y + incr att y x = 0 ∧ hol att x y x = 0 ∧ hol att x x y = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hol, incr] <;> ring

/-! ## The obstruction is model-derived: carried by the directedness -/

/-- **THE HOLONOMY IS MODEL-DERIVED (WS3).** (1) `incr` IS the signed `knows` difference — a function of the
attention alone (no free parameter, no counter disconnected from the attention). (2) Make the attention SYMMETRIC
(`x∈att y ↔ y∈att x`, the direction-blind reduct) and ALL holonomy vanishes: the obstruction is carried entirely by
the DIRECTEDNESS (the knowing-asymmetry), so a bolted-on gadget indifferent to `att`'s symmetry could not produce it
(the T1-S1 trap foreclosed). (3) The frustrating carrier `attTri` is genuinely directed (a one-way edge). -/
theorem ws3_holonomy_model_derived :
    (∀ (att : S → Finset S) (x y : S),
        incr att x y = (if knows att x y then 1 else 0) - (if knows att y x then 1 else 0))
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro att x y; rfl
  · intro att hsym x y z
    have hz : ∀ a b : S, incr att a b = 0 := by
      intro a b
      simp only [incr]
      by_cases h : b ∈ att a
      · rw [if_pos h, if_pos ((hsym a b).mpr h)]; ring
      · rw [if_neg h, if_neg (fun hc => h ((hsym a b).mp hc))]; ring
    have a1 := hz x y; have a2 := hz y z; have a3 := hz z x
    simp only [hol]; omega
  · exact ⟨p0, p1, by decide, by decide⟩

end P2S8
