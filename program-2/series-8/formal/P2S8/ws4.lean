/-
`program-2/series-8/formal/P2S8/ws4.lean`

WS4 - The frustration knot (the fork). Program 2 Series 8 (2.8).

The two sides of the gluing fork, both reachable on directed-attention carriers, neither by fiat.
`ws4_frustrated_reachable`: the directed 3-ring `attTri` has non-trivial triangle holonomy (`hol = 3`) and NO global
section — no single good consistent with every reconciliation at once — though every pair reconciles (WS2). This is
the value analog of Series 2.7's global failure: local coherence does NOT glue.
`ws4_gluable_reachable`: the mutual star `attStar` has vanishing holonomy (`hol = 0`) and a global section, which
restricts to the self's local good at the base. A world whose directed attention closes into no net cycle admits a
global good.

Frustration is not built into `hol` (the star gives `0`); gluing is not built in (the ring gives `3`): same `incr`,
same `hol`, only the directed attention differs. The fork is a fact about which world you are in.

Design docs: `program-2/series-8/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8.ws1

universe u

namespace P2S8

set_option linter.unusedVariables false

/-! ## Frustrated: the directed 3-ring -/

/-- **FRUSTRATED-REACHABLE (WS4).** The directed ring `attTri` has triangle holonomy `hol = 3 ≠ 0`, and NO global
section exists: any `s : S → ℤ` gluing the three ring edges would force `s p0 = s p0 + 3`, i.e. `0 = 3`. So there is
no global good, though every pair reconciles (WS2). Local coherence does not glue. -/
theorem ws4_frustrated_reachable :
    hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s := by
  refine ⟨by decide, ?_⟩
  rintro ⟨s, hs⟩
  have h01 : s p1 = s p0 + incr attTri p0 p1 := hs p0 p1 (by decide)
  have h12 : s p2 = s p1 + incr attTri p1 p2 := hs p1 p2 (by decide)
  have h20 : s p0 = s p2 + incr attTri p2 p0 := hs p2 p0 (by decide)
  have e01 : incr attTri p0 p1 = 1 := by decide
  have e12 : incr attTri p1 p2 = 1 := by decide
  have e20 : incr attTri p2 p0 = 1 := by decide
  rw [e01] at h01; rw [e12] at h12; rw [e20] at h20
  omega

/-! ## Gluable: the mutual star -/

/-- **GLUABLE-REACHABLE (WS4).** The mutual star `attStar` has triangle holonomy `hol = 0`, and the constant
assignment `s = 0` is a global section (every present edge carries `incr = 0`), restricting to the self's local good
at the base (`s p0 = valu attStar p0 = 0`). A global good exists. -/
theorem ws4_gluable_reachable :
    hol attStar p0 p1 p2 = 0
  ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0) := by
  refine ⟨by decide, fun _ => 0, ?_, by decide⟩
  intro x y hy
  have hz : incr attStar x y = 0 := by revert hy; fin_cases x <;> fin_cases y <;> decide
  show (0 : ℤ) = 0 + incr attStar x y
  omega

end P2S8
