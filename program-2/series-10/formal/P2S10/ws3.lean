/-
`program-2/series-10/formal/P2S10/ws3.lean`

WS3 - Decodability is not reversal, and the core criterion (the crux). Program 2 Series 10 (2.10).

Imports `P2S10.ws1`. Two things.

(i) `ws3_section_not_measure_preserving`: the reification SECTION (`attendsM`, a right-inverse) RECOVERS the reified
pattern (`attendsM (reifyM {e0}) = {e0}`) but does NOT preserve the built measure (`mu (reifyM {e0}) = mu e0 + 1 ≠ mu
e0`). So decodability is strictly weaker than a dynamical reversal — recovering the pattern does not lower the rank the
tick raised. Passing the section off as a reversal is the look-alike (the exact Series 2.7 lesson). (The section has
type `Cfg → Finset Cfg` — state to pattern — so it is not even an iterable state sub-dynamics; the measure conjunct is
the operative fact.)

(ii) The CORE CRITERION `IsCore`: a genuine reversible core is a sub-domain `D` on which the map is a MEASURE-
PRESERVING BIJECTION — closed, surjective onto `D`, injective on `D` (⇒ a bijection of the finite `D`), AND rank-
preserving. BOTH clauses required; bijectivity that raises the rank is not a core, and the decodable section is a
weaker, different thing. `ws3_core_criterion` records that `IsCore` entails the full higher bar (rank-preservation AND
injectivity) and is SATISFIABLE on the built rank (the control swap `tickR` has the core `{e0,e0'}`), so WS4's search
on the built tick is a genuine test.

Design docs: `program-2/series-10/spec/ws3-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S10.ws1

universe u

namespace P2S10

open P2S7

set_option linter.unusedVariables false

/-! ## (i) The section decodes but does not preserve the measure -/

/-- **THE SECTION DECODES BUT DOES NOT PRESERVE THE MEASURE (WS3.i, the costume gate).** The section is a
right-inverse on the pattern (`attendsM (reifyM {e0}) = {e0}` — it recovers the reified constituent), YET the tick that
produced the reified state raised the built rank (`mu (reifyM {e0}) = mu e0 + 1 ≠ mu e0`). Decodability is strictly
weaker than a dynamical reversal; passing the section off as a reversal is the Series 2.7 look-alike. -/
theorem ws3_section_not_measure_preserving :
    attendsM (reifyM {e0}) = {e0}
  ∧ mu (reifyM {e0}) = mu e0 + 1
  ∧ mu (reifyM {e0}) ≠ mu e0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## (ii) The core criterion (the higher bar) -/

/-- **A CONTROL SUB-DYNAMICS.** The relabelling swap of the two rank-0 states (`e0 ↔ e0'`), fixing the rest. NOT the
built tick and NOT an inverse of it — the positive witness that the core criterion is satisfiable on the built rank. -/
def tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x

/-- **THE CORE CRITERION.** A genuine reversible core is a sub-domain `D` on which `t` is a MEASURE-PRESERVING
BIJECTION: closed, surjective onto `D`, injective on `D` (closure + surjectivity + injectivity on a finite `D` ⇒ a
bijection `D → D`), AND rank-preserving (`m (t x) = m x`). BOTH clauses are required; `m` is the built rank. -/
def IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D)
  ∧ (D.image t = D)
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y)
  ∧ (∀ x ∈ D, m (t x) = m x)

/-- Decidability (so WS4's `ws4_no_core_built` / `ws4_core_reachable` discharge by `decide` over `Finset Cfg`). -/
instance decIsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Decidable (IsCore t m D) := by
  unfold IsCore; infer_instance

/-- **THE CRITERION IS GENUINE AND SATISFIABLE (WS3.ii).** (a) `IsCore` ENTAILS the full higher bar — both
rank-preservation and injectivity (a measure-preserving bijection), not decodability. (b) It is SATISFIABLE on the
built rank by a genuine dynamics: the relabelling swap `tickR` has the measure-preserving bijective core `{e0, e0'}`.
So the criterion is real, not vacuous; WS4 tests whether the BUILT tick meets it. -/
theorem ws3_core_criterion :
    (∀ t m D, IsCore t m D →
        (∀ x ∈ D, m (t x) = m x)
      ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y))
  ∧ (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D) := by
  refine ⟨fun t m D h => ⟨h.2.2.2, h.2.2.1⟩, ⟨{e0, e0'}, ⟨e0, by decide⟩, by decide⟩⟩

end P2S10
