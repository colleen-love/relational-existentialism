/-
`program-2/series-5/formal/P2S5/ws1.lean`

WS1 - The fold and the poles (the ground). Program 2 Series 5 (2.5), the blocking workstream.

Imports `P2S4` (the layered chain; `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` reached transitively). Builds the
topology of the whole on the P1 diagonal: NO SMALLEST (atomlessness, every reachable node `SHNE`, nothing bottoms
out), NO LARGEST (the reification section yields from any relatum a higher relatum, coinciding with it only at a
self-membered point), THE FOLD (the totalizing self-inspection misses the residue point it produces, and the
self-total seam is unrealizable, `ws2_residue_distinct` / `ws1_no_self_total_hold`), and the number-face (the
whole cannot count itself, `ws1_insp_not_surjective`). The fold rests on the diagonal, NOT on a seated import.

Design docs: `program-2/series-5/spec/ws1-design.md`; shared objects `spec/README.md` §2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S4

universe u

namespace P2S5

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

/-! ## No smallest, no largest (the poles) -/

/-- **NO SMALLEST (WS1).** Nothing bottoms out: every reachable node of the tick carrier has a nonempty
successor set (`SHNE`). Atomlessness, reachability-relative, no absolute floor. -/
theorem ws1_no_pole_below (hinf : ℵ₀ ≤ κ) (x : TCar) : SHNE (outDest hinf attendsT) x :=
  ws1_tcar_SHNE hinf x

/-- **NO LARGEST (WS1).** Reification is unbounded: from any relatum `x`, a total finite section produces a
relatum `reify {x}` whose sole constituent is `x` (a higher reified relatum), coinciding with `x` ONLY at a
self-membered point (`attends x = {x}`). No absolute ceiling; the one obstruction to ascent is the fold. -/
theorem ws1_no_pole_above {X : Type u} (attends : X → Finset X) (reify : Finset X → X)
    (h : FinReify attends reify) (x : X) :
    attends (reify {x}) = {x} ∧ (reify {x} = x → attends x = {x}) :=
  ⟨h {x}, fun he => by have hx := h {x}; rw [he] at hx; exact hx⟩

/-- **THE SECTION IS NON-VACUOUS.** A carrier with a total finite reification section exists (an infinite carrier
where `Finset X ≃ X`), so `ws1_no_pole_above` is discharged non-vacuously. -/
theorem ws1_reify_nonvacuous :
    ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X),
      FinReify attends reify ∧ Function.Injective reify :=
  ws1_reification_exists

/-! ## The fold and the number-face (the diagonal) -/

/-- **THE FOLD (WS1), drawn by the diagonal.** The totalizing self-inspection produces a residue point that NO
hold realises (`ws2_residue_distinct` — the largest act yields the smallest object it cannot contain), and the
self-total seam is unrealizable (`ws1_no_self_total_hold`). Rests on the P1 diagonal, not on an import. -/
theorem ws1_fold {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (∀ h, insp h ≠ residue insp) ∧ (¬ ∃ t, SelfTotal insp t) :=
  ⟨ws2_residue_distinct dest insp, ws1_no_self_total_hold dest insp⟩

/-- **THE NUMBER-FACE (WS1).** The whole cannot count itself: no inspection is surjective onto its content-space
(Cantor, from the diagonal). -/
theorem ws1_no_total_count {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ Function.Surjective insp :=
  ws1_insp_not_surjective dest insp

end P2S5
