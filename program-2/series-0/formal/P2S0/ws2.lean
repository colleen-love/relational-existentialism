/-
`program-2/series-0/formal/P2S0/ws2.lean`

WS2 - The inherited collapse (baseline, transcription, NOT relitigation). Program 2 Series 0 (2.0).

Without the import, the atomless symmetric world is the One. This is Program 1's theorem, INHERITED here
as baseline by APPLYING the imported P1 collapse engine `P1.Core.ws2_import_theorem_static` to the symmetric
relating `symDest` (WS1). It is NOT re-proved; the proof term IS the imported engine. Stated as the ground
the import (WS4) acts against, in one line; no series verdict hinges on it (audit (d), certified in WS5).

Design docs: `program-2/series-0/spec/ws2-design.md`; shared objects `spec/README.md` §2.1-§2.2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S0.ws1

universe u

namespace P2S0

open P1.Core Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **THE INHERITED COLLAPSE (baseline).** Without the import, the atomless, behaviorally-identified
symmetric world is a subsingleton: the One. The imported P1 engine (`ws2_import_theorem_static`), applied to
`symDest`. `hcar : mk X < κ` is the ambient carrier-size hypothesis for the symmetric reduct's possibly
infinite in-attention neighborhoods (audit (a)), never an ontological ceiling. -/
theorem ws2_collapse_inherited (hinf : ℵ₀ ≤ κ) {X : Type u} (hcar : Cardinal.mk X < κ)
    (attends : X → Finset X)
    (hbehav : BehaviorallyIdentified (symDest hinf hcar attends))
    (hatom : ∀ x, SHNE (symDest hinf hcar attends) x) : Subsingleton X :=
  ws2_import_theorem_static (symDest hinf hcar attends) hbehav hatom

end P2S0
