/-
`program-2/series-1/formal/P2S1/ws3.lean`

WS3 - The stream and the tick (the exogeneity knot). Program 2 Series 1 (2.1).

The stream IS S0's seated import `impLift`, located at the tick's choice-point (which of the two available
closures fires), per charter §3 ("the stream generalizing S0's `impLift` into succession"). The two available
closures are encoded as `Bool`. The choice is proved non-recoverable from the plain relating
(`ws3_stream_exogenous`, the reused `ws4_import_breaks_baseline`, quantified over ALL import value-spaces and
functions, none named) and load-bearing (`ws3_tick_needs_stream`: the plain projection identifies the options,
so without the stream the closure is not determinate - the collapse to the One). No proof term names the choice
(audit (e)).

Design docs: `program-2/series-1/spec/ws3-design.md`; shared objects `spec/README.md` §1-§2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE STREAM IS EXOGENOUS (audit (b), WS3).** For ALL import value-spaces `Q` and import functions `f`,
whenever `f` genuinely differs on the two available closures, the plain relating IDENTIFIES them (the options
are not distinguished by the relating) yet the exogenous choice SEPARATES them (not label-recoverable). The
choice the tick draws from the stream is non-recoverable from the plain relating: the reused
`ws4_import_breaks_baseline`, quantified, no import named. -/
theorem ws3_stream_exogenous (hinf : ℵ₀ ≤ κ) :
    ∀ {Q : Type} (f : Bool → Q), f true ≠ f false →
        (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R true false)
      ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false) := by
  intro Q f hf
  exact ws4_import_breaks_baseline hinf f hf

/-- **THE TICK NEEDS THE STREAM (WS3).** The plain projection identifies the two available closures (the
collapse - without the import they are behaviorally one), and the identity import (the canonical non-choice,
not a content-name) is non-recoverable. Together: the stream's entry is what makes the closure determinate, an
obligation not a cosmetic. If the choice were recoverable the dynamics would be the deterministic-relational
One (Series 07). -/
theorem ws3_tick_needs_stream (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (impLift hinf (id : Bool → Bool))) R ∧ R true false)
  ∧ (¬ Recoverable (impLift hinf (id : Bool → Bool))) := by
  refine ⟨⟨(fun _ _ => True), plainOf_impLift_true_bisim hinf id, trivial⟩, (ws4_import_quantified hinf).2⟩

end P2S1
