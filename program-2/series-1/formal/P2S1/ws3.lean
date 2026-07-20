/-
`program-2/series-1/formal/P2S1/ws3.lean`

WS3 - The stream and the tick (the exogeneity knot). Program 2 Series 1 (2.1).

**Charter Extension 1 (EXT-F1, R2): the stream lives at the tick's choice-point ON THE REAL CARRIER `TCar`.**
The first build reused S0's generic `impLift` on `Bool`, disconnected from the tick machinery. The rebuild puts
the stream's choice on `TCar`: which of the concurrent available closures `kA`, `kB` the tick draws is an
exogenous label `ch : TCar → ℕ` distinguishing them. The two closures are plain-bisimilar on the real carrier
(the collapse engine on `outDest attendsT`) - the relating does not force which fires - so the choice is
non-recoverable (`ws3_stream_exogenous`), quantified over all such labels, never named; and load-bearing
(`ws3_tick_needs_stream`: the closures are plain-identified, so without the stream the choice is indeterminate).
The stream stays NON-RECOVERABLE - a recoverable choice would collapse the dynamics to the One (Series 07). This
reuses the WS4-linearization pattern for the choice; WS4 itself is untouched.

Design docs: `program-2/series-1/spec/ws3-design.md`; charter extension `charter-extension.md` R2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE STREAM IS EXOGENOUS, TICK-SPECIFIC (audit (b), WS3; Ext-1 R2).** The choice among the concurrent
available closures `kA`, `kB` is an exogenous label `ch : TCar → ℕ` on the REAL carrier. For every `ch`
distinguishing them: the two closures are plain-bisimilar (the collapse engine, `ch`-independent - the relating
does not force which fires) yet the choice separates them, so the choice is NOT recoverable from the plain
relating. Quantified over all `ch`, never named. This is the tick's actual choice-point on `TCar`. -/
theorem ws3_stream_exogenous (hinf : ℵ₀ ≤ κ) :
    ∀ ch : TCar → ℕ, ch kA ≠ ch kB →
        AttentionDistinguishes (rankLift (outDest hinf attendsT) ch) kA kB
      ∧ (¬ Recoverable (rankLift (outDest hinf attendsT) ch)) := by
  intro ch hch
  have hdist : AttentionDistinguishes (rankLift (outDest hinf attendsT) ch) kA kB := by
    refine ⟨?_, ?_⟩
    · rw [plainOf_rankLiftT]
      exact ws1_atomless_bisim (outDest hinf attendsT) kA kB (ws1_tcar_SHNE hinf kA) (ws1_tcar_SHNE hinf kB)
    · rintro ⟨R, hR, hRel⟩
      obtain ⟨hfwd, _⟩ := hR kA kB hRel
      have hedge : ((⟨ch kA⟩ : ULift.{0} ℕ), p0) ∈ (rankLift (outDest hinf attendsT) ch kA).1 := by
        rw [rankLiftT_val]
        exact ⟨p0, by show p0 ∈ (↑(attendsT kA) : Set TCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
      obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
      rw [rankLiftT_val] at hq
      obtain ⟨w, hw, rfl⟩ := hq
      have : ch kA = ch kB := congrArg ULift.down hfst
      exact hch this
  refine ⟨hdist, ?_⟩
  intro hrec
  obtain ⟨hbisim, hsep⟩ := hdist
  exact hsep (ws4_recoverable_not_import (rankLift (outDest hinf attendsT) ch) hrec _ _ hbisim)

/-- **THE TICK NEEDS THE STREAM, ON `TCar` (WS3; Ext-1 R2).** The two available closures `kA`, `kB` are
plain-identified on the real carrier (the collapse engine) - the relating alone does not determine which fires -
and every exogenous choice label distinguishing them is non-recoverable. So the stream's entry is what makes the
closure determinate, load-bearing rather than cosmetic; without it the choice is indeterminate. -/
theorem ws3_tick_needs_stream (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (outDest hinf attendsT) R ∧ R kA kB)
  ∧ (∀ ch : TCar → ℕ, ch kA ≠ ch kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ch)) := by
  refine ⟨ws1_atomless_bisim (outDest hinf attendsT) kA kB (ws1_tcar_SHNE hinf kA) (ws1_tcar_SHNE hinf kB), ?_⟩
  intro ch hch
  exact (ws3_stream_exogenous hinf ch hch).2

end P2S1
