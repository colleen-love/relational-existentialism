/-
`program-2/series-1/formal/P2S1/ws4.lean`

WS4 - The clock knot (the genuinely-uncertain obligation). Program 2 Series 1 (2.1), the knot.

The two orders on ticks and the two-zone fork. The CAUSAL partial order `causal` (a tick `u` consumes a
produced tick `t`: `isTick t ∧ isTick u ∧ t ∈ attendsT u`) is ENDOGENOUS - read off `attendsT`, exhibited on
the witnessed causal pair `kA ≺ kC`, rank-constrained (`causal t u → rankT t < rankT u`), and genuinely partial
(the concurrent pair `kA`,`kB` is incomparable). Every LINEARIZATION of the concurrent pair the stream supplies
is a genuine IMPORT: for ANY exogenous order label `ord : TCar → ℕ` distinguishing `kA`,`kB`, the ordered lift
plain-identifies them (the collapse engine) yet is label-separated, hence NOT `Recoverable`. The tower `rankT`
canNOT linearize the concurrent pair (`rankT kA = rankT kB = 1`), so the linearization is genuinely exogenous.
Both arms on the SAME witness `TCar`, witnessed causal and concurrent pairs (audit (d), no PR1-S1 tautology).

Design docs: `program-2/series-1/spec/ws4-design.md`; shared objects `spec/README.md` §1-§3, §5.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- The produced relata (ticks/closures): the reified composites. -/
@[reducible] def isTick (x : TCar) : Prop := x = kA ∨ x = kB ∨ x = kC

/-- **The causal order between ticks.** A tick `u` consumes a produced tick `t`: `t ∈ attendsT u`, both ticks.
Defined from the plain relating `attendsT` and `isTick`, with no exogenous label. The base 2-cycle edges are
WITHIN-tick relating (not `isTick`), correctly NOT causal edges. -/
@[reducible] def causal (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u

/-- **THE CAUSAL ORDER IS ENDOGENOUS AND STRUCTURALLY CONSTRAINED (WS4 arm 1, audit (d)).** The causal pair
`kA ≺ kC`, `kB ≺ kC` is witnessed (non-empty); consuming a product strictly raises the reification height
(`causal t u → rankT t < rankT u`, so the order is acyclic and rank-constrained, not total by construction);
and the concurrent pair `kA`,`kB` is incomparable (the order is genuinely partial). All read off `attendsT`,
recoverable. -/
theorem ws4_causal_order_endogenous :
    (causal kA kC ∧ causal kB kC)
  ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide

/-- **THE LINEARIZATION IS A GENUINE IMPORT, QUANTIFIED (WS4 arm 2, audit (a)/(e)).** For EVERY exogenous order
label `ord : TCar → ℕ` distinguishing the concurrent pair (`ord kA ≠ ord kB`), the ordered lift plain-identifies
`kA`,`kB` (the collapse engine, `ord`-independent) yet is label-separated (the `ord` label survives), so the
linearization is NOT recoverable from the plain relating. The order `ord` is supplied by the stream, quantified
over all such labels, never named. The tower `rankT` cannot supply it (`rankT kA = rankT kB`). -/
theorem ws4_linearization_import (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB
      ∧ (¬ Recoverable (rankLift (outDest hinf attendsT) ord)) := by
  intro ord hord
  have hdist : AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB := by
    refine ⟨?_, ?_⟩
    · rw [plainOf_rankLiftT]
      exact ws1_atomless_bisim (outDest hinf attendsT) kA kB (ws1_tcar_SHNE hinf kA) (ws1_tcar_SHNE hinf kB)
    · rintro ⟨R, hR, hRel⟩
      obtain ⟨hfwd, _⟩ := hR kA kB hRel
      have hedge : ((⟨ord kA⟩ : ULift.{0} ℕ), p0) ∈ (rankLift (outDest hinf attendsT) ord kA).1 := by
        rw [rankLiftT_val]
        exact ⟨p0, by show p0 ∈ (↑(attendsT kA) : Set TCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
      obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
      rw [rankLiftT_val] at hq
      obtain ⟨w, hw, rfl⟩ := hq
      have : ord kA = ord kB := congrArg ULift.down hfst
      exact hord this
  refine ⟨hdist, ?_⟩
  intro hrec
  obtain ⟨hbisim, hsep⟩ := hdist
  exact hsep (ws4_recoverable_not_import (rankLift (outDest hinf attendsT) ord) hrec _ _ hbisim)

/-- **THE TWO-ZONE FORK (WS4, the audit-facing aggregate).** The causal order is a witnessed, partial,
endogenous order (arm 1); every linearization of the concurrent pair is an import (arm 2). The wall between the
conjuncts is Series 07's import boundary: the causal order recoverable, the linearization not. -/
theorem ws4_two_zone (hinf : ℵ₀ ≤ κ) :
    (causal kA kC ∧ ¬ causal kA kB ∧ ¬ causal kB kA)
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · decide
  · intro ord hord; exact (ws4_linearization_import hinf ord hord).2

end P2S1
