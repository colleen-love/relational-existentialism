/-
`program-2/series-6/formal/P2S6/ws1.lean`

WS1 - Strict identity fails across a tick (the trivial ground). Program 2 Series 6 (2.6), the blocking workstream.

Imports `P2S5` and reaches the tick machinery transitively (`TCar`, `attendsT`, `rankT`, `reifyT`, `kA`/`kB`/`kC`,
`isTick`, `causal`, `outDest`, `ws1_tcar_SHNE`, `plainOf_rankLiftT`, `rankLiftT_val`, the collapse engine
`ws1_atomless_bisim`, the rank lift `rankLift`, `AttentionDistinguishes`). It fixes the TICK-SUCCESSOR relation
`succDep` (a produced moment consumed by the next, an alias of `causal`, named for this series) and proves the
trivial ground: STRICT identity (bisimilarity of the rank lift that fixes it) fails across a tick, because the
reified successor `kC` outranks its constituent `kA` while staying plain-bisimilar to it (`AttentionDistinguishes`,
the `ws2_many_general` / linearization-import mechanism). This is the COSTUME of relational identity, walled out
of the verdict; the series earns its keep on WS2 (the weak continuity) and WS3 (the linearization import).

Design docs: `program-2/series-6/spec/ws1-design.md`; shared objects `spec/README.md` §2.1.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S5

universe u

namespace P2S6

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **The tick-successor relation.** A produced moment `t` consumed by the next produced moment `u`
(`t ∈ attendsT u`, both `isTick`). An alias of `P2S1.causal`, named for this series (the candidate carrier of a
weak continuity). -/
@[reducible] def succDep (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u

/-- **The tick-successor is witnessed.** `kA` and `kB` are each consumed by the higher closure `kC`: the
reification-dependency edges of the succession. -/
theorem ws1_succ_witnessed : succDep kA kC ∧ succDep kB kC := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide

/-- **STRICT IDENTITY FAILS ACROSS A TICK (the trivial ground).** The reified successor moment `kC` and its
constituent `kA` are plain-bisimilar (the collapse engine `ws1_atomless_bisim`, both `SHNE`) yet NOT bisimilar
over the rank lift that fixes strict identity (`kC` carries tower rank 2, `kA`'s edges carry rank 1): exactly
`AttentionDistinguishes`. Strict identity fails; the pair stays plain-alike. Trivial by design (the costume);
walled out of the verdict, which rests on WS2/WS3. -/
theorem ws1_strict_fails (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA := by
  refine ⟨?_, ?_⟩
  · rw [plainOf_rankLiftT]
    exact ws1_atomless_bisim (outDest hinf attendsT) kC kA (ws1_tcar_SHNE hinf kC) (ws1_tcar_SHNE hinf kA)
  · rintro ⟨R, hR, hRel⟩
    obtain ⟨hfwd, _⟩ := hR kC kA hRel
    have hedge : ((⟨rankT kC⟩ : ULift.{0} ℕ), kA) ∈ (rankLift (outDest hinf attendsT) rankT kC).1 := by
      rw [rankLiftT_val]
      exact ⟨kA, by show kA ∈ (↑(attendsT kC) : Set TCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
    obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
    rw [rankLiftT_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have : rankT kC = rankT kA := congrArg ULift.down hfst
    exact absurd this (by decide)

end P2S6
