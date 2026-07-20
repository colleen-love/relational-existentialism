/-
`program-2/series-1/formal/P2S1/ws2.lean`

WS2 - Subtractivity and the arrow (the reader knot). Program 2 Series 1 (2.1).

The composite `kA` is genuinely new and the reading is load-bearing: it carries a residue non-recoverable from
the plain relating (`ws2_composite_residue`, the transcribed diagonal `ws2_residue_free` at the composite's
inspections, with a genuine hold witnessed at `kA`); it is real FOR a NAMED finite attention
(`ws2_composite_real_for`, a genuine `RealFor` witness with the reader bound and used, the `ws2_attention_makes_real`
shape, NOT `Many`); and the closure does not invert (`ws2_tick_irreversible`, the reification height is
`¬ Recoverable`, a theorem over the relating, not a step counter). The shared engine is
`ws2_composite_distinguishes`: `kA` and the base relatum `p0` are plain-bisimilar (the collapse engine) yet
rank-separated (`rankT kA = 1 ≠ 0 = rankT p0`), the `ws1_first_other` pattern.

Design docs: `program-2/series-1/spec/ws2-design.md`; shared objects `spec/README.md` §1-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE COMPOSITE IS DISTINGUISHED FROM ITS BASE (the shared engine).** `kA` and the base relatum `p0` are
plain-bisimilar over the bare relating (`ws1_atomless_bisim`) yet NOT label-bisimilar over the rank lift (`kA`'s
edge carries tower height `rankT kA = 1`, `p0`'s carries `rankT p0 = 0`): exactly `AttentionDistinguishes`. The
`ws1_first_other` / `firstOther_label_sep` pattern, generalized from the self-loop to the 2-cycle composite. -/
theorem ws2_composite_distinguishes (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kA p0 := by
  refine ⟨?_, ?_⟩
  · rw [plainOf_rankLiftT]
    exact ws1_atomless_bisim (outDest hinf attendsT) kA p0 (ws1_tcar_SHNE hinf kA) (ws1_tcar_SHNE hinf p0)
  · rintro ⟨R, hR, hRel⟩
    obtain ⟨hfwd, _⟩ := hR kA p0 hRel
    have hedge : ((⟨rankT kA⟩ : ULift.{0} ℕ), p0) ∈ (rankLift (outDest hinf attendsT) rankT kA).1 := by
      rw [rankLiftT_val]
      exact ⟨p0, by show p0 ∈ (↑(attendsT kA) : Set TCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
    obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
    rw [rankLiftT_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have : rankT kA = rankT p0 := congrArg ULift.down hfst
    exact absurd this (by decide)

/-- **THE COMPOSITE'S PARTIAL ATTENTION DRIVES A GENUINE LOSS (subtractivity, LOAD-BEARING; Charter Extension 1
R3).** The composite's FINITE attention is a PROPER PART of its relating: `kA` is behaviorally identified (the
collapse engine, `ws1_atomless_bisim`) with `kC`, a relatum it does NOT attend (`kC ∉ attendsT kA = {p0,p1}`).
So the finite attention genuinely SUBTRACTS - it loses `kC` (and everything beyond its cycle) that the relating
still identifies it with. The composite's partial attention does the work (attention ⊊ relating), not a bare
conjunction of a global diagonal with a non-vacuity witness (the EXT-F3 repair). -/
theorem ws2_composite_residue (hinf : ℵ₀ ≤ κ) :
    ∃ y : TCar, (∃ R, IsBisim (outDest hinf attendsT) R ∧ R kA y) ∧ y ∉ attendsT kA := by
  refine ⟨kC, ws1_atomless_bisim (outDest hinf attendsT) kA kC (ws1_tcar_SHNE hinf kA) (ws1_tcar_SHNE hinf kC),
          ?_⟩
  decide

/-- **THE COMPOSITE IS REAL FOR A NAMED ATTENTION (audit (c), WS2).** There is a genuine `FiniteAttention` (a
bounded reader: focus `p0`, reading `{p0}`, finite, grounded) FOR WHICH `kA` is real: `kA` is plain-bisimilar
to the read relatum `p0` yet label-separated from it (`RealFor` via `ws2_composite_distinguishes`). The reader
(`att.reads` membership) is LOAD-BEARING; `Many` is not used. The `ws2_attention_makes_real` shape. -/
theorem ws2_composite_real_for (hinf : ℵ₀ ≤ κ) :
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsT) rankT),
      RealFor (rankLift (outDest hinf attendsT) rankT) att kA := by
  refine ⟨⟨p0, {p0}, Set.finite_singleton p0, ⟨Set.mem_singleton p0, ?_⟩⟩,
          p0, Set.mem_singleton p0, ws2_composite_distinguishes hinf⟩
  intro z hz
  rw [Set.mem_singleton_iff] at hz; subst hz
  exact Relation.ReflTransGen.refl

/-- **THE TICK DOES NOT INVERT (the arrow, DIRECTIONAL; Charter Extension 1 R1).** Reification strictly raises
the tower height from a tick's components to the composite: every member of `kA`'s cycle ranks strictly below
`kA` (`∀ x ∈ attendsT kA, rankT x < rankT kA`). So the closure does not run backward - the composite is not a
predecessor of its own components; the tick relation is acyclic. This is the DIRECTIONAL arrow (the EXT-F2
repair), not non-recoverability. The `¬ Recoverable` fact is RETAINED as the companion import (Series 07: a
genuine distinction is non-recoverable). WS5's `arrow` flag rests on the directional conjunct. -/
theorem ws2_tick_irreversible (hinf : ℵ₀ ≤ κ) :
    (∀ x ∈ attendsT kA, rankT x < rankT kA)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsT) rankT) := by
  refine ⟨by decide, ?_⟩
  intro hrec
  obtain ⟨hbisim, hsep⟩ := ws2_composite_distinguishes hinf
  exact hsep (ws4_recoverable_not_import (rankLift (outDest hinf attendsT) rankT) hrec _ _ hbisim)

end P2S1
