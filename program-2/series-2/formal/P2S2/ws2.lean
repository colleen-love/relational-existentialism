/-
`program-2/series-2/formal/P2S2/ws2.lean`

WS2 - Genuinely two reader-wise (the reader knot, the central sin, K1). Program 2 Series 2 (2.2).

The self and the other are genuinely two READER-WISE: `oth` and `slf` are plain-bisimilar over the bare
out-attention relating (the collapse engine `ws1_atomless_bisim`) yet rank-separated (`ws2_other_distinguishes`,
the `ws1_first_other` / `ws2_composite_distinguishes` pattern), so the other is real FOR a NAMED finite attention
`selfReader` (`ws2_other_reader_wise`, a genuine `RealFor` witness on a FIXED reader — not existentially tailored,
not `Many`), and the separation is NON-RECOVERABLE (`ws2_other_non_recoverable`, an import, Series 07). The
reader is a fixed named bounded attention (its `reads` membership load-bearing), and the OTHER's own attention
(`attendsR oth`, the four readings of WS3) is what does the distinguishing; the other is never a point-tag, never
the reader quantified out (K1, the C1-S1 repair: the reader named, not existential).

Design docs: `program-2/series-2/spec/ws2-design.md`; shared objects `spec/README.md` §1-§4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S2.ws1

universe u

namespace P2S2

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-- **THE OTHER IS DISTINGUISHED FROM THE SELF (the shared engine).** `oth` and `slf` are plain-bisimilar over
the bare relating (`ws1_atomless_bisim`) yet NOT label-bisimilar over the rank lift (`oth`'s edge carries `rankR
oth = 1`, `slf`'s carries `rankR slf = 0`): exactly `AttentionDistinguishes`. The `ws1_first_other` /
`firstOther_label_sep` pattern lifted from one relatum to the two loci. -/
theorem ws2_other_distinguishes (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsR) rankR) oth slf := by
  refine ⟨?_, ?_⟩
  · rw [plainOf_rankLiftR]
    exact ws1_atomless_bisim (outDest hinf attendsR) oth slf (ws1_rcar_SHNE hinf oth) (ws1_rcar_SHNE hinf slf)
  · rintro ⟨R, hR, hRel⟩
    obtain ⟨hfwd, _⟩ := hR oth slf hRel
    have hedge : ((⟨rankR oth⟩ : ULift.{0} ℕ), slf) ∈ (rankLift (outDest hinf attendsR) rankR oth).1 := by
      rw [rankLiftR_val]
      exact ⟨slf, by show slf ∈ (↑(attendsR oth) : Set RCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
    obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
    rw [rankLiftR_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have : rankR oth = rankR slf := congrArg ULift.down hfst
    exact absurd this (by decide)

/-- **THE NAMED READER (the C1-S1 repair).** A FIXED bounded reader — focus `slf`, reading `{slf}`, finite,
grounded — over the rank lift. It is a `def`, not an existential witness, so the WS2 payoff cannot be tailored
per structure: the reader is named and its `reads = {slf}` is fixed. -/
noncomputable def selfReader (hinf : ℵ₀ ≤ κ) : FiniteAttention (rankLift (outDest hinf attendsR) rankR) :=
  ⟨slf, {slf}, Set.finite_singleton slf,
    ⟨Set.mem_singleton slf, by
      intro z hz
      rw [Set.mem_singleton_iff] at hz; subst hz
      exact Relation.ReflTransGen.refl⟩⟩

/-- **GENUINELY TWO READER-WISE, THE READER LOAD-BEARING AND NAMED (audit (a), K1).** The other `oth` is real
FOR the NAMED finite attention `selfReader` (not an existential over readers, the C1-S1 repair): `oth` is
plain-bisimilar to the read relatum `slf ∈ selfReader.reads` yet label-separated from it (`RealFor` via
`ws2_other_distinguishes`). The reader is a fixed named bounded attention whose `reads` membership is
LOAD-BEARING; `Many` is not used, and the reader is not quantified out. This is the reader-relative reality (a
relatum is real for a bounded reader that reads a relatum it is plain-bisimilar-yet-label-separated from) that
`Many` alone does not carry; the OTHER's own attention (`attendsR oth`, WS3's four readings) does the
distinguishing. -/
theorem ws2_other_reader_wise (hinf : ℵ₀ ≤ κ) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (selfReader hinf) oth :=
  ⟨slf, Set.mem_singleton slf, ws2_other_distinguishes hinf⟩

/-- **THE TWONESS IS NON-RECOVERABLE (audit (b)).** The self/other separation is NOT recoverable from the plain
(symmetric) relating: an import, which by Series 07 is what a genuine atomless distinction MUST be. The
`ws2_tick_irreversible` / `ws2_distinction_free` pattern. -/
theorem ws2_other_non_recoverable (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (rankLift (outDest hinf attendsR) rankR) := by
  intro hrec
  obtain ⟨hbisim, hsep⟩ := ws2_other_distinguishes hinf
  exact hsep (ws4_recoverable_not_import (rankLift (outDest hinf attendsR) rankR) hrec _ _ hbisim)

end P2S2
