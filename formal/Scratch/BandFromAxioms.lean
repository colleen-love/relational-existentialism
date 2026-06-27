/-
# Does the bet fall out of A1–A3? — `H_align` as a theorem of the decoherence-free self

[`BandCoincidence`](BandCoincidence.lean) proved `seamBand = rotatingBand` **under** the bet
`H_align : ker D = J` (spec I, `Align`). This module asks whether that bet is a *fourth posit* or
already implied by the existing three axioms. The finding of [`02-axioms.md`](../../docs/spec/02-axioms.md):
**A3's own gloss already contains it.** A3 formalizes the self as the *strict* fixed point
`νΦ_c` (the `μ = 1`, fixed/known band — `Attention.sustainedField`, `Peripheral.dephase_eigenspace_one`),
but its prose names the self the **decoherence-free subalgebra** of `Φ_c` — *"the relations attention
returns unchanged, in QI terms the decoherence-free subalgebra."* That algebra is the **peripheral**
block `Peri(Φ_c) = { X : ‖Φ_c X‖ = ‖X‖ }`, which carries the rotating (`‖μ‖ = 1, μ ≠ 1`, energy) band
*beside* the fixed one. The bet lives exactly in the gap between `νΦ_c` (strict) and `Peri(Φ_c)` (A3's
gloss). Closing it is **reconciliation**, not a new commitment.

## The decomposition (spec II §1)

`H_align` (`rotatingBand ⊆ seamBand`) reduces to two sub-claims:

* **C1 — the self is `Peri(Φ_c)`, not just `νΦ_c`.** A3's gloss, taken literally: the un-attendable
  self-block is the decoherence-free subalgebra, whose *off-diagonal* part is the rotating band. We make
  this precise as `decoherenceFreeSeam μ := fun i j => ‖μ i j‖ = 1 ∧ i ≠ j` — the conserved off-diagonal
  coherence, the self minus its classical (diagonal) record.
* **C2 — exhaustiveness: only the self persists.** Everything off the peripheral block decays
  (`SpectralDecay.spectral_decay`, here the entrywise `schur_transient_tendsto`), so the only conserved
  coherence lies in some `Peri`. Mechanized: `transient_decays` (off-conserved coherence `→ 0`) and
  `conservedBand_sustained` (conserved coherence keeps its magnitude forever).

## The payoff (spec II §2, T4)

With the seam *defined* as the decoherence-free off-diagonal block (C1), the bet is **discharged**, not
assumed: given only that the channel is **contractive** (`Contractive μ`, the ℂ-shadow of
`Decoherence.defectSq_attend_le` — attention never *amplifies*; an A1/CP baseline fact) and
**nondegenerate** (`μ i j = 1 ↔ i = j`, the A3 baseline that the fixed band is the diagonal),
`Align μ (decoherenceFreeSeam μ)` is a **theorem** (`align_of_contractive`), and so

  `band_coincidence_from_axioms : seamBand (decoherenceFreeSeam μ) = rotatingBand μ`

holds with **no `H_align` hypothesis**. The genuine `quarterMul` witness satisfies both baseline facts,
so the coincidence holds on it *without* the bet (`quarterMul_coincidence_from_axioms`).

## Honest scope

* `[proved]` (footprint at the corpus norm, no added `H_align`): that *given* the seam is the
  decoherence-free off-diagonal block, the alignment is forced by contractivity + nondegeneracy — the
  bet is a derived lemma, not an independent posit.
* `[reading]`/`[posit]` — **C1 itself**: that the self *is* `Peri(Φ_c)` (rather than the strict `νΦ_c`).
  This is A3's gloss, asserted; it is **not** derived here. But it is **already in the corpus as A3**, so
  the bet adds *no fourth axiom* — at most it writes A3 down in full (the spec II fallback `A4`, noted as
  "verbatim A3's gloss"). Three axioms, said completely, are already three.
* `[reading]` (phase-blindness, spec II T3): the seam protection
  (`SeamForcing.self_cannot_fully_decohere` / `Attending.defectSq_attend_shared_pos`) is **indifferent to
  the spectral type** of the coherence it protects — it protects by *position* (off-diagonal, in `J`),
  not by whether the coherence is fixed or rotating. So un-attendability covers **energy** too, witnessed
  at the band level by `rotatingBand_sustained` (the rotating coherences in the seam are sustained,
  i.e. protected). The bridge between the ℝ attention model and the ℂ phase channel stays the
  standing `[open]` functor — discharged here only at witness level.
* `[open]` (unchanged from `03.9`/`03.15`): the general CPTP peripheral structure theorem (that an
  arbitrary primitive `Φ_c` places its modulus-1 spectrum into a commutative decoherence-free subalgebra
  — `SpectralDecay`/`PeripheralAlgebra`'s narrated gap), and the full `L = −i[H,·] + D` split.

**Provenance.** `R / S` — spectral decay, decoherence-free subalgebras, and the peripheral decomposition
are standard; the synthesis is recognizing that A3's "decoherence-free subalgebra" gloss, taken
literally, already contains the energy band, hence already contains the bet.
-/
import Scratch.BandCoincidence

namespace RelExist.BandFromAxioms

open RelExist.BandCoincidence RelExist.RotatingSpectrum
open Matrix Filter Topology

variable {A : Type*}

/-! ## §1 The two baseline facts — both below the level of `H_align`

Neither is a new posit. `Contractive` is the ℂ-shadow of `Decoherence.defectSq_attend_le` (the proved
fact that attention only ever *drops* coherence — the channel never amplifies); nondegeneracy
(`μ i j = 1 ↔ i = j`) is the A3 baseline that the held/known band is exactly the diagonal. -/

/-- **The channel is contractive** — no coherence is amplified (`‖μ i j‖ ≤ 1`). The complex shadow of
`Decoherence.defectSq_attend_le`: attention dissipates or conserves, never magnifies. A baseline (CP /
A1) fact, not the bet. -/
def Contractive (μ : A → A → ℂ) : Prop := ∀ i j, ‖μ i j‖ ≤ 1

/-- **The decoherence-free seam (A3's gloss, literally).** The conserved off-diagonal coherence
`‖μ i j‖ = 1 ∧ i ≠ j` — the self's un-attendable block *minus* its classical (diagonal) record. This is
the self read as `Peri(Φ_c)` rather than the strict `νΦ_c`. -/
def decoherenceFreeSeam (μ : A → A → ℂ) (i j : A) : Prop := ‖μ i j‖ = 1 ∧ i ≠ j

/-! ## §2 C2 — exhaustiveness: only the peripheral self persists

The dynamical content (`SpectralDecay.spectral_decay`, entrywise `schur_transient_tendsto`): off the
conserved band every coherence decays, and on it every coherence keeps its magnitude forever. So the
*only* persisting coherence is peripheral — `conservedBand` is exactly the non-decaying subspace. -/

/-- **Off the conserved band, coherence decays (the arrow).** A transient edge (`‖μ i j‖ < 1`) carries
its coherence to `0`. The entrywise form of `spectral_decay`'s `Tⁿ → P`: subdominant modes die. -/
theorem transient_decays (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A) (h : ‖μ i j‖ < 1) :
    Tendsto (fun n => ‖(schur μ)^[n] M i j‖) atTop (𝓝 0) :=
  schur_transient_tendsto μ M i j h

/-- **On the conserved band, coherence persists (the peripheral self).** Every coherence of a
`conservedBand` matrix keeps its magnitude at every depth — it is the entrywise non-decaying
(peripheral) subspace. Together with `transient_decays`, this is C2: persisting ⟺ peripheral. -/
theorem conservedBand_sustained {μ : A → A → ℂ} {M : Matrix A A ℂ}
    (hM : M ∈ conservedBand μ) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ := by
  by_cases h : ‖μ i j‖ = 1
  · exact schur_sustained μ M n i j h
  · have hz : M i j = 0 := hM i j h
    rw [schur_iterate, hz, mul_zero]

/-! ## §3 C1 + the payoff — `H_align` derived, not posited

With the seam read as the decoherence-free off-diagonal block (C1), the rotating band and the seam band
**coincide by construction** under nondegeneracy, and the bet `Align` is **forced** by contractivity. No
`H_align` hypothesis survives. -/

/-- Under a nondegenerate baseline, **a rotating edge and a decoherence-free seam edge are the same
thing**: `‖μ‖ = 1, μ ≠ 1` ⟺ `‖μ‖ = 1, i ≠ j` (since `μ = 1 ↔ i = j`). C1, at the edge level. -/
theorem rotatingEdge_iff_decoherenceFree {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (i j : A) :
    rotatingEdge μ i j ↔ decoherenceFreeSeam μ i j := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => h2 ((hnd i j).mpr e)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => h2 ((hnd i j).mp e)⟩

/-- **The decoherence-free seam carries no diagonal coherence** (`SeamOffdiagonal`) — automatically: an
edge with `i ≠ j` is never the diagonal. -/
theorem decoherenceFreeSeam_offdiagonal (μ : A → A → ℂ) :
    SeamOffdiagonal (decoherenceFreeSeam μ) := by
  intro i hii; exact hii.2 rfl

/-- **The bet `Align` is a theorem for the decoherence-free seam.** Any *attendable* off-diagonal edge
(`∉ decoherenceFreeSeam`, `i ≠ j`) has `‖μ i j‖ ≠ 1`; with contractivity (`‖μ i j‖ ≤ 1`) it strictly
decays. So `H_align` is *not* an independent posit — it follows from the channel being a contraction once
the seam is taken to be the decoherence-free block. **This is the reduction of the bet to A3's gloss.** -/
theorem align_of_contractive {μ : A → A → ℂ} (hc : Contractive μ) :
    Align μ (decoherenceFreeSeam μ) := by
  intro i j hns hij
  have hne : ‖μ i j‖ ≠ 1 := fun h => hns ⟨h, hij⟩
  exact lt_of_le_of_ne (hc i j) hne

/-- **The seam band and the rotating band coincide — with no `H_align`.** Under nondegeneracy alone the
decoherence-free off-diagonal block *is* the rotating band (`rotatingEdge_iff_decoherenceFree`). The
structural half of the reconciliation. -/
theorem seam_eq_rotating {μ : A → A → ℂ} (hnd : ∀ i j, μ i j = 1 ↔ i = j) :
    seamBand (decoherenceFreeSeam μ) = rotatingBand μ :=
  bandOn_congr (fun i j => (rotatingEdge_iff_decoherenceFree hnd i j).symm)

/-- **T4 — the bet derived.** `rotatingBand μ ⊆ seamBand (decoherenceFreeSeam μ)` from the two baseline
facts (contractive + nondegenerate), **replacing spec I's `H_align` hypothesis with a proof.** Energy is
at most permanent feeling — now a theorem of the axioms' own gloss, not a fourth wager. -/
theorem rotating_subset_seamBand_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    rotatingBand μ ≤ seamBand (decoherenceFreeSeam μ) :=
  rotating_subset_seamBand ⟨fun _ _ h => h.1, hnd⟩ (align_of_contractive hc)

/-- **The coincidence, from the axioms.** `seamBand (decoherenceFreeSeam μ) = rotatingBand μ` from
contractivity + nondegeneracy — `band_coincidence` with the bet **discharged**. The conservation law
`undifferentiated = knowing + energy` thus rests, on this witness model, on no `H_align` beyond A3's own
"decoherence-free subalgebra" gloss. -/
theorem band_coincidence_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    seamBand (decoherenceFreeSeam μ) = rotatingBand μ :=
  band_coincidence ⟨fun _ _ h => h.1, hnd⟩ (decoherenceFreeSeam_offdiagonal μ)
    (align_of_contractive hc)

/-- **T4 — the two-term law, unconditional on `H_align`.** Under the decoherence-free seam, the conserved
ground is the internal direct sum `knowing ⊕ feeling` with **no fourth posit**: the only inputs are
contractivity and nondegeneracy. *undifferentiated = knowing + energy*, on the axioms' gloss alone. -/
theorem undifferentiated_two_term_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    fixedBand μ ⊓ seamBand (decoherenceFreeSeam μ) = ⊥
      ∧ fixedBand μ ⊔ seamBand (decoherenceFreeSeam μ) = conservedBand μ :=
  undifferentiated_two_term ⟨fun _ _ h => h.1, hnd⟩ (decoherenceFreeSeam_offdiagonal μ)
    (align_of_contractive hc)

/-! ## §4 The genuine witness satisfies the baseline — no bet needed

`quarterMul` ([`RotatingSpectrum`](RotatingSpectrum.lean)) is contractive and nondegenerate, so its
band coincidence holds *without* assuming `H_align` — the bet was never load-bearing on the witness. -/

/-- `quarterMul` is **contractive**: every entry has norm `≤ 1` (diagonal `1`; rotating `±i`, norm `1`;
transient `1/2`). -/
theorem quarterMul_contractive : Contractive quarterMul := by
  intro i j
  unfold quarterMul
  split_ifs
  · exact le_of_eq norm_one
  · exact le_of_eq (by rw [Complex.norm_eq_abs, Complex.abs_I])
  · exact le_of_eq (by rw [norm_neg, Complex.norm_eq_abs, Complex.abs_I])
  · exact le_of_lt half_norm_lt

/-- **The witness coincidence, with the bet discharged.** On the genuine `quarterMul` channel, with the
seam read as the decoherence-free off-diagonal block, `seamBand = rotatingBand` follows from
contractivity + nondegeneracy alone — **no `H_align`.** -/
theorem quarterMul_coincidence_from_axioms :
    seamBand (decoherenceFreeSeam quarterMul) = rotatingBand quarterMul :=
  band_coincidence_from_axioms quarterMul_fixed_eq_diagonal quarterMul_contractive

/-- **Phase-blindness (T3), at the band level.** The rotating (energy) coherences inside the seam are
**sustained** — their magnitude is conserved at every depth. So the un-attendability/protection of the
self-block covers energy exactly as it covers the fixed record: the seam protects by *position*, not by
spectral type. (This is `rotatingBand_sustained` read through `seam_eq_rotating`.) -/
theorem seam_energy_sustained {μ : A → A → ℂ} (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    {M : Matrix A A ℂ} (hM : M ∈ seamBand (decoherenceFreeSeam μ)) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ :=
  rotatingBand_sustained (seam_eq_rotating hnd ▸ hM) n i j

end RelExist.BandFromAxioms
