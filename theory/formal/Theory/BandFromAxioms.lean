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
  this precise as `conservedOffdiag μ := fun i j => ‖μ i j‖ = 1 ∧ i ≠ j` — the conserved off-diagonal
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
`Align μ (conservedOffdiag μ)` is a **theorem** (`align_of_contractive`), and so

  `band_coincidence_from_axioms : seamBand (conservedOffdiag μ) = rotatingBand μ`

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
* `[open]` (unchanged from `03.8`/`03.9`): the general CPTP peripheral structure theorem (that an
  arbitrary primitive `Φ_c` places its modulus-1 spectrum into a commutative decoherence-free subalgebra
  — `SpectralDecay`/`PeripheralAlgebra`'s narrated gap), and the full `L = −i[H,·] + D` split.

**Provenance.** `R / S` — spectral decay, decoherence-free subalgebras, and the peripheral decomposition
are standard; the synthesis is recognizing that A3's "decoherence-free subalgebra" gloss, taken
literally, already contains the energy band, hence already contains the bet.
-/
import Theory.BandCoincidence

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

/-- **The conserved off-diagonal band (the *spectral* object).** The modulus-one off-diagonal coherence
`‖μ i j‖ = 1 ∧ i ≠ j`. This is a **spectral** predicate (defined by `‖μ‖`), A3's `Peri(Φ_c)` minus its
classical diagonal record — **not** the operational seam. Renamed off "seam" deliberately: that the
operational seam (the un-attendable block of `SeamForcing`/`SeamConserved`, characterized *without* `‖μ‖`)
equals this spectral band is the **claim** (`band_coincidence`), not a shared name. -/
def conservedOffdiag (μ : A → A → ℂ) (i j : A) : Prop := ‖μ i j‖ = 1 ∧ i ≠ j

/-! ## §0 A3's sustainable field `Peri(Φ_c)`, and the seam as its off-diagonal

A3 names the self the **greatest sustainable field** — *"a self is an eigenform of the co-directed
attention operator `Φ_c` … the carrier of selves being its greatest sustainable field."* Read literally,
that field is `Peri(Φ_c) = { X : ‖Φ_c X‖ = ‖X‖ }`, the forms the loop returns unchanged in magnitude —
which **includes the rotating band** (`‖μ‖ = 1, μ ≠ 1`), not only the strict fixed band (`νΦ_c`, `μ = 1`).
This section makes that precise: `Peri` *is* the conserved band, `conservedOffdiag` is its off-diagonal
part, and `νΦ_c` (the fixed band) is its `μ = 1` sub-band. So `conservedOffdiag` is **A3's own self
minus its diagonal record**, not a free definition — which is exactly why the band coincidence below
*unfolds* A3's text rather than positing a fourth axiom. -/

/-- **A3's sustainable field, entrywise.** `Peri μ M` holds when one closure of the loop returns `M`
unchanged in magnitude at every entry: `‖schur μ M i j‖ = ‖M i j‖` for all `i, j`. This is A3's "greatest
sustainable field" — the forms reproduced up to magnitude — read entrywise, the same reading under which
`schur_sustained` / `conservedBand_sustained` already state sustainedness (so no choice of matrix norm is
smuggled in). -/
def Peri (μ : A → A → ℂ) (M : Matrix A A ℂ) : Prop := ∀ i j, ‖schur μ M i j‖ = ‖M i j‖

/-- **A3's sustainable field is exactly the conserved band.** `M` is sustained (entrywise
magnitude-preserved under one loop) iff every nonzero coherence sits on a modulus-one edge — i.e. iff
`M ∈ conservedBand μ`. So `Peri`, A3's self, carries the rotating (energy) band *beside* the fixed (known)
one; it is **not** the strict fixed point `νΦ_c` alone. -/
theorem peri_iff_mem_conservedBand (μ : A → A → ℂ) (M : Matrix A A ℂ) :
    Peri μ M ↔ M ∈ conservedBand μ := by
  constructor
  · intro h
    simp only [conservedBand, mem_bandOn]
    intro i j hcons
    have hij := h i j
    rw [schur_apply, norm_mul] at hij
    rcases mul_left_eq_self₀.mp hij with h1 | h0
    · exact absurd h1 hcons
    · exact norm_eq_zero.mp h0
  · intro hM i j
    simp only [conservedBand, mem_bandOn] at hM
    by_cases hc : ‖μ i j‖ = 1
    · rw [schur_apply, norm_mul, hc, one_mul]
    · rw [schur_apply, hM i j hc, mul_zero]

/-- **The seam is the off-diagonal part of A3's sustainable field.** `conservedOffdiag` selects exactly
the *off-diagonal* edges of `Peri` (= `conservedBand`): the self read as `Peri(Φ_c)`, minus its diagonal
(known) record. (`Iff.rfl`: `conservedOffdiag` and `conservedEdge ∧ off-diagonal` are the same
predicate.) -/
theorem conservedOffdiag_iff_offdiag_conserved (μ : A → A → ℂ) (i j : A) :
    conservedOffdiag μ i j ↔ (conservedEdge μ i j ∧ i ≠ j) := Iff.rfl

/-- **`νΦ_c` is the `μ = 1` sub-band of A3's sustainable field.** The strict fixed band (the known /
diagonal record) sits inside `Peri = conservedBand` as its non-rotating part: `fixedBand μ ≤
conservedBand μ`. So A3's self is the sustainable field; `νΦ_c` is one half of it (knowing), the rotating
(energy) band the other. -/
theorem fixedBand_le_conservedBand (μ : A → A → ℂ) : fixedBand μ ≤ conservedBand μ :=
  bandOn_mono fun i j h => by
    have h' : μ i j = 1 := h
    show ‖μ i j‖ = 1
    rw [h', norm_one]

/-- **The eigenoperator anchor.** A single off-diagonal coherence `Eunit i j` lies in A3's sustainable
field iff its channel eigenvalue is a phase: `Peri μ (Eunit i j) ↔ ‖μ i j‖ = 1`. (The matrix unit is the
eigen-operator with eigenvalue `μ i j`; it is sustained exactly when `‖μ i j‖ = 1`.) So the rotating
(energy) edges are literally the off-diagonal eigen-directions A3 calls the self. -/
theorem Eunit_peri_iff (μ : Fin 3 → Fin 3 → ℂ) (i j : Fin 3) :
    Peri μ (Eunit i j) ↔ ‖μ i j‖ = 1 := by
  rw [peri_iff_mem_conservedBand]
  constructor
  · intro hmem; by_contra hc; exact Eunit_not_mem_bandOn (P := conservedEdge μ) hc hmem
  · intro hc; exact Eunit_mem_bandOn (P := conservedEdge μ) hc

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
    rotatingEdge μ i j ↔ conservedOffdiag μ i j := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => h2 ((hnd i j).mpr e)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => h2 ((hnd i j).mp e)⟩

/-- **The decoherence-free seam carries no diagonal coherence** (`SeamOffdiagonal`) — automatically: an
edge with `i ≠ j` is never the diagonal. -/
theorem conservedOffdiag_offdiagonal (μ : A → A → ℂ) :
    SeamOffdiagonal (conservedOffdiag μ) := by
  intro i hii; exact hii.2 rfl

/-- **The bet `Align` is a theorem for the decoherence-free seam.** Any *attendable* off-diagonal edge
(`∉ conservedOffdiag`, `i ≠ j`) has `‖μ i j‖ ≠ 1`; with contractivity (`‖μ i j‖ ≤ 1`) it strictly
decays. So `H_align` is *not* an independent posit — it follows from the channel being a contraction once
the seam is taken to be the decoherence-free block. **This is the reduction of the bet to A3's gloss.** -/
theorem align_of_contractive {μ : A → A → ℂ} (hc : Contractive μ) :
    Align μ (conservedOffdiag μ) := by
  intro i j hns hij
  have hne : ‖μ i j‖ ≠ 1 := fun h => hns ⟨h, hij⟩
  exact lt_of_le_of_ne (hc i j) hne

/-- **The seam band and the rotating band coincide — A3 unfolded, not a fourth posit.** Under
nondegeneracy alone the decoherence-free off-diagonal block *is* the rotating band
(`rotatingEdge_iff_decoherenceFree`). This is **not** "deriving `H_align`": with the seam read as the
off-diagonal of A3's sustainable field `Peri` (`conservedOffdiag_iff_offdiag_conserved`,
`peri_iff_mem_conservedBand`), the two bands are the *same predicate* once `μ = 1 ↔ i = j` identifies the
held band with the diagonal. The content is A3's own "greatest sustainable field," written out — the
structural half of the reconciliation. -/
theorem seam_eq_rotating {μ : A → A → ℂ} (hnd : ∀ i j, μ i j = 1 ↔ i = j) :
    seamBand (conservedOffdiag μ) = rotatingBand μ :=
  bandOn_congr (fun i j => (rotatingEdge_iff_decoherenceFree hnd i j).symm)

/-- **T4 — the bet, as A3 unfolded.** `rotatingBand μ ⊆ seamBand (conservedOffdiag μ)` from the two
baseline facts (contractive + nondegenerate), **replacing spec I's `H_align` hypothesis with a proof** once
the seam is read as the off-diagonal of A3's own sustainable field `Peri` (`peri_iff_mem_conservedBand`).
Energy is at most permanent feeling — A3 written in full, not a fourth wager. -/
theorem rotating_subset_seamBand_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    rotatingBand μ ≤ seamBand (conservedOffdiag μ) :=
  rotating_subset_seamBand ⟨fun _ _ h => h.1, hnd⟩ (align_of_contractive hc)

/-- **The coincidence, by unfolding A3 (no fourth posit).** `seamBand (conservedOffdiag μ) =
rotatingBand μ` from contractivity + nondegeneracy. This is **not** a fourth axiom and not "the bet
derived as a theorem of A1–A3": with the seam *read* as the off-diagonal of A3's own sustainable field
`Peri` (`peri_iff_mem_conservedBand`) — i.e. C1, A3 taken at the strength of its text — the alignment is a
one-line consequence of the channel being a contraction (`align_of_contractive`), and the coincidence is
then near-definitional (`seam_eq_rotating`). What stays a `[reading]` is **C1 itself** — that the self is
`Peri(Φ_c)` rather than the strict `νΦ_c` — but C1 is A3's gloss, *already* an axiom, so nothing is added.
*Three axioms, said completely, are already three.* The conservation law `undifferentiated = knowing +
energy` thus rests, on this witness model, on no `H_align` beyond A3 written in full. -/
theorem band_coincidence_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    seamBand (conservedOffdiag μ) = rotatingBand μ :=
  band_coincidence ⟨fun _ _ h => h.1, hnd⟩ (conservedOffdiag_offdiagonal μ)
    (align_of_contractive hc)

/-- **T4 — the two-term law, unconditional on `H_align`.** Under the decoherence-free seam, the conserved
ground is the internal direct sum `knowing ⊕ feeling` with **no fourth posit**: the only inputs are
contractivity and nondegeneracy. *undifferentiated = knowing + energy*, on the axioms' gloss alone. -/
theorem undifferentiated_two_term_from_axioms {μ : A → A → ℂ}
    (hnd : ∀ i j, μ i j = 1 ↔ i = j) (hc : Contractive μ) :
    fixedBand μ ⊓ seamBand (conservedOffdiag μ) = ⊥
      ∧ fixedBand μ ⊔ seamBand (conservedOffdiag μ) = conservedBand μ :=
  undifferentiated_two_term ⟨fun _ _ h => h.1, hnd⟩ (conservedOffdiag_offdiagonal μ)
    (align_of_contractive hc)

/-! ## §4 The genuine witness satisfies the baseline — no bet needed

`quarterMul` ([`RotatingSpectrum`](RotatingSpectrum.lean)) is contractive and nondegenerate, so its
band coincidence holds *without* assuming `H_align` — the bet was never load-bearing on the witness. -/

/-- `quarterMul` is **contractive**: every entry has norm `≤ 1` (diagonal `1`; rotating `±i`, norm `1`;
phase-locked `∓i·½` and transient `½`, norm `½`). -/
theorem quarterMul_contractive : Contractive quarterMul := by
  intro i j
  unfold quarterMul
  split_ifs
  · exact le_of_eq norm_one
  · exact le_of_eq (by rw [Complex.norm_eq_abs, Complex.abs_I])
  · exact le_of_eq (by rw [norm_neg, Complex.norm_eq_abs, Complex.abs_I])
  · refine le_of_lt ?_
    rw [norm_mul, norm_neg, Complex.norm_eq_abs, Complex.abs_I, one_mul]
    exact half_norm_lt
  · refine le_of_lt ?_
    rw [norm_mul, Complex.norm_eq_abs, Complex.abs_I, one_mul]
    exact half_norm_lt
  · exact le_of_lt half_norm_lt

/-- **The witness coincidence, with the bet discharged.** On the genuine `quarterMul` channel, with the
seam read as the decoherence-free off-diagonal block, `seamBand = rotatingBand` follows from
contractivity + nondegeneracy alone — **no `H_align`.** -/
theorem quarterMul_coincidence_from_axioms :
    seamBand (conservedOffdiag quarterMul) = rotatingBand quarterMul :=
  band_coincidence_from_axioms quarterMul_fixed_eq_diagonal quarterMul_contractive

/-- **Phase-blindness (T3), at the band level.** The rotating (energy) coherences inside the seam are
**sustained** — their magnitude is conserved at every depth. So the un-attendability/protection of the
self-block covers energy exactly as it covers the fixed record: the seam protects by *position*, not by
spectral type. (This is `rotatingBand_sustained` read through `seam_eq_rotating`.) -/
theorem seam_energy_sustained {μ : A → A → ℂ} (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    {M : Matrix A A ℂ} (hM : M ∈ seamBand (conservedOffdiag μ)) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ :=
  rotatingBand_sustained (seam_eq_rotating hnd ▸ hM) n i j

/-! ## §5 The energy band as the generator's `ker(genReal)` — arrow and energy, one generator

`RotatingSpectrum`'s `energyEdge μ := genReal μ i j = 0 ∧ i ≠ j` reads the energy band off the *single*
generator `log μ` (its real part vanishing off the diagonal), rather than off the modulus directly. On the
witness this coincides — edge for edge — with both the rotating band and the decoherence-free seam, so the
"energy = conserved band" identification is now stated through the generator the arrow also lives in. The
two senses of "conserved" stay distinct: `energyEdge`/`Peri` is *exact* (`genReal = 0`); the operational
seam's `self_cannot_fully_decohere` is only a positive floor — kept apart deliberately. -/

/-- **The generator-defined energy band is the rotating band, on the witness.** `genReal = 0` ⟺ `‖μ‖ = 1`
(a live edge, `quarterMul_ne_zero`) and `i ≠ j` ⟺ `μ ≠ 1` (nondegeneracy), so the edge predicates agree. -/
theorem energyEdge_iff_rotatingEdge_quarterMul (i j : Fin 3) :
    energyEdge quarterMul i j ↔ rotatingEdge quarterMul i j := by
  unfold energyEdge rotatingEdge
  rw [genReal_eq_zero_iff quarterMul i j (quarterMul_ne_zero i j)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun he => h2 ((quarterMul_fixed_eq_diagonal i j).mp he)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun he => h2 ((quarterMul_fixed_eq_diagonal i j).mpr he)⟩

/-- **The generator-defined energy band is the decoherence-free seam, on the witness.** `genReal = 0` ⟺
`‖μ‖ = 1` collapses `energyEdge` onto `conservedOffdiag = (‖μ‖ = 1 ∧ i ≠ j)` directly. -/
theorem energyEdge_iff_conservedOffdiag_quarterMul (i j : Fin 3) :
    energyEdge quarterMul i j ↔ conservedOffdiag quarterMul i j := by
  unfold energyEdge conservedOffdiag
  rw [genReal_eq_zero_iff quarterMul i j (quarterMul_ne_zero i j)]

/-- **`energyBand = rotatingBand` on the witness** — the generator's `ker(genReal)` off-diagonal block is
exactly the rotating (energy) band. The energy reading, stated through the one generator the arrow lives
in. -/
theorem energyBand_eq_rotating_quarterMul :
    bandOn (energyEdge quarterMul) = rotatingBand quarterMul :=
  bandOn_congr energyEdge_iff_rotatingEdge_quarterMul

/-- **`energyBand = seamBand (conservedOffdiag)` on the witness** — the generator-defined energy band is
A3's decoherence-free off-diagonal block. (This relates the *spectral* seam `conservedOffdiag`, defined
by `‖μ‖ = 1`, to the generator band; the **operational** seam of `SeamForcing` is a separate object — the
open unifier — not this.) -/
theorem energyBand_eq_seam_quarterMul :
    bandOn (energyEdge quarterMul) = seamBand (conservedOffdiag quarterMul) :=
  bandOn_congr energyEdge_iff_conservedOffdiag_quarterMul

end RelExist.BandFromAxioms
