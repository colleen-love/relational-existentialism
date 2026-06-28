/-
# The band-coincidence conjecture — does permanent feeling coincide with energy?

The open question named in [`03.8-space-energy.md`](../../docs/spec/03.8-space-energy.md)'s honest scope:
*"whether the seam-protected and rotating-protected bands coincide."* Two conservations were kept
strictly distinct there — **dynamical** (a coupling symmetry → the rotating spectrum → a conserved
charge, *energy*: [`RotatingSpectrum`](RotatingSpectrum.lean)) and **operational** (self-inclusion →
the un-attendable seam → permanent feeling: [`SeamForcing`](SeamForcing.lean)). As proved, the
undifferentiated ground splits *three* ways under the first arrow — **knowing** (the fixed band,
`μ = 1`), **energy** (the rotating band, `‖μ‖ = 1`, `μ ≠ 1`), and **permanent feeling** (the
seam-protected block `J`). This module asks whether the last two are the **same band**, which would
collapse the split to *two* terms: `undifferentiated = knowing + energy`, no third remainder.

## The bridge (Task 0) — one carrier

Both structures live on a single ambient space `Matrix A A ℂ`. A coupling is `μ : A → A → ℂ` with channel
`Φ = schur μ`; the seam is a predicate `J : A → A → Prop` (the self-inclusive, un-attendable edges). For a
predicate `P` on edges, `bandOn P` is the submodule of coherences supported on `P`-edges. Then:

* `seamBand J  := bandOn J`                         — coherences on the seam (operationally conserved);
* `rotatingBand μ := bandOn (rotatingEdge μ)`        — `‖μ i j‖ = 1 ∧ μ i j ≠ 1` (dynamically conserved);
* `fixedBand μ := bandOn (fixedEdge μ)`              — `μ i j = 1` (the known / classical record);
* `conservedBand μ := bandOn (conservedEdge μ)`      — `‖μ i j‖ = 1` (the undissipated ground).

This is a *witness-level* identification, not a posited functor: the seam's `defectSq`-protection
(`SeamForcing.self_cannot_fully_decohere`) and the rotating band's magnitude-conservation
(`schur_sustained`) are transported onto this common carrier, where the coincidence becomes a question
about which *edges* each band occupies.

## The hypotheses (the content lives here)

* `UnitaryBaseline μ J` — the only source of `‖μ i j‖ < 1` is attention, and the fixed band is exactly
  the diagonal. So un-attendable seam edges keep modulus one (`seam_undamped`) and every off-diagonal
  edge that survives genuinely rotates (`fixed_eq_diagonal : μ i j = 1 ↔ i = j` — a nondegenerate
  baseline). The Lindblad reading: unitary `H` (+ nondegenerate spectrum) and a dissipator `D` that *is*
  attention.
* `SeamOffdiagonal J` — the seam carries no diagonal (known) coherence (`∀ i, ¬ J i i`). The seam is the
  *live* off-diagonal coherence of the relationship.
* `Align μ J` **(the bet, `H_align : ker D = J`)** — every *attendable* off-diagonal edge strictly
  decays: `¬ J i j → i ≠ j → ‖μ i j‖ < 1`. In words: *the only coherence that does not dissipate is the
  coherence you cannot attend to.* This **is** the conjecture in operator form.

## What is proved (`sorry`-free, footprint reported below)

* `seamBand_subset_rotating` `[follows]` — `UnitaryBaseline ∧ SeamOffdiagonal ⇒ seamBand ⊆ rotatingBand`.
* `rotating_subset_seamBand` `[proved under Align]` — `Align ⇒ rotatingBand ⊆ seamBand`. (Consumes the bet.)
* `band_coincidence` `[proved under hypotheses]` — the coincidence `seamBand = rotatingBand`.
* `conserved_internal_split` / `undifferentiated_two_term` `[follows]` — the conserved ground is the
  internal direct sum `fixedBand ⊕ rotatingBand` (`⊓ = ⊥`, `⊔ = conservedBand`); under the coincidence,
  `= fixedBand ⊕ seamBand` — *undifferentiated = knowing + energy*, **no third summand**.
* `rotatingBand_sustained` — every coherence of a `rotatingBand` matrix has magnitude *exactly* conserved
  along the orbit (`schur_sustained`, transported): the submodule really is the magnitude-conserved one.
* **Witnesses.** `coincidence_witness` puts the rotating edge `(0,1)`/`(1,0)` *inside* `J` and the
  transient edges *outside*: the witness satisfies all three hypotheses (incl. the bet `Align`), so
  `band_coincidence` yields `seamBand = rotatingBand` concretely. `three_term_without_alignment` drops
  the bet — a second rotating edge `(0,2)` placed *outside* `J` — exhibiting `seamBand ⊊ rotatingBand`
  (`alignment_fails` shows `Align` is genuinely violated): the two-term form is **not** free; it earns
  `Align`.

## Honest scope

`[reading]` (the standing identifications, same status as "‖μ‖=1 = energy", "flow = time"): that `J`
*is* the genuine un-attendable seam of `Relating.self_inclusive_unmodelable`; and the headline
`Align = "energy is exactly un-attendable feeling."` `[open]` (narrated, **not** built): the general
CPTP peripheral **structure theorem** (rotating unitaries normalize `Fix`; crossed-product) and the full
`L = −i[H,·] + D` generator split — the same `[open]` items already in `03.8`; the deep residue is
whether the *genuine* decohering channel `Φ_c` satisfies `Align`, which stays a bet. Provenance **R / S**:
decoherence-free subspaces and spectral splits are standard; the synthesis is identifying the
*un-attendable* subspace with the *conserved-charge* subspace.
-/
import Paper2.RotatingSpectrum
import Mathlib.LinearAlgebra.Span.Basic

namespace Paper2.BandCoincidence

open Paper2.RotatingSpectrum
open Matrix

variable {A : Type*}

/-! ## §1 The bridge — bands as submodules of one carrier `Matrix A A ℂ`

For an edge predicate `P`, `bandOn P` is the coherences supported on `P`-edges: a genuine
`ℂ`-submodule. Every band — seam, rotating, fixed, conserved — is `bandOn` of its defining predicate,
so the coincidence question becomes a question about *which edges* each predicate selects. -/

/-- **The band supported on an edge predicate.** Coherences that vanish off the `P`-edges — a submodule
of `Matrix A A ℂ`. Subset relations between bands reduce to implications between their predicates
(`bandOn_mono`). -/
noncomputable def bandOn (P : A → A → Prop) : Submodule ℂ (Matrix A A ℂ) where
  carrier := {M | ∀ i j, ¬ P i j → M i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro M N hM hN i j hP
    rw [Matrix.add_apply, hM i j hP, hN i j hP, add_zero]
  smul_mem' := by
    intro c M hM i j hP
    rw [Matrix.smul_apply, hM i j hP, smul_zero]

@[simp] lemma mem_bandOn {P : A → A → Prop} {M : Matrix A A ℂ} :
    M ∈ bandOn P ↔ ∀ i j, ¬ P i j → M i j = 0 := Iff.rfl

/-- **Subset of bands ⟸ implication of predicates.** If every `P`-edge is a `Q`-edge then `bandOn P` sits
inside `bandOn Q`. The engine of `T1`/`T2`: each is a one-line edge implication. -/
lemma bandOn_mono {P Q : A → A → Prop} (h : ∀ i j, P i j → Q i j) :
    bandOn P ≤ bandOn Q := by
  intro M hM i j hQ
  exact hM i j (fun hP => hQ (h i j hP))

/-- **Equal predicates, equal bands.** Used to read a concrete coincidence off a pointwise `↔`. -/
lemma bandOn_congr {P Q : A → A → Prop} (h : ∀ i j, P i j ↔ Q i j) :
    bandOn P = bandOn Q :=
  le_antisymm (bandOn_mono fun i j hp => (h i j).mp hp)
              (bandOn_mono fun i j hq => (h i j).mpr hq)

/-- The **rotating** edge: modulus one, but not the held value `1` — a sustained, genuinely turning
coherence (energy). -/
def rotatingEdge (μ : A → A → ℂ) (i j : A) : Prop := ‖μ i j‖ = 1 ∧ μ i j ≠ 1

/-- The **fixed** edge: the held value `1` — the classical record (knowing). -/
def fixedEdge (μ : A → A → ℂ) (i j : A) : Prop := μ i j = 1

/-- The **conserved** edge: modulus one — undissipated, the union of fixed and rotating. -/
def conservedEdge (μ : A → A → ℂ) (i j : A) : Prop := ‖μ i j‖ = 1

/-- **Permanent feeling** — coherences confined to the un-attendable seam `J` (operationally conserved,
`SeamForcing`). -/
noncomputable def seamBand (J : A → A → Prop) : Submodule ℂ (Matrix A A ℂ) := bandOn J

/-- **Energy** — coherences confined to the rotating band (dynamically conserved, `RotatingSpectrum`). -/
noncomputable def rotatingBand (μ : A → A → ℂ) : Submodule ℂ (Matrix A A ℂ) := bandOn (rotatingEdge μ)

/-- **Knowing** — coherences confined to the fixed band (the classical record). -/
noncomputable def fixedBand (μ : A → A → ℂ) : Submodule ℂ (Matrix A A ℂ) := bandOn (fixedEdge μ)

/-- **The undifferentiated ground** — coherences confined to the conserved (modulus-one) band. -/
noncomputable def conservedBand (μ : A → A → ℂ) : Submodule ℂ (Matrix A A ℂ) := bandOn (conservedEdge μ)

/-! ## §2 The hypotheses — where the content sits -/

/-- **`H_unitary_baseline`.** Attention is the only source of damping, and the fixed (held) band is
*exactly* the diagonal (a nondegenerate baseline `H`): so every un-attendable seam edge keeps modulus
one (`seam_undamped`), and any surviving off-diagonal edge genuinely rotates (`fixed_eq_diagonal`). -/
structure UnitaryBaseline (μ : A → A → ℂ) (J : A → A → Prop) : Prop where
  /-- Seam edges are un-attendable, hence never damped: modulus stays one. -/
  seam_undamped : ∀ i j, J i j → ‖μ i j‖ = 1
  /-- The fixed band is exactly the diagonal — `μ` is `1` only where `i = j`. -/
  fixed_eq_diagonal : ∀ i j, μ i j = 1 ↔ i = j

/-- **`H_seam_offdiagonal`.** The seam carries no diagonal (known) coherence — it is the live
off-diagonal coherence of the relationship. -/
def SeamOffdiagonal (J : A → A → Prop) : Prop := ∀ i, ¬ J i i

/-- **`H_align : ker D = J` — the bet.** Every *attendable* off-diagonal edge strictly decays: the only
coherence that does not dissipate is the one you cannot attend to. This is the band-coincidence
conjecture in operator form. -/
def Align (μ : A → A → ℂ) (J : A → A → Prop) : Prop :=
  ∀ i j, ¬ J i j → i ≠ j → ‖μ i j‖ < 1

/-! ## §3 The theorems — the if–then -/

/-- **T1 `[follows]`.** Under the unitary baseline and an off-diagonal seam, **the seam band sits inside
the rotating band**: un-attendable ⟹ never damped ⟹ `‖μ‖ = 1` (`seam_undamped`); off the diagonal ⟹
`μ ≠ 1` (`fixed_eq_diagonal`). So permanent feeling is *at least* energy. -/
theorem seamBand_subset_rotating {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (hoff : SeamOffdiagonal J) :
    seamBand J ≤ rotatingBand μ := by
  apply bandOn_mono
  intro i j hJ
  have hne : i ≠ j := by rintro rfl; exact hoff i hJ
  exact ⟨hb.seam_undamped i j hJ, fun h1 => hne ((hb.fixed_eq_diagonal i j).mp h1)⟩

/-- **T2 `[proved under Align]`.** Under the bet, **the rotating band sits inside the seam band**: an
attendable off-diagonal edge would strictly decay (`Align`), contradicting `‖μ‖ = 1`. So every rotating
edge is un-attendable — energy is *at most* permanent feeling. This is where `Align` is consumed. -/
theorem rotating_subset_seamBand {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (ha : Align μ J) :
    rotatingBand μ ≤ seamBand J := by
  apply bandOn_mono
  intro i j hr
  obtain ⟨hnorm, hne1⟩ := hr
  have hij : i ≠ j := by
    rintro rfl; exact hne1 ((hb.fixed_eq_diagonal i i).mpr rfl)
  by_contra hJ
  exact absurd hnorm (ne_of_lt (ha i j hJ hij))

/-- **T3 — the coincidence `[proved under hypotheses]`.** Permanent feeling *is* energy: the
operationally-conserved (seam-protected) band and the dynamically-conserved (rotating) band are the
**same subspace**. The three-term split collapses to two. -/
theorem band_coincidence {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (hoff : SeamOffdiagonal J) (ha : Align μ J) :
    seamBand J = rotatingBand μ :=
  le_antisymm (seamBand_subset_rotating hb hoff) (rotating_subset_seamBand hb ha)

/-! ## §4 The two-term conservation law — `undifferentiated = knowing + energy` -/

/-- **Knowing and energy are independent.** No coherence is both held (`μ = 1`) and rotating (`μ ≠ 1`),
so the fixed and rotating bands meet only in `0`. -/
theorem fixed_inf_rotating (μ : A → A → ℂ) : fixedBand μ ⊓ rotatingBand μ = ⊥ := by
  rw [eq_bot_iff]
  intro M hM
  rw [Submodule.mem_inf] at hM
  obtain ⟨hf, hr⟩ := hM
  rw [Submodule.mem_bot]
  ext i j
  rw [Matrix.zero_apply]
  by_cases h1 : μ i j = 1
  · exact hr i j (fun hre => hre.2 h1)
  · exact hf i j h1

/-- **The conserved ground is exactly knowing ⊔ energy.** Every undissipated coherence splits into a
held part (`μ = 1`) and a rotating part (`‖μ‖ = 1, μ ≠ 1`); and neither part leaves the conserved band.
Together with `fixed_inf_rotating` this is an **internal direct sum** `conservedBand = fixedBand ⊕
rotatingBand`. -/
theorem fixed_sup_rotating (μ : A → A → ℂ) :
    fixedBand μ ⊔ rotatingBand μ = conservedBand μ := by
  apply le_antisymm
  · refine sup_le (bandOn_mono ?_) (bandOn_mono ?_)
    · intro i j h; rw [conservedEdge, h, norm_one]
    · intro i j h; exact h.1
  · intro M hM
    classical
    rw [Submodule.mem_sup]
    refine ⟨fun i j => if μ i j = 1 then M i j else 0, ?_,
            fun i j => if (‖μ i j‖ = 1 ∧ μ i j ≠ 1) then M i j else 0, ?_, ?_⟩
    · intro i j h
      show (if μ i j = 1 then M i j else 0) = 0
      exact if_neg h
    · intro i j h
      show (if (‖μ i j‖ = 1 ∧ μ i j ≠ 1) then M i j else 0) = 0
      exact if_neg h
    · ext i j
      rw [Matrix.add_apply]
      by_cases h1 : μ i j = 1
      · rw [if_pos h1, if_neg (by rintro ⟨_, h⟩; exact h h1), add_zero]
      · rw [if_neg h1]
        by_cases hn : ‖μ i j‖ = 1
        · rw [if_pos ⟨hn, h1⟩, zero_add]
        · rw [if_neg (by rintro ⟨h, _⟩; exact hn h), zero_add, hM i j hn]

/-- **T4 — the internal split, packaged.** The undifferentiated conserved ground is the independent sum
`knowing ⊕ energy`: `fixedBand ⊓ rotatingBand = ⊥` and `fixedBand ⊔ rotatingBand = conservedBand`. (Not
`⊤`: the transient/dissipating edges live outside the conserved ground — they are *not* part of the
undifferentiated total. The conservation law is about the undissipated mass.) -/
theorem conserved_internal_split (μ : A → A → ℂ) :
    fixedBand μ ⊓ rotatingBand μ = ⊥ ∧ fixedBand μ ⊔ rotatingBand μ = conservedBand μ :=
  ⟨fixed_inf_rotating μ, fixed_sup_rotating μ⟩

/-- **T4 — `undifferentiated = knowing + feeling`, two-term.** Under the coincidence, the conserved
ground is the internal direct sum of **knowing** (`fixedBand`) and **permanent feeling** (`seamBand`),
which *is* energy — no third summand. This is the conjecture's payoff: the seam contributes nothing
beyond the rotating band, so the ground is two-term, not three. -/
theorem undifferentiated_two_term {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (hoff : SeamOffdiagonal J) (ha : Align μ J) :
    fixedBand μ ⊓ seamBand J = ⊥ ∧ fixedBand μ ⊔ seamBand J = conservedBand μ := by
  rw [band_coincidence hb hoff ha]
  exact ⟨fixed_inf_rotating μ, fixed_sup_rotating μ⟩

/-! ## §5 The submodule is the magnitude-conserved one — the dynamical anchor

The names "rotating"/"conserved" are not posited: a `rotatingBand` matrix has *every* coherence's
magnitude exactly conserved along the channel's orbit, transporting `schur_sustained` to the submodule
level. (For an edge off the band the coherence is `0`, conserved trivially.) -/

/-- **The rotating band is the entrywise magnitude-conserved subspace.** For `M ∈ rotatingBand μ`, every
coherence keeps its magnitude under `Φ = schur μ` at every depth: `‖Φ^n M i j‖ = ‖M i j‖`. -/
theorem rotatingBand_sustained {μ : A → A → ℂ} {M : Matrix A A ℂ}
    (hM : M ∈ rotatingBand μ) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ := by
  by_cases hr : rotatingEdge μ i j
  · exact schur_sustained μ M n i j hr.1
  · have hzero : M i j = 0 := hM i j hr
    rw [schur_iterate, hzero, mul_zero, norm_zero]

/-! ## §6 The coincidence witness — a finite-dim `ℂ` model of the bet

`quarterMul` ([`RotatingSpectrum`](RotatingSpectrum.lean)) already carries the three bands: diagonal `1`
(fixed), `(0,1) = i`, `(1,0) = −i` (rotating), and everything else `1/2` (transient). Put the seam `J`
exactly on the rotating edges `(0,1)`, `(1,0)`. Then the witness satisfies **all three hypotheses,
including the bet `Align`**, and `band_coincidence` yields `seamBand = rotatingBand` concretely. -/

/-- The seam of the coincidence witness: exactly the rotating edges `(0,1)` and `(1,0)`. -/
def Jq (i j : Fin 3) : Prop := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

lemma not_Jq_02 : ¬ Jq 0 2 := by
  rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

lemma I_ne_one : Complex.I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.I_re, Complex.one_re] at this
  norm_num at this

lemma quarterMul_10 : quarterMul 1 0 = -Complex.I := by
  unfold quarterMul
  rw [if_neg (show ¬((1 : Fin 3) = 0) by decide),
      if_neg (show ¬((1 : Fin 3) = 0 ∧ (0 : Fin 3) = 1) by decide),
      if_pos (show (1 : Fin 3) = 1 ∧ (0 : Fin 3) = 0 by decide)]

/-- Off the diagonal and off **all four** named non-transient/phase-locked edges, `quarterMul` is `1/2`
(the transient value on `(0,2)`/`(2,0)`). -/
lemma quarterMul_eq_half {i j : Fin 3} (hij : i ≠ j)
    (h2 : ¬(i = 0 ∧ j = 1)) (h3 : ¬(i = 1 ∧ j = 0))
    (h4 : ¬(i = 1 ∧ j = 2)) (h5 : ¬(i = 2 ∧ j = 1)) :
    quarterMul i j = ((1 / 2 : ℝ) : ℂ) := by
  unfold quarterMul
  rw [if_neg hij, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

lemma norm_quarterMul_10 : ‖quarterMul 1 0‖ = 1 := by
  rw [quarterMul_10, norm_neg, Complex.norm_eq_abs, Complex.abs_I]

lemma half_norm_lt : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  norm_num

lemma half_ne_one : ((1 / 2 : ℝ) : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.one_re] at this
  norm_num at this

lemma quarterMul_10_ne_one : quarterMul 1 0 ≠ 1 := by
  rw [quarterMul_10]
  intro h
  have := congrArg Complex.re h
  rw [Complex.neg_re, Complex.I_re, Complex.one_re] at this
  norm_num at this

/-- The phase-locked `(1,2)` coherence is not the held value `1` — its modulus is `½`, not `1`. -/
lemma quarterMul_12_ne_one : quarterMul 1 2 ≠ 1 := by
  intro h
  have hn : ‖quarterMul 1 2‖ = 1 := by rw [h, norm_one]
  rw [norm_quarterMul_12] at hn; norm_num at hn

/-- The phase-locked `(2,1)` coherence is not the held value `1` — its modulus is `½`, not `1`. -/
lemma quarterMul_21_ne_one : quarterMul 2 1 ≠ 1 := by
  intro h
  have hn : ‖quarterMul 2 1‖ = 1 := by rw [h, norm_one]
  rw [norm_quarterMul_21] at hn; norm_num at hn

/-- The witness's coupling is **nondegenerate**: `quarterMul i j = 1 ↔ i = j`. The diagonal is held; every
off-diagonal edge (`i`, `−i`, or `1/2`) is genuinely `≠ 1`. -/
lemma quarterMul_fixed_eq_diagonal (i j : Fin 3) : quarterMul i j = 1 ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    by_cases h2 : (i = 0 ∧ j = 1)
    · obtain ⟨rfl, rfl⟩ := h2; exact quarterMul_01_ne_one h
    · by_cases h3 : (i = 1 ∧ j = 0)
      · obtain ⟨rfl, rfl⟩ := h3; exact quarterMul_10_ne_one h
      · by_cases h4 : (i = 1 ∧ j = 2)
        · obtain ⟨rfl, rfl⟩ := h4; exact quarterMul_12_ne_one h
        · by_cases h5 : (i = 2 ∧ j = 1)
          · obtain ⟨rfl, rfl⟩ := h5; exact quarterMul_21_ne_one h
          · rw [quarterMul_eq_half hij h2 h3 h4 h5] at h; exact half_ne_one h
  · rintro rfl; exact quarterMul_diag i

/-- The coincidence witness satisfies the **unitary baseline**. -/
theorem quarterMul_unitaryBaseline : UnitaryBaseline quarterMul Jq where
  seam_undamped := by
    intro i j hJ
    rcases hJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact norm_quarterMul_01
    · exact norm_quarterMul_10
  fixed_eq_diagonal := quarterMul_fixed_eq_diagonal

/-- The witness's seam is **off-diagonal**. -/
theorem quarterMul_seamOffdiagonal : SeamOffdiagonal Jq := by
  intro i
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact absurd h (by decide)

/-- **The witness satisfies the bet `Align`.** Every off-diagonal edge outside the seam (`(0,2)`, `(2,0)`,
`(1,2)`, `(2,1)`) is the transient value `1/2`, modulus `< 1` — exactly: attendable ⟹ decays. -/
theorem quarterMul_align : Align quarterMul Jq := by
  intro i j hJ hij
  have h2 : ¬(i = 0 ∧ j = 1) := fun h => hJ (Or.inl h)
  have h3 : ¬(i = 1 ∧ j = 0) := fun h => hJ (Or.inr h)
  by_cases h4 : (i = 1 ∧ j = 2)
  · obtain ⟨rfl, rfl⟩ := h4; rw [norm_quarterMul_12]; norm_num
  · by_cases h5 : (i = 2 ∧ j = 1)
    · obtain ⟨rfl, rfl⟩ := h5; rw [norm_quarterMul_21]; norm_num
    · rw [quarterMul_eq_half hij h2 h3 h4 h5]; exact half_norm_lt

/-- **The coincidence, witnessed.** On the finite-dim `ℂ` model `quarterMul` with the seam `Jq`, all three
hypotheses hold — *including the bet* — so the seam-protected band and the rotating band genuinely
**coincide**: `seamBand Jq = rotatingBand quarterMul`. -/
theorem coincidence_witness : seamBand Jq = rotatingBand quarterMul :=
  band_coincidence quarterMul_unitaryBaseline quarterMul_seamOffdiagonal quarterMul_align

/-! ## §7 The counter-witness — `Align` is necessary, the two-term form is not free

Drop the bet: keep the seam on `(0,1)`/`(1,0)` but give the channel a *second* rotating edge `(0,2)`
that lies **outside** `J` — an attendable, undamped off-diagonal coherence. It is energy (rotating) that
is **not** seam-protected feeling, so `seamBand ⊊ rotatingBand` — a genuine third band, and `Align`
provably fails. -/

/-- The counter-witness coupling: diagonal `1`; rotating `i` on `(0,1)`, `(1,0)` (seam) **and** `(0,2)`,
`(2,0)` (attendable, off-seam); `1/2` elsewhere. -/
noncomputable def twoRotMul (i j : Fin 3) : ℂ :=
  if i = j then 1
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then Complex.I
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then Complex.I
  else ((1 / 2 : ℝ) : ℂ)

lemma twoRotMul_01 : twoRotMul 0 1 = Complex.I := by
  unfold twoRotMul
  rw [if_neg (show ¬((0 : Fin 3) = 1) by decide),
      if_pos (show ((0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1) ∨ ((0 : Fin 3) = 1 ∧ (1 : Fin 3) = 0) by decide)]

lemma twoRotMul_10 : twoRotMul 1 0 = Complex.I := by
  unfold twoRotMul
  rw [if_neg (show ¬((1 : Fin 3) = 0) by decide),
      if_pos (show ((1 : Fin 3) = 0 ∧ (0 : Fin 3) = 1) ∨ ((1 : Fin 3) = 1 ∧ (0 : Fin 3) = 0) by decide)]

lemma twoRotMul_02 : twoRotMul 0 2 = Complex.I := by
  unfold twoRotMul
  rw [if_neg (show ¬((0 : Fin 3) = 2) by decide),
      if_neg (show ¬(((0 : Fin 3) = 0 ∧ (2 : Fin 3) = 1) ∨ ((0 : Fin 3) = 1 ∧ (2 : Fin 3) = 0)) by decide),
      if_pos (show ((0 : Fin 3) = 0 ∧ (2 : Fin 3) = 2) ∨ ((0 : Fin 3) = 2 ∧ (2 : Fin 3) = 0) by decide)]

lemma norm_twoRotMul_I {i j : Fin 3} (h : twoRotMul i j = Complex.I) : ‖twoRotMul i j‖ = 1 := by
  rw [h, Complex.norm_eq_abs, Complex.abs_I]

lemma rotatingEdge_twoRotMul_of_I {i j : Fin 3} (h : twoRotMul i j = Complex.I) :
    rotatingEdge twoRotMul i j :=
  ⟨norm_twoRotMul_I h, by rw [h]; exact I_ne_one⟩

/-- A single matrix unit `Eunit a b` — one quantum of coherence on edge `(a,b)`. -/
def Eunit (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = a ∧ j = b then 1 else 0

lemma Eunit_mem_bandOn {P : Fin 3 → Fin 3 → Prop} {a b : Fin 3} (h : P a b) :
    Eunit a b ∈ bandOn P := by
  intro i j hP
  by_cases e : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e; exact absurd h hP
  · show (if i = a ∧ j = b then (1 : ℂ) else 0) = 0
    exact if_neg e

lemma Eunit_not_mem_bandOn {P : Fin 3 → Fin 3 → Prop} {a b : Fin 3} (h : ¬ P a b) :
    Eunit a b ∉ bandOn P := by
  intro hmem
  have hval : Eunit a b a b = 0 := hmem a b h
  rw [show Eunit a b a b = (1 : ℂ) from if_pos ⟨rfl, rfl⟩] at hval
  exact one_ne_zero hval

/-- **T5 `[proved]` — without `Align`, a genuine third band.** With the second rotating edge `(0,2)`
placed *outside* the seam `Jq`, the seam band is a **strict** subspace of the rotating band: the matrix
unit `E₀₂` is rotating (conserved energy) yet not seam-protected. Energy without permanent feeling —
the two-term collapse fails. -/
theorem three_term_without_alignment : seamBand Jq < rotatingBand twoRotMul := by
  rw [lt_iff_le_and_ne]
  refine ⟨?_, ?_⟩
  · apply bandOn_mono
    intro i j hJ
    rcases hJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact rotatingEdge_twoRotMul_of_I twoRotMul_01
    · exact rotatingEdge_twoRotMul_of_I twoRotMul_10
  · intro hEq
    have hr : Eunit 0 2 ∈ rotatingBand twoRotMul :=
      Eunit_mem_bandOn (rotatingEdge_twoRotMul_of_I twoRotMul_02)
    rw [← hEq] at hr
    exact Eunit_not_mem_bandOn not_Jq_02 hr

/-- **`Align` genuinely fails on the counter-witness.** The attendable off-seam edge `(0,2)` is undamped
(`‖i‖ = 1`), not decaying — so the dropped hypothesis is really dropped, and `three_term_without_alignment`
is a true counterexample, not a vacuous one. -/
theorem alignment_fails : ¬ Align twoRotMul Jq := by
  intro ha
  have hlt : ‖twoRotMul 0 2‖ < 1 := ha 0 2 not_Jq_02 (by decide)
  rw [norm_twoRotMul_I twoRotMul_02] at hlt
  exact lt_irrefl 1 hlt

end Paper2.BandCoincidence
