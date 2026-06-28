/-
# The rotating peripheral spectrum — energy as the conserved half of the generator (Parts 2–3)

The spec's **keystone**. `TimeFlow`/`TimeArrow` captured the purely *dissipative* extreme: over the
real, self-adjoint model every coherence off the fixed set **decays** (`idempotent_eigenvalue`,
`dephase_no_rotating_peripheral` — there is no eigenvalue of modulus `1` other than `1`). That is pure
arrow, no energy. Energy lives in the sector that model excludes: the **rotating peripheral band**, a
modulus-one, non-`1` eigenvalue, which requires non-self-adjoint dynamics over `ℂ`.

Per the spec's discipline (mirror `TimeFlow`): not the general Perron–Frobenius/peripheral structure
theorem first (mathlib has none of it), but **one genuine instance**, concrete and `sorry`-free,
exhibiting all three spectral bands at once under a single channel `Φ` on `Matrix (Fin 3) ℂ`:

* **fixed** (`Φ U = U`) — the known / classical / self band (the diagonal);
* **rotating** (`Φ U = e^{iθ} U`, `|e^{iθ}| = 1`, `θ ≠ 0`) — sustained, magnitude **never decays**:
  conserved oscillating coherence, *reversible time*;
* **transient** (`Φ U = r U`, `r < 1`) — the passing feeling, the `TimeFlow` arrow.

## Construction (the `ℂ`-lift of `Space.wDephase` / `TimeFlow.partialDephase`)

`schur μ` is the **phase-damping channel**: a Schur (entrywise) multiplier `M i j ↦ μ i j · M i j`. Its
matrix units are eigen-operators, eigenvalue `μ i j`, so `schur μ ^[n] M i j = (μ i j)^n · M i j`
(`schur_iterate`) — the geometric law of `TimeFlow`, now complex-valued and edge-resolved. The band of
an edge is read off `‖μ i j‖`: `= 1` rotating/fixed (`schur_sustained` — magnitude exactly conserved),
`< 1` transient (`schur_transient_tendsto` — magnitude `→ 0`).

The concrete witness `quarterMul` is the **quarter-turn channel** on `Matrix (Fin 3) ℂ`: diagonal `1`
(fixed); `μ_{01} = i = e^{iπ/2}` (rotating — `‖i‖ = 1`, `i ≠ 1`); `μ_{02} = 1/2` (transient). The
coherence `U = E₀₁` satisfies `Φ U = i · U` (`phaseChannel_eigen`): a genuine rotating eigen-operator,
sustained (`rotating_sustained` — `‖Φ^n U‖ = ‖U‖` for all `n`) while the `(0,2)` coherence decays
(`transient_decays`).

## Part 3 — energy, as a reading over the instance (`[reading]`)

Write each eigenvalue as `μ = exp(s)`, so `s = log μ` is the per-step **generator** with `Re s = log‖μ‖`
and `Im s = arg μ`. The rotating band has `‖μ‖ = 1`, i.e. `Re s = 0`: pure phase, `s = iθ` with `θ` the
**frequency / energy**, conserved (`energy_conserved`; `energy_conserved_generator` —
`Re(log μ₀₁) = 0`; `frequency_nonzero` — `Im(log μ₀₁) = π/2 ≠ 0`). The transient band has `‖μ‖ < 1`,
i.e. `Re s < 0`: the gap, the decay, the **arrow** (`arrow_dissipates`; `arrow_negative_generator` —
`Re(log μ₀₂) < 0`). One channel, two halves of its spectrum: **energy = `Im(spec L)` (the conserved,
modulus-one band); arrow = `Re(spec L) < 0` (the decaying band)** — a literal pair of theorems about
the generator `L = log μ` (`energy_arrow_split` at the modulus level, `energy_arrow_spectrum` at the
generator level). Energy is what relational time is the flow of; the arrow is what it dissipates. Two
further readings sit over the eigen-operator's orbit: **energy as frequency** — the phase winds at a
constant rate `Φ^n U = i^n U` (`rotating_winds`, the `E = ℏω` reading) — and **energy as reversibility /
recurrence** — the mode runs a closed periodic orbit `Φ⁴ U = U` (`rotating_recurs`), unlike the
transient's monotone decay.

## Honest scope

`[proved]`: a concrete `ℂ` channel with a genuine rotating eigen-operator (sustained) and a transient
one (decaying) coexisting — the three-way split, witnessed; **and** that the witness multiplier is
positive semidefinite (`quarterMul_posSemidef`), hence a *bona fide* completely-positive (Schur product
theorem), unit-diagonal channel — so the energy band sits inside genuine physics. `[reading]`: that the
rotating phase *is* energy and its conservation *is* energy conservation (PSD earns *"physical channel,"*
not *"= energy"*). `[open]` (narrated, not built): the general peripheral **structure theorem** for CPTP
maps (the rotating unitaries normalize `Fix`, a crossed-product structure), and the `L = −i[H,·] + D`
generator split in full. The witness needs none of it — exactly as `TimeFlow`'s `partialDephase` needed
none of the general decay theory.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Paper2.RotatingSpectrum

open Matrix Filter Topology
open scoped ComplexOrder

/-! ## §1 The phase-damping channel — the `ℂ`-lift of the dephasing flow -/

variable {A : Type*}

/-- **The phase-damping channel.** A Schur (entrywise) multiplier `M i j ↦ μ i j · M i j` on complex
matrices — the `ℂ`-valued, edge-resolved generalization of `Space.wDephase` / `TimeFlow.partialDephase`.
With `‖μ i j‖ = 1` it is a *phase rotation* of the `(i,j)` coherence (no decay); with `‖μ i j‖ < 1` it
*damps* it. Both at once is what carries a rotating band beside a transient one. -/
def schur (μ : A → A → ℂ) (M : Matrix A A ℂ) : Matrix A A ℂ := fun i j => μ i j * M i j

@[simp] lemma schur_apply (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A) :
    schur μ M i j = μ i j * M i j := rfl

/-- **The eigen-operator law along the orbit.** Each matrix unit is an eigen-operator of `schur μ` with
eigenvalue `μ i j`, so the `(i,j)` coherence after `n` closures of the loop is `(μ i j)^n · M i j`
exactly — `TimeFlow`'s geometric monovariant, now complex and per edge. -/
lemma schur_iterate (μ : A → A → ℂ) (M : Matrix A A ℂ) (n : ℕ) (i j : A) :
    (schur μ)^[n] M i j = (μ i j) ^ n * M i j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      show μ i j * (schur μ)^[n] M i j = (μ i j) ^ (n + 1) * M i j
      rw [ih, pow_succ]; ring

/-- **Fixed band.** Where the edge multiplier is `1`, the coherence is held exactly: `μ i j = 1 ⟹
Φ^n M i j = M i j`. The known / classical / self part (the diagonal, since `μ i i = 1`). -/
lemma schur_fixed (μ : A → A → ℂ) (M : Matrix A A ℂ) (n : ℕ) (i j : A) (h : μ i j = 1) :
    (schur μ)^[n] M i j = M i j := by
  rw [schur_iterate, h, one_pow, one_mul]

/-- **Rotating / conserved band.** Where the edge multiplier has modulus `1`, the coherence's
**magnitude is exactly conserved** for all `n`: `‖μ i j‖ = 1 ⟹ ‖Φ^n M i j‖ = ‖M i j‖`. It *rotates*
(the phase turns) but never decays — sustained oscillating coherence, the spectral home of energy. -/
lemma schur_sustained (μ : A → A → ℂ) (M : Matrix A A ℂ) (n : ℕ) (i j : A) (h : ‖μ i j‖ = 1) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ := by
  rw [schur_iterate, norm_mul, norm_pow, h, one_pow, one_mul]

/-- **Transient band, the exact law.** Where the edge multiplier has modulus `< 1`, the coherence's
magnitude is `‖μ i j‖^n · ‖M i j‖`. -/
lemma schur_transient_norm (μ : A → A → ℂ) (M : Matrix A A ℂ) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖μ i j‖ ^ n * ‖M i j‖ := by
  rw [schur_iterate, norm_mul, norm_pow]

/-- **Transient band decays.** `‖μ i j‖ < 1 ⟹ ‖Φ^n M i j‖ → 0`: the passing feeling, the `TimeFlow`
arrow, in the complex model. -/
lemma schur_transient_tendsto (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A) (h : ‖μ i j‖ < 1) :
    Tendsto (fun n => ‖(schur μ)^[n] M i j‖) atTop (𝓝 0) := by
  have heq : (fun n => ‖(schur μ)^[n] M i j‖) = fun n => ‖μ i j‖ ^ n * ‖M i j‖ := by
    funext n; exact schur_transient_norm μ M n i j
  rw [heq]
  have h0 : Tendsto (fun n => ‖μ i j‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rwa [norm_norm])
  simpa using h0.mul_const (‖M i j‖)

/-! ## §2 The concrete witness — the quarter-turn channel on `Matrix (Fin 3) ℂ`

`quarterMul` puts a fixed band on the diagonal, a **rotating** band (eigenvalue `i = e^{iπ/2}`) on the
`(0,1)` coherence, and a **transient** band (`1/2`) on the rest. All three coexist under one channel. -/

/-- The quarter-turn multiplier: diagonal `1` (fixed); `μ_{01} = i`, `μ_{10} = −i` (rotating, `e^{±iπ/2}`);
the `(1,2)`/`(2,1)` coherences **phase-locked** at `∓i·½` and the `(0,2)`/`(2,0)` ones at `½` (all
transient, modulus `½`). The phase-lock is **not** cosmetic: it is exactly what makes the multiplier a
positive-semidefinite (hence completely positive — `quarterMul_posSemidef`) channel. With the naive `½` on
`(1,2)` the multiplier fails to be PSD, so the conserved relative phase of the `(0,1)` band *disciplines*
how the remaining coherences may decohere — a decoherence-free-subspace constraint, not a free choice. -/
noncomputable def quarterMul (i j : Fin 3) : ℂ :=
  if i = j then 1
  else if i = 0 ∧ j = 1 then Complex.I
  else if i = 1 ∧ j = 0 then -Complex.I
  else if i = 1 ∧ j = 2 then -Complex.I * ((1 / 2 : ℝ) : ℂ)
  else if i = 2 ∧ j = 1 then Complex.I * ((1 / 2 : ℝ) : ℂ)
  else ((1 / 2 : ℝ) : ℂ)

lemma quarterMul_diag (i : Fin 3) : quarterMul i i = 1 := by
  simp [quarterMul]

lemma quarterMul_01 : quarterMul 0 1 = Complex.I := by
  unfold quarterMul
  rw [if_neg (show ¬((0 : Fin 3) = 1) by decide),
      if_pos (show (0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1 by decide)]

lemma quarterMul_02 : quarterMul 0 2 = ((1 / 2 : ℝ) : ℂ) := by
  unfold quarterMul
  rw [if_neg (show ¬((0 : Fin 3) = 2) by decide),
      if_neg (show ¬((0 : Fin 3) = 0 ∧ (2 : Fin 3) = 1) by decide),
      if_neg (show ¬((0 : Fin 3) = 1 ∧ (2 : Fin 3) = 0) by decide),
      if_neg (show ¬((0 : Fin 3) = 1 ∧ (2 : Fin 3) = 2) by decide),
      if_neg (show ¬((0 : Fin 3) = 2 ∧ (2 : Fin 3) = 1) by decide)]

lemma quarterMul_12 : quarterMul 1 2 = -Complex.I * ((1 / 2 : ℝ) : ℂ) := by
  unfold quarterMul
  rw [if_neg (show ¬((1 : Fin 3) = 2) by decide),
      if_neg (show ¬((1 : Fin 3) = 0 ∧ (2 : Fin 3) = 1) by decide),
      if_neg (show ¬((1 : Fin 3) = 1 ∧ (2 : Fin 3) = 0) by decide),
      if_pos (show (1 : Fin 3) = 1 ∧ (2 : Fin 3) = 2 by decide)]

lemma quarterMul_21 : quarterMul 2 1 = Complex.I * ((1 / 2 : ℝ) : ℂ) := by
  unfold quarterMul
  rw [if_neg (show ¬((2 : Fin 3) = 1) by decide),
      if_neg (show ¬((2 : Fin 3) = 0 ∧ (1 : Fin 3) = 1) by decide),
      if_neg (show ¬((2 : Fin 3) = 1 ∧ (1 : Fin 3) = 0) by decide),
      if_neg (show ¬((2 : Fin 3) = 1 ∧ (1 : Fin 3) = 2) by decide),
      if_pos (show (2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 by decide)]

/-- `‖μ_{12}‖ = ½ < 1` — the phase-locked `(1,2)` coherence is transient. -/
lemma norm_quarterMul_12 : ‖quarterMul 1 2‖ = 1 / 2 := by
  rw [quarterMul_12, norm_mul, norm_neg, Complex.norm_eq_abs, Complex.abs_I, one_mul,
      Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- `‖μ_{21}‖ = ½ < 1` — the phase-locked `(2,1)` coherence is transient. -/
lemma norm_quarterMul_21 : ‖quarterMul 2 1‖ = 1 / 2 := by
  rw [quarterMul_21, norm_mul, Complex.norm_eq_abs, Complex.abs_I, one_mul,
      Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- `‖μ_{01}‖ = ‖i‖ = 1` — the `(0,1)` band is on the unit circle (conserved). -/
lemma norm_quarterMul_01 : ‖quarterMul 0 1‖ = 1 := by
  rw [quarterMul_01, Complex.norm_eq_abs, Complex.abs_I]

/-- `‖μ_{02}‖ = 1/2 < 1` — the `(0,2)` band is strictly inside the disk (decaying). -/
lemma norm_quarterMul_02_lt : ‖quarterMul 0 2‖ < 1 := by
  rw [quarterMul_02, Complex.norm_eq_abs, Complex.abs_ofReal,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  norm_num

/-- `μ_{01} = i ≠ 1` — the rotating band is genuinely rotating, **not** fixed: it carries a nonzero
phase (a nonzero frequency). This is what separates *reversible time* (rotating) from the *known* band
(fixed). -/
lemma quarterMul_01_ne_one : quarterMul 0 1 ≠ 1 := by
  rw [quarterMul_01]
  intro h
  have := congrArg Complex.re h
  rw [Complex.I_re, Complex.one_re] at this
  norm_num at this

/-! ### The rotating eigen-operator `U = E₀₁` -/

/-- The `(0,1)` coherence `U = E₀₁`: a single unit of off-diagonal coherence. -/
def Ucoh : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = 0 ∧ j = 1 then 1 else 0

lemma Ucoh_01 : Ucoh 0 1 = 1 := by
  unfold Ucoh
  rw [if_pos (show (0 : Fin 3) = 0 ∧ (1 : Fin 3) = 1 by decide)]

lemma Ucoh_ne_zero : Ucoh ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [Ucoh_01, Matrix.zero_apply] at h01
  exact one_ne_zero h01

/-- **`Φ U = e^{iθ} U` — a genuine rotating eigen-operator.** The quarter-turn channel sends the
coherence `U = E₀₁` to `i · U` (`θ = π/2`): a modulus-one, non-`1` eigenvalue, the rotating peripheral
spectrum the real model provably excludes. -/
theorem phaseChannel_eigen : schur quarterMul Ucoh = Complex.I • Ucoh := by
  ext i j
  by_cases h : i = 0 ∧ j = 1
  · obtain ⟨hi, hj⟩ := h
    subst hi; subst hj
    rw [schur_apply, Matrix.smul_apply, Ucoh_01, quarterMul_01, smul_eq_mul]
  · rw [schur_apply, Matrix.smul_apply, smul_eq_mul]
    have hU : Ucoh i j = 0 := if_neg h
    rw [hU, mul_zero, mul_zero]

/-- **The rotating eigen-operator is sustained.** Its magnitude is exactly conserved at every
return-depth: `‖Φ^n U‖ = ‖U‖` for all `n` (entrywise on the `(0,1)` coherence). It rotates forever and
**never decays** — conserved coherence, in contrast to the transient band below. -/
theorem rotating_sustained (n : ℕ) :
    ‖(schur quarterMul)^[n] Ucoh 0 1‖ = ‖Ucoh 0 1‖ :=
  schur_sustained quarterMul Ucoh n 0 1 norm_quarterMul_01

/-- **The transient band decays.** The `(0,2)` coherence under the same channel tends to `0` — the
arrow, alive beside the conserved rotating band. -/
theorem transient_decays (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Tendsto (fun n => ‖(schur quarterMul)^[n] M 0 2‖) atTop (𝓝 0) :=
  schur_transient_tendsto quarterMul M 0 2 norm_quarterMul_02_lt

/-- **The fixed band is held.** The diagonal `(i,i)` coherence is preserved exactly — the known /
classical / self part, neither rotating nor decaying. -/
theorem fixed_held (M : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ) (i : Fin 3) :
    (schur quarterMul)^[n] M i i = M i i :=
  schur_fixed quarterMul M n i i (quarterMul_diag i)

/-! ## §3 Energy — the conserved half of the spectrum (`[reading]`)

The three bands of one channel are the three aspects of relational dynamics. The rotating band has
modulus exactly `1` (`Re(log μ) = 0`): pure phase, conserved — this is **energy / reversible time**.
The transient band has modulus `< 1` (`Re(log μ) < 0`): the gap, the decay — this is the **arrow**.
Energy and the arrow are the imaginary and real halves of one generator's spectrum. -/

/-- **Energy is conserved.** The rotating band's magnitude is invariant under the flow at every depth —
the conserved spectral datum. Read as energy: the modulus-one band does not dissipate. -/
theorem energy_conserved (n : ℕ) :
    ‖(schur quarterMul)^[n] Ucoh 0 1‖ = ‖Ucoh 0 1‖ :=
  rotating_sustained n

/-- **The arrow dissipates.** The transient band's magnitude decays to `0` — the dissipative half,
the `TimeFlow` arrow. -/
theorem arrow_dissipates (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Tendsto (fun n => ‖(schur quarterMul)^[n] M 0 2‖) atTop (𝓝 0) :=
  transient_decays M

/-- **Energy = the conserved band; arrow = the decaying band — two halves of one generator's
spectrum.** The *same* channel carries a modulus-one (conserved, energy, reversible) band beside a
modulus-`< 1` (decaying, arrow, irreversible) band, and the rotating band is genuinely *off* the fixed
band (`μ_{01} ≠ 1`). This is the spec's unifying frame on one concrete instance: arrow = `Re(spec) < 0`,
energy = the modulus-one (imaginary-spectrum) rotating part, both in the spectrum of one `Φ`. -/
theorem energy_arrow_split :
    ‖quarterMul 0 1‖ = 1 ∧ quarterMul 0 1 ≠ 1 ∧ ‖quarterMul 0 2‖ < 1 :=
  ⟨norm_quarterMul_01, quarterMul_01_ne_one, norm_quarterMul_02_lt⟩

/-! ### The generator `L = log μ` — energy is `Im(spec)`, the arrow is `Re(spec)`

Write the per-step multiplier as the exponential of a generator, `μ = exp(s)`. Then `s = log μ`, and
`Re s = log‖μ‖`, `Im s = arg μ`. The three lemmas below make the spec's "**energy = Im(spec L); arrow
= Re(spec L)**" literal, on the witness: the rotating band's generator is **pure imaginary** (`Re = 0`,
no decay) with a **nonzero frequency** (`Im ≠ 0` — the energy), while the transient band's generator has
**negative real part** (`Re < 0` — the dissipative arrow). Two halves of one generator's spectrum. -/

/-- **Energy is conserved: the rotating generator is pure imaginary** (`Re(log μ₀₁) = 0`). Since
`‖μ₀₁‖ = 1`, its generator has no real (decaying) part — the modulus-one band does not dissipate. -/
theorem energy_conserved_generator : (Complex.log (quarterMul 0 1)).re = 0 := by
  rw [Complex.log_re, quarterMul_01, Complex.abs_I, Real.log_one]

/-- **A genuine frequency: the rotating generator's imaginary part is nonzero** (`Im(log μ₀₁) = arg i =
π/2 ≠ 0`). The rotating band carries a real oscillation — a nonzero energy/frequency — distinguishing
*reversible time* from the static fixed (known) band. -/
theorem frequency_nonzero : (Complex.log (quarterMul 0 1)).im ≠ 0 := by
  rw [Complex.log_im, quarterMul_01, Complex.arg_I]
  positivity

/-- **The arrow is the negative-real part: the transient generator has `Re(log μ₀₂) < 0`** (`log(1/2) =
−log 2 < 0`). The dissipative half of the spectrum — the `TimeFlow` arrow — read off the same generator. -/
theorem arrow_negative_generator : (Complex.log (quarterMul 0 2)).re < 0 := by
  rw [Complex.log_re, quarterMul_02, Complex.abs_ofReal, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  exact Real.log_neg (by norm_num) (by norm_num)

/-- **Energy = `Im(spec L)`, arrow = `Re(spec L)` — the two halves of one generator's spectrum.** The
rotating band's generator is pure imaginary with a nonzero frequency (conserved energy); the transient
band's generator is negative-real (the dissipative arrow). The spec's unifying frame, now a literal pair
of theorems about `L = log μ` on the concrete witness. -/
theorem energy_arrow_spectrum :
    (Complex.log (quarterMul 0 1)).re = 0 ∧ (Complex.log (quarterMul 0 1)).im ≠ 0
      ∧ (Complex.log (quarterMul 0 2)).re < 0 :=
  ⟨energy_conserved_generator, frequency_nonzero, arrow_negative_generator⟩

/-! ### The single generator as one object — arrow = `Re`, energy = `Im`

The spec-VI **collapse**: rather than two stories (a dissipative arrow and a conserved energy), there is
*one* generator `L = log μ` whose real and imaginary parts are the arrow and the energy. `genReal =
Re(log μ) = log‖μ‖ ≤ 0` is the per-step decay rate; `genImag = Im(log μ) = arg μ` is the frequency. The
iterate-magnitude law `‖Φ^n M i j‖ = exp(n · genReal) · ‖M i j‖` makes the dichotomy **exact**:
`genReal < 0` is the decaying arrow (clause A); `genReal = 0` is *exact* magnitude conservation — clause
B's `Peri`, not a positive floor — and on that band the generator is purely imaginary, so **energy is its
imaginary spectrum** (`genImag` on `ker genReal`), the standard energy-as-spectrum-of-the-unitary-generator,
not an `i^n` analogy. This is what lets energy descend from the *single* time reading: arrow and energy are
`Re` and `Im` of `log Φ_c`. -/

/-- **The generator's real part** — the per-step decay rate `Re(log μ) = log‖μ‖ ≤ 0`. The dissipative
(arrow) half of the single generator `log μ`. -/
noncomputable def genReal (μ : A → A → ℂ) (i j : A) : ℝ := (Complex.log (μ i j)).re

/-- **The generator's imaginary part** — the per-step frequency `Im(log μ) = arg μ`. The unitary
(energy) half of the single generator `log μ`. -/
noncomputable def genImag (μ : A → A → ℂ) (i j : A) : ℝ := (Complex.log (μ i j)).im

/-- The decay rate **is** the log-modulus: `genReal μ i j = log‖μ i j‖`. -/
lemma genReal_eq_log_norm (μ : A → A → ℂ) (i j : A) :
    genReal μ i j = Real.log ‖μ i j‖ := by
  rw [genReal, Complex.log_re, ← Complex.norm_eq_abs]

/-- **The iterate-magnitude law, from the generator.** For a live edge (`μ i j ≠ 0`), the `(i,j)`
coherence's magnitude after `n` closures is `exp(n · genReal) · ‖M i j‖` — geometric in `n` at the rate
fixed by the generator's real part. The one law behind both bands: the *sign* of `genReal` decides arrow
vs. conservation. -/
theorem schur_iterate_norm_exp (μ : A → A → ℂ) (M : Matrix A A ℂ) (n : ℕ) (i j : A)
    (h : μ i j ≠ 0) :
    ‖(schur μ)^[n] M i j‖ = Real.exp (n * genReal μ i j) * ‖M i j‖ := by
  have hpos : 0 < ‖μ i j‖ := norm_pos_iff.mpr h
  rw [schur_transient_norm, genReal_eq_log_norm, ← Real.log_pow,
      Real.exp_log (pow_pos hpos n)]

/-- **Exact conservation ⟺ vanishing decay rate.** On a live edge the magnitude is conserved iff the
generator's real part is exactly zero: `genReal = 0 ↔ ‖μ‖ = 1`. This is clause B's `Peri` read through the
generator — *exact* conservation (`genReal = 0`), distinct from the operational positive-floor of
`SeamForcing.self_cannot_fully_decohere` (which only forbids reaching `0`). -/
theorem genReal_eq_zero_iff (μ : A → A → ℂ) (i j : A) (h : μ i j ≠ 0) :
    genReal μ i j = 0 ↔ ‖μ i j‖ = 1 := by
  rw [genReal_eq_log_norm]
  constructor
  · intro h0
    have hpos : 0 < ‖μ i j‖ := norm_pos_iff.mpr h
    have hx := Real.exp_log hpos
    rw [h0, Real.exp_zero] at hx
    exact hx.symm
  · intro h1; rw [h1, Real.log_one]

/-- **Arrow ⟺ negative decay rate.** On a live edge the magnitude decays (`‖μ‖ < 1`) iff the generator's
real part is negative. The dissipative band — clause A. -/
theorem genReal_neg_iff (μ : A → A → ℂ) (i j : A) (h : μ i j ≠ 0) :
    genReal μ i j < 0 ↔ ‖μ i j‖ < 1 := by
  rw [genReal_eq_log_norm]
  constructor
  · intro hlt
    by_contra hge
    push_neg at hge
    exact absurd (Real.log_nonneg hge) (not_le.mpr hlt)
  · intro hlt
    exact Real.log_neg (norm_pos_iff.mpr h) hlt

/-- **Clause B from the generator: `genReal = 0` ⟹ exact magnitude conservation at every depth.** -/
theorem conserved_of_genReal_zero (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A)
    (h : μ i j ≠ 0) (hz : genReal μ i j = 0) (n : ℕ) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ :=
  schur_sustained μ M n i j ((genReal_eq_zero_iff μ i j h).mp hz)

/-- **Clause A from the generator: `genReal < 0` ⟹ the magnitude decays to `0`.** -/
theorem arrow_of_genReal_neg (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A)
    (h : μ i j ≠ 0) (hneg : genReal μ i j < 0) :
    Tendsto (fun n => ‖(schur μ)^[n] M i j‖) atTop (𝓝 0) :=
  schur_transient_tendsto μ M i j ((genReal_neg_iff μ i j h).mp hneg)

/-- **The energy band, as a constructed spectral object.** The off-diagonal edges where the generator's
real part vanishes exactly — `ker(genReal)` off the diagonal. On the witness this is exactly the rotating
band / `conservedOffdiag` (proved in `BandFromAxioms`). -/
def energyEdge (μ : A → A → ℂ) (i j : A) : Prop := genReal μ i j = 0 ∧ i ≠ j

/-- **Energy** — the imaginary spectrum of the single generator, on the band where it is purely unitary
(`genReal = 0`). Not a label on `i^n`: `Im(log Φ_c) = arg μ`, the standard energy-as-spectrum of the
generator of unitary evolution. -/
noncomputable def energy (μ : A → A → ℂ) (i j : A) : ℝ := genImag μ i j

/-- **The witness is everywhere live.** Every entry of `quarterMul` is nonzero (the diagonal `1`, the
rotating `±i`, the transient `½` and phase-locked `±i·½`), so the generator `log(quarterMul i j)` is
well-behaved on every edge. -/
theorem quarterMul_ne_zero (i j : Fin 3) : quarterMul i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [quarterMul, Complex.ext_iff]

/-- **The rotating edge is an energy edge**, with energy `π/2`: `genReal = 0` (conserved) and the energy
`genImag = arg i = π/2` is a genuine frequency. The `(0,1)` band inhabits `energyEdge`. -/
theorem quarterMul_energyEdge_01 : energyEdge quarterMul 0 1 :=
  ⟨energy_conserved_generator, by decide⟩

/-- **The witness energy is `π/2`** — the imaginary spectrum of the generator on the rotating band. -/
theorem energy_quarterMul_01 : energy quarterMul 0 1 = Real.pi / 2 := by
  rw [energy, genImag, quarterMul_01, Complex.log_im, Complex.arg_I]

/-! ### Two further energy readings (`[reading]` over the witness)

Beyond the modulus/generator split, the rotating band supports two more readings of energy, each laid
over a proved fact about the eigen-operator's orbit. -/

/-- **Energy as frequency — the phase winds at a constant rate** (`E = ℏω`). The rotating eigen-operator
advances by a fixed phase factor `i` (a quarter turn, `θ = π/2`) at *every* return-depth:
`Φ^n U = i^n · U`. The winding rate `θ` per closure of the loop is a frequency, and the reading
identifies that frequency with energy — the rotating mode is a clock, and its rate is its energy. (Proved
fact: the uniform winding `Φ^n U = i^n U`; `[reading]`: that the winding rate *is* energy.) -/
theorem rotating_winds (n : ℕ) : (schur quarterMul)^[n] Ucoh = Complex.I ^ n • Ucoh := by
  ext i j
  rw [schur_iterate, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = 0 ∧ j = 1
  · obtain ⟨hi, hj⟩ := h; subst hi; subst hj
    rw [quarterMul_01]
  · have hU : Ucoh i j = 0 := if_neg h
    rw [hU, mul_zero, mul_zero]

/-- **Energy as reversibility / recurrence — a closed periodic orbit.** Because the rotating eigenvalue
`i` has finite order (`i⁴ = 1`), the eigen-operator **returns to itself** after a finite period:
`Φ⁴ U = U`. The energy-carrying mode runs a *closed* orbit — Poincaré recurrence, reversible time — in
sharp contrast to the transient band, whose magnitude decays monotonically and never returns
(`transient_decays`). (Proved fact: the period-4 recurrence `Φ⁴ U = U`; `[reading]`: that this
reversibility is the mark of energy — the conserved datum that makes the dynamics time-reversible.) -/
theorem rotating_recurs : (schur quarterMul)^[4] Ucoh = Ucoh := by
  rw [rotating_winds, Complex.I_pow_four, one_smul]

/-! ## §4 The witness is a genuine channel — a positive-semidefinite multiplier (`[proved]`)

A Schur multiplier `schur μ` is **completely positive** — a legitimate quantum channel, by the Schur
product theorem — exactly when the multiplier matrix `μ` is positive semidefinite; and it is unital /
trace-preserving when `μ` has unit diagonal (which `quarterMul` does, `quarterMul_diag`). We discharge the
PSD condition here, so the energy witness is **physical dynamics**, not merely a linear map. The proof
exhibits `quarterMul` as a Gram matrix `qBᴴ * qB`: its rows are the vectors whose Hermitian inner products
*are* the entries of `quarterMul`. The third coordinate `(√3/2)` and the `(1,2)` phase-lock `−i·½` are
exactly what let the third Gram vector close — the conserved phase of the `(0,1)` band **disciplines** the
transient coherences, a decoherence-free-subspace constraint rather than a free addition. -/

/-- A Gram factor for `quarterMul`: two rows over `Fin 3`. The columns are the vectors whose Hermitian
inner products are the entries of `quarterMul`; the only irrational entry, `(2,2) = ¼ + (√3/2)² = 1`,
uses `√3·√3 = 3`. -/
noncomputable def qB : Matrix (Fin 2) (Fin 3) ℂ :=
  !![1, Complex.I, ((1 / 2 : ℝ) : ℂ); 0, 0, ((Real.sqrt 3 / 2 : ℝ) : ℂ)]

set_option linter.unnecessarySeqFocus false in
/-- **`quarterMul` is a Gram matrix** `qBᴴ * qB`. The nine entries check out by the inner products of the
two rows of `qB`; the `(2,2)` entry `¼ + (√3/2)² = ¼ + ¾ = 1` uses `√3·√3 = 3`. -/
theorem quarterMul_eq_gram :
    (quarterMul : Matrix (Fin 3) (Fin 3) ℂ) = qB.conjTranspose * qB := by
  have key : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [quarterMul, qB, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq] <;>
    norm_num [div_mul_div_comm, key]

/-- **The witness channel is positive semidefinite** — hence completely positive (Schur product theorem),
and with unit diagonal a genuine unital/trace-preserving quantum channel. So the rotating "energy" band
lives inside *bona fide* physics, not a merely formal linear map. (This earns *"physical channel,"* not
*"= energy"*: the energy identification stays the standing `[reading]`.) -/
theorem quarterMul_posSemidef : Matrix.PosSemidef (quarterMul : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [quarterMul_eq_gram]; exact Matrix.posSemidef_conjTranspose_mul_self qB

end Paper2.RotatingSpectrum
