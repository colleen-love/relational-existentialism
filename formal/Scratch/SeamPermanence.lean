/-
# Seam Permanence — the knowing never completes

The keystone of [`03.11-seam-permanence.md`](../../docs/spec/03.11-seam-permanence.md), sequel to
[`TimeFlow`](TimeFlow.lean) / [`SeamForcing`](SeamForcing.lean). `SeamForcing.self_cannot_fully_decohere`
proved the **qualitative** floor: while the seam carries a live coherence, *every* available knowing
leaves positive feeling. This module makes it **quantitative and permanent**: the seam-respecting
attention flow's potential `defectSq` is bounded strictly below by a *fixed positive constant* for
**all** finite return-depth `n`, and converges to the seam mass — not to zero. The flow never reaches
its fixed point; knowing-as-process never completes.

**The flow.** `seamFlow J p = (1−p)·id + p·(attend Jᶜ)` — directed attention at strength `p` aimed at
*everything except* the seam block `J` (the part of the aimer, un-attendable —
`Relating.self_inclusive_unmodelable`, *you cannot aim at the aimer*). It is `TimeFlow.partialDephase`
restricted to the complement: it **fixes the seam coherences** (a bit of you is our relationship,
which is a part of me) and **shrinks the complement** coherences by `(1−p)` each closure.

**The keystone.** `seam_permanence`: for a live seam coherence (`M i₀ j₀ ≠ 0`, `i₀,j₀ ∈ J`, `i₀ ≠ j₀`),
`0 < defectSq (seamFlow J p ^[n] M)` for **all** `n` — a positive floor that never lifts. And the
closed form `defectSq_seamFlow_iterate`: `defectSq (seamFlow^[n] M) = seamMass + ((1−p)²)^n · compMass`,
so the potential **descends geometrically to `seamMass > 0`** (`defectSq_seamFlow_tendsto`), the seam
mass it can never dissolve — the process runs forever toward a floor it never reaches.

**Honest scope.** `[proved]`: the *conditional* — IF a self-inclusive whole carries a live seam
coherence, THEN its seam-respecting knowing-process is permanent (a fixed positive floor for all `n`).
`[reading]`/premise, stated in the spec, not the operator: that the cosmos *satisfies the antecedent*
(is a totality you cannot get outside of, carrying an irreducible coherence). And "for all finite `n`"
is the framework's only form of "forever" — the A2 guard means `n` is internal return-depth, with any
external-clock identification (e.g. "= 13.8 Gyr") a `[reading]` laid on top. The theorem gives
permanence outright; the number is just the clock named.
-/
import Scratch.TimeFlow
import Scratch.SeamForcing

namespace RelExist.SeamPermanence

open RelExist.Decoherence RelExist.SeamForcing RelExist.TimeFlow
open Filter Topology BigOperators Matrix

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## §1 The seam-respecting flow

`seamFlow J p` attends everything outside the seam at strength `p`: it is the convex combination of
the identity (do nothing) and the maximal available knowing `attend Jᶜ = knowSeam J`. The seam block
`J` is fixed (you cannot aim at the aimer); the complement decays geometrically. -/

/-- **The seam-respecting attention flow.** `(1−p)·M + p·(attend Jᶜ M)` — directed attention at
strength `p` aimed at everything *except* the self-inclusive seam `J`. The graded version of
`SeamForcing.knowSeam J` (`p = 1`), the analogue of `TimeFlow.partialDephase` on the complement. -/
def seamFlow (J : Finset A) (p : ℝ) (M : Matrix A A ℝ) : Matrix A A ℝ :=
  (1 - p) • M + p • attend Jᶜ M

/-- **One step, entrywise.** The seam coherences (`i, j ∈ J`) are **fixed**; every other coherence is
scaled by `(1−p)`. (At `p = 1` this is `knowSeam J`: seam kept, complement killed.) -/
lemma copyDefect_seamFlow (J : Finset A) (p : ℝ) (M : Matrix A A ℝ) (i j : A) :
    copyDefect (seamFlow J p M) i j
      = if (i ∈ J ∧ j ∈ J) then copyDefect M i j else (1 - p) * copyDefect M i j := by
  by_cases e : i = j
  · subst e; simp [copyDefect_apply]
  · rw [copyDefect_apply, if_neg e, copyDefect_apply, if_neg e]
    simp only [seamFlow, add_apply, smul_apply, smul_eq_mul, attend_apply]
    by_cases hJ : i ∈ J ∧ j ∈ J
    · obtain ⟨hi, hj⟩ := hJ
      rw [if_pos (Or.inr ⟨Finset.not_mem_compl.mpr hi, Finset.not_mem_compl.mpr hj⟩),
        if_pos (show i ∈ J ∧ j ∈ J from ⟨hi, hj⟩)]
      ring
    · rw [if_neg hJ, if_neg (show ¬ (i = j ∨ (i ∉ (Jᶜ : Finset A) ∧ j ∉ (Jᶜ : Finset A))) from by
        rintro (h | ⟨hi, hj⟩)
        · exact e h
        · exact hJ ⟨Finset.not_mem_compl.mp hi, Finset.not_mem_compl.mp hj⟩)]
      ring

/-- **`n` steps, entrywise.** The seam coherences stay fixed forever; the complement coherences decay
as `(1−p)^n`. This is the microscopic engine of permanence: nothing the flow does ever touches the
seam block. -/
lemma copyDefect_seamFlow_iterate (J : Finset A) (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) (i j : A) :
    copyDefect ((seamFlow J p)^[n] M) i j
      = if (i ∈ J ∧ j ∈ J) then copyDefect M i j else (1 - p) ^ n * copyDefect M i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', copyDefect_seamFlow, ih]
    split_ifs with hJ
    · rfl
    · ring

/-! ## §2 The keystone — Seam Permanence

While the seam carries a live coherence, the potential never reaches zero: a fixed positive floor for
*every* return-depth. The quantitative, permanent form of `self_cannot_fully_decohere`. -/

/-- **The seam coherence is fixed by the flow** — the corollary of the iterate at a seam entry. -/
lemma seam_entry_fixed (J : Finset A) (p : ℝ) (M : Matrix A A ℝ) (n : ℕ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) :
    copyDefect ((seamFlow J p)^[n] M) i j = copyDefect M i j := by
  rw [copyDefect_seamFlow_iterate, if_pos ⟨hi, hj⟩]

/-- **Seam Permanence.** For a **live seam coherence** — `i₀, j₀ ∈ J`, `i₀ ≠ j₀`, `M i₀ j₀ ≠ 0` — the
flow's potential is **strictly positive for all `n`**: `0 < defectSq (seamFlow J p ^[n] M)`. The
knowing never completes — the off-diagonal mass the self cannot dissolve survives every closure of the
loop, at every return-depth. The quantitative, all-`n` lift of `SeamForcing.self_cannot_fully_decohere`
(which gave one available knowing; this gives the whole orbit a uniform positive floor). -/
theorem seam_permanence (J : Finset A) (p : ℝ) (M : Matrix A A ℝ)
    {i₀ j₀ : A} (hi : i₀ ∈ J) (hj : j₀ ∈ J) (hne : i₀ ≠ j₀) (hlive : M i₀ j₀ ≠ 0) (n : ℕ) :
    0 < defectSq ((seamFlow J p)^[n] M) := by
  have hfix : copyDefect ((seamFlow J p)^[n] M) i₀ j₀ = M i₀ j₀ := by
    rw [seam_entry_fixed J p M n hi hj, copyDefect_apply, if_neg hne]
  have hterm : 0 < (copyDefect ((seamFlow J p)^[n] M) i₀ j₀) ^ 2 := by
    rw [hfix]; exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hlive))
  have hle : (copyDefect ((seamFlow J p)^[n] M) i₀ j₀) ^ 2 ≤ defectSq ((seamFlow J p)^[n] M) := by
    rw [defectSq]
    refine le_trans (Finset.single_le_sum
      (f := fun j => (copyDefect ((seamFlow J p)^[n] M) i₀ j) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j₀)) ?_
    exact Finset.single_le_sum
      (f := fun i => ∑ j, (copyDefect ((seamFlow J p)^[n] M) i j) ^ 2)
      (fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i₀)
  exact lt_of_lt_of_le hterm hle

/-- **Knowing-as-process never completes.** Restatement: the potential is never `0`, so the flow never
reaches its fixed point — the descent is unending in the return-depth `n`. -/
theorem never_completes (J : Finset A) (p : ℝ) (M : Matrix A A ℝ)
    {i₀ j₀ : A} (hi : i₀ ∈ J) (hj : j₀ ∈ J) (hne : i₀ ≠ j₀) (hlive : M i₀ j₀ ≠ 0) (n : ℕ) :
    defectSq ((seamFlow J p)^[n] M) ≠ 0 :=
  ne_of_gt (seam_permanence J p M hi hj hne hlive n)

/-! ## §3 The floor in closed form — descent to the seam mass

The potential splits into the **seam mass** (fixed) and the **complement mass** (decaying), so the
descent is geometric down to a positive floor it never reaches. -/

/-- The **seam mass**: the off-diagonal coherence confined to the seam block `J` — the part no
available knowing can touch. -/
def seamMass (J : Finset A) (M : Matrix A A ℝ) : ℝ :=
  ∑ i, ∑ j, if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0

/-- The **complement mass**: the off-diagonal coherence touching outside the seam — the part the flow
decoheres away. -/
def compMass (J : Finset A) (M : Matrix A A ℝ) : ℝ :=
  ∑ i, ∑ j, if (i ∈ J ∧ j ∈ J) then 0 else (copyDefect M i j) ^ 2

omit [Fintype A] in
private lemma ite_seam_nonneg (J : Finset A) (M : Matrix A A ℝ) (i j : A) :
    0 ≤ if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0 := by
  split_ifs <;> positivity

omit [Fintype A] in
private lemma ite_comp_nonneg (J : Finset A) (M : Matrix A A ℝ) (i j : A) :
    0 ≤ if (i ∈ J ∧ j ∈ J) then (0 : ℝ) else (copyDefect M i j) ^ 2 := by
  split_ifs <;> positivity

lemma seamMass_nonneg (J : Finset A) (M : Matrix A A ℝ) : 0 ≤ seamMass J M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ite_seam_nonneg J M i j

lemma compMass_nonneg (J : Finset A) (M : Matrix A A ℝ) : 0 ≤ compMass J M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ite_comp_nonneg J M i j

/-- **The potential splits**: `defectSq = seamMass + compMass` — every off-diagonal coherence is
either in the seam block or touching its complement. -/
theorem defectSq_split (J : Finset A) (M : Matrix A A ℝ) :
    defectSq M = seamMass J M + compMass J M := by
  rw [defectSq, seamMass, compMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **The descent in closed form.** `defectSq (seamFlow J p ^[n] M) = seamMass + ((1−p)²)^n · compMass`:
the seam mass stands fixed while the complement mass decays geometrically at rate `(1−p)²`. The flow
bleeds off exactly the knowable (complement) coherence and leaves the un-knowable (seam) coherence
untouched. -/
theorem defectSq_seamFlow_iterate (J : Finset A) (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) :
    defectSq ((seamFlow J p)^[n] M) = seamMass J M + ((1 - p) ^ 2) ^ n * compMass J M := by
  have hsum : defectSq ((seamFlow J p)^[n] M)
      = ∑ i, ∑ j, ((if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0)
          + ((1 - p) ^ 2) ^ n * (if (i ∈ J ∧ j ∈ J) then 0 else (copyDefect M i j) ^ 2)) := by
    rw [defectSq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [copyDefect_seamFlow_iterate]
    split_ifs with hJ
    · ring
    · rw [mul_pow, pow_right_comm]; ring
  rw [hsum]
  have hinner : ∀ i, (∑ j, ((if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0)
          + ((1 - p) ^ 2) ^ n * (if (i ∈ J ∧ j ∈ J) then 0 else (copyDefect M i j) ^ 2)))
        = (∑ j, if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0)
          + ((1 - p) ^ 2) ^ n * (∑ j, if (i ∈ J ∧ j ∈ J) then 0 else (copyDefect M i j) ^ 2) := by
    intro i; rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [hinner]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, seamMass, compMass]

/-- **`compMass` is the strict knowable part: it decays to zero.** -/
theorem compMass_seamFlow_tendsto (J : Finset A) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (M : Matrix A A ℝ) :
    Tendsto (fun n => ((1 - p) ^ 2) ^ n * compMass J M) atTop (𝓝 0) := by
  have hrate : ‖((1 - p) ^ 2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_pos hp0 (show (0:ℝ) < 2 - p by linarith)]
  have h0 : Tendsto (fun n => ((1 - p) ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hrate
  simpa using h0.mul_const (compMass J M)

/-- **The descent converges to the seam mass, not to zero.** `defectSq (seamFlow J p ^[n] M) →
seamMass J M`: knowing-as-process runs forever *toward* the seam mass, the floor it asymptotically
approaches but — by `seam_permanence` — never reaches while the seam is live. -/
theorem defectSq_seamFlow_tendsto (J : Finset A) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (M : Matrix A A ℝ) :
    Tendsto (fun n => defectSq ((seamFlow J p)^[n] M)) atTop (𝓝 (seamMass J M)) := by
  have h := (tendsto_const_nhds (x := seamMass J M)).add (compMass_seamFlow_tendsto J p hp0 hp1 M)
  rw [add_zero] at h
  exact h.congr (fun n => (defectSq_seamFlow_iterate J p M n).symm)

/-- **The floor is positive iff the seam carries a live coherence.** Forward: a live seam entry forces
`0 < seamMass`, so the limit `defectSq → seamMass` lands strictly above zero — the process never
dissolves the seam. -/
theorem seamMass_pos (J : Finset A) (M : Matrix A A ℝ)
    {i₀ j₀ : A} (hi : i₀ ∈ J) (hj : j₀ ∈ J) (hne : i₀ ≠ j₀) (hlive : M i₀ j₀ ≠ 0) :
    0 < seamMass J M := by
  have hterm : 0 < (if (i₀ ∈ J ∧ j₀ ∈ J) then (copyDefect M i₀ j₀) ^ 2 else 0) := by
    rw [if_pos ⟨hi, hj⟩, copyDefect_apply, if_neg hne]
    exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hlive))
  have hle : (if (i₀ ∈ J ∧ j₀ ∈ J) then (copyDefect M i₀ j₀) ^ 2 else 0) ≤ seamMass J M := by
    rw [seamMass]
    refine le_trans (Finset.single_le_sum
      (f := fun j => if (i₀ ∈ J ∧ j ∈ J) then (copyDefect M i₀ j) ^ 2 else 0)
      (fun k _ => ite_seam_nonneg J M i₀ k) (Finset.mem_univ j₀)) ?_
    exact Finset.single_le_sum
      (f := fun i => ∑ j, if (i ∈ J ∧ j ∈ J) then (copyDefect M i j) ^ 2 else 0)
      (fun k _ => Finset.sum_nonneg fun j _ => ite_seam_nonneg J M k j) (Finset.mem_univ i₀)
  exact lt_of_lt_of_le hterm hle

end RelExist.SeamPermanence
