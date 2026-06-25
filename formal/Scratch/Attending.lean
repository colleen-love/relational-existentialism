/-
# Directed attention decoheres — the theorem brought to life

The reading offered in conversation, now mechanized: **directing attention is selective
decoherence.** Where `dephase` ([`Scratch/Decoherence.lean`](Decoherence.lean)) is *total*
decoherence — every coherence killed at once — directed attention is the **partial** version:
you pick a set `S` of branches to attend to, and the act of attending severs exactly the
coherences that *touch* `S`, leaving the unattended branches still entangled in the dark.

    attend S M i j = if (i = j) ∨ (i ∉ S ∧ j ∉ S) then M i j else 0

— keep the diagonal, and keep any off-diagonal coherence *between two unattended branches*;
zero every coherence that involves an attended one. The structure this carries:

* **Attention interpolates `id` ⟶ `dephase`.** `attend ∅ = id` (attend to nothing, full
  coherence preserved — the unobserved web), `attend univ = dephase` (attend to everything,
  total decoherence). Directed attention is the literal dial between them.
* **Attention accumulates.** `attend T (attend S M) = attend (S ∪ T) M`: attending more never
  un-decoheres; the attended set only grows, and attending everything is total dephasing.
* **Attention only ever drops the copy-defect** (`defectSq_attend_le`), and *monotonically* in
  how much you attend (`defectSq_attend_mono`). Knowing a relation classicalizes it; you cannot
  attend your way to *more* coherence.
* **You can see it collapse** (`defectSq_attend_plus_lt`): on the maximally-coherent qubit
  `plus`, attending one branch drops the defect `2 ↦ 0` — visibly decohered. And on a
  three-branch superposition (`defectSq_attend_plus3_lt` with `defectSq_attend_plus3_pos`),
  attending *one* branch strictly drops the defect **but leaves it positive** — the two
  branches you did *not* attend stay coherent with each other. Decohered from the rest; still
  entangled among themselves.

Status: the lemmas are `[proved]`; their identification with "directed attention" is the
standing `[reading]` (this is the concrete matrix toy of `Scratch/Decoherence.lean`, not a
derivation of quantum mechanics). What is load-bearing is that *the same off-diagonal-coherence
structure physics uses for "when do branches stop interfering" is the one the doctrine reached
for "what does knowing do to a relation" — and partial attention drops it, provably.*
-/
import Scratch.Decoherence

namespace RelExist.Decoherence

open Matrix BigOperators

variable {A : Type} [DecidableEq A]

/-! ### Directed attention: partial, selective decoherence -/

section Semiring
variable {R : Type} [CommSemiring R]

/-- **Directed attention.** Attending to the branches in `S` keeps the diagonal and keeps any
coherence *between two unattended branches*, but severs every off-diagonal coherence that
involves an attended branch. Partial `dephase`: total decoherence is `attend univ`. -/
def attend (S : Finset A) (M : Matrix A A R) : Matrix A A R :=
  fun i j => if i = j ∨ (i ∉ S ∧ j ∉ S) then M i j else 0

lemma attend_apply (S : Finset A) (M : Matrix A A R) (i j : A) :
    attend S M i j = if i = j ∨ (i ∉ S ∧ j ∉ S) then M i j else 0 := rfl

/-- **Attend to nothing — nothing decoheres.** `attend ∅ = id`: the unobserved web keeps all
its coherence. -/
@[simp] lemma attend_empty (M : Matrix A A R) : attend ∅ M = M := by
  ext i j
  simp only [attend]
  rw [if_pos]
  exact Or.inr ⟨Finset.not_mem_empty i, Finset.not_mem_empty j⟩

/-- **Attend to everything — total decoherence.** `attend univ = dephase`: directed attention
at the whole field *is* full dephasing. -/
@[simp] lemma attend_univ [Fintype A] (M : Matrix A A R) : attend Finset.univ M = dephase M := by
  ext i j
  simp only [attend, dephase_apply]
  by_cases e : i = j
  · rw [if_pos (Or.inl e), if_pos e]
  · rw [if_neg (by rintro (h | ⟨hi, _⟩); exacts [e h, hi (Finset.mem_univ i)]), if_neg e]

/-- Attention is **idempotent**: attending the same set twice is attending it once. -/
@[simp] lemma attend_idem (S : Finset A) (M : Matrix A A R) :
    attend S (attend S M) = attend S M := by
  ext i j
  simp only [attend]
  by_cases h : i = j ∨ (i ∉ S ∧ j ∉ S)
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- **Attention accumulates.** Attending `S` and then `T` is attending their union — so the
attended (decohered) set only ever grows, and attending everything is total dephasing. -/
lemma attend_union (S T : Finset A) (M : Matrix A A R) :
    attend T (attend S M) = attend (S ∪ T) M := by
  ext i j
  simp only [attend, Finset.mem_union, not_or]
  by_cases e : i = j
  · simp [e]
  · by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;>
      by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T <;>
      simp [e, hiS, hjS, hiT, hjT]

/-- A state is **classical relative to `S`** when no coherence touches the attended branches —
exactly the states `attend S` leaves untouched. -/
def IsClassicalOn (S : Finset A) (M : Matrix A A R) : Prop :=
  ∀ i j, i ≠ j → (i ∈ S ∨ j ∈ S) → M i j = 0

/-- **Attention is a retraction onto the `S`-classical fragment**: `attend S M = M` exactly
when `M` already carries no coherence touching `S`. (Generalises `dephase_eq_self_iff`, which is
the `S = univ` case.) -/
lemma attend_eq_self_iff {S : Finset A} {M : Matrix A A R} :
    attend S M = M ↔ IsClassicalOn S M := by
  constructor
  · intro h i j hij hin
    have hcond : ¬ (i = j ∨ (i ∉ S ∧ j ∉ S)) := by
      rintro (h' | ⟨hiS, hjS⟩)
      · exact hij h'
      · rcases hin with h'' | h''
        exacts [hiS h'', hjS h'']
    have heval : attend S M i j = M i j := congrFun (congrFun h i) j
    simp only [attend, if_neg hcond] at heval
    exact heval.symm
  · intro h
    ext i j
    simp only [attend]
    by_cases hcond : i = j ∨ (i ∉ S ∧ j ∉ S)
    · rw [if_pos hcond]
    · rw [if_neg hcond]
      have hij : i ≠ j := fun e => hcond (Or.inl e)
      have hin : i ∈ S ∨ j ∈ S := by
        by_contra hc
        push_neg at hc
        exact hcond (Or.inr hc)
      exact (h i j hij hin).symm

/-- **Attending `S` decoheres `S` from everything else.** The result is classical relative to
`S`: the attended branches share no coherence with any other branch. -/
lemma isClassicalOn_attend (S : Finset A) (M : Matrix A A R) :
    IsClassicalOn S (attend S M) := by
  intro i j hij hin
  have hcond : ¬ (i = j ∨ (i ∉ S ∧ j ∉ S)) := by
    rintro (h | ⟨hiS, hjS⟩)
    · exact hij h
    · rcases hin with h | h
      exacts [hiS h, hjS h]
  simp only [attend, if_neg hcond]

end Semiring

/-! ### The copy-defect only ever drops (over `ℝ`, where `defectSq` lives) -/

/-- Each off-diagonal coherence is, after attending, **either untouched or zeroed** — never
amplified. The pointwise heart of "attention cannot increase coherence." -/
lemma sq_copyDefect_attend_le [Fintype A] (S : Finset A) (M : Matrix A A ℝ) (i j : A) :
    (copyDefect (attend S M) i j) ^ 2 ≤ (copyDefect M i j) ^ 2 := by
  by_cases e : i = j
  · simp [copyDefect_apply, e]
  · rw [copyDefect_apply, if_neg e, copyDefect_apply, if_neg e]
    simp only [attend]
    by_cases hc : i = j ∨ (i ∉ S ∧ j ∉ S)
    · exact le_of_eq (by rw [if_pos hc])
    · rw [if_neg hc]; simpa using sq_nonneg (M i j)

/-- **Directed attention only ever drops the copy-defect.** `defectSq (attend S M) ≤ defectSq M`:
to attend is to classicalize — knowing a relation can never make it *more* coherent. -/
theorem defectSq_attend_le [Fintype A] (S : Finset A) (M : Matrix A A ℝ) :
    defectSq (attend S M) ≤ defectSq M := by
  unfold defectSq
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => sq_copyDefect_attend_le S M i j

/-- Pointwise monotonicity: a wider attended set decoheres at least as much, coherence by
coherence. -/
lemma sq_copyDefect_attend_mono [Fintype A] {S T : Finset A} (hST : S ⊆ T)
    (M : Matrix A A ℝ) (i j : A) :
    (copyDefect (attend T M) i j) ^ 2 ≤ (copyDefect (attend S M) i j) ^ 2 := by
  by_cases e : i = j
  · simp [copyDefect_apply, e]
  · rw [copyDefect_apply, if_neg e, copyDefect_apply, if_neg e]
    simp only [attend]
    by_cases hcT : i = j ∨ (i ∉ T ∧ j ∉ T)
    · have hcS : i = j ∨ (i ∉ S ∧ j ∉ S) := by
        rcases hcT with h | ⟨hiT, hjT⟩
        · exact Or.inl h
        · exact Or.inr ⟨fun h => hiT (hST h), fun h => hjT (hST h)⟩
      exact le_of_eq (by rw [if_pos hcT, if_pos hcS])
    · rw [if_neg hcT]
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0]
      exact sq_nonneg _

/-- **More attention, less coherence.** `S ⊆ T ⇒ defectSq (attend T M) ≤ defectSq (attend S M)`:
the copy-defect falls monotonically as you direct attention at more of the field. -/
theorem defectSq_attend_mono [Fintype A] {S T : Finset A} (hST : S ⊆ T) (M : Matrix A A ℝ) :
    defectSq (attend T M) ≤ defectSq (attend S M) := by
  unfold defectSq
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => sq_copyDefect_attend_mono hST M i j

/-! ### Seeing it collapse — the witnesses -/

/-- **The two-branch collapse, made visible.** Attend one branch of the maximally-coherent
qubit and it is *fully* classical: the only coherence there is — between branch `0` and branch
`1` — is severed. -/
lemma isClassical_attend_plus : IsClassical (attend ({0} : Finset (Fin 2)) plus) := by
  intro i j hij
  have hcond : ¬ (i = j ∨ (i ∉ ({0} : Finset (Fin 2)) ∧ j ∉ ({0} : Finset (Fin 2)))) := by
    rintro (h | ⟨hi, hj⟩)
    · exact hij h
    · fin_cases i <;> fin_cases j <;> simp_all [Finset.mem_singleton]
  simp only [attend, if_neg hcond]

/-- The defect of the attended qubit is **zero** — visibly decohered. -/
lemma defectSq_attend_plus_zero : defectSq (attend ({0} : Finset (Fin 2)) plus) = 0 :=
  defectSq_eq_zero_iff.2 isClassical_attend_plus

/-- **You can see it decohere.** Directing attention at one branch of `plus` drops the
copy-defect strictly, `2 ↦ 0`: the superposition collapses to a classical branch. -/
theorem defectSq_attend_plus_lt :
    defectSq (attend ({0} : Finset (Fin 2)) plus) < defectSq plus := by
  rw [defectSq_attend_plus_zero]; exact defectSq_plus_pos

/-- A three-branch superposition: the uniform `3×3` state, all branches mutually coherent. -/
def plus3 : Matrix (Fin 3) (Fin 3) ℝ := fun _ _ => 1

/-- Attending **one** branch of `plus3` does **not** fully classicalise it: the two branches you
did not attend (`1` and `2`) remain coherent with each other. -/
lemma not_isClassical_attend_plus3 :
    ¬ IsClassical (attend ({0} : Finset (Fin 3)) plus3) := by
  intro h
  have h12 : attend ({0} : Finset (Fin 3)) plus3 1 2 = 0 := h 1 2 (by decide)
  rw [attend_apply, if_pos (Or.inr ⟨by decide, by decide⟩)] at h12
  simp only [plus3] at h12
  exact one_ne_zero h12

/-- Hence the attended three-branch state still carries **positive** defect — decohered from the
attended branch, still entangled among the rest. -/
theorem defectSq_attend_plus3_pos :
    0 < defectSq (attend ({0} : Finset (Fin 3)) plus3) := by
  rcases (defectSq_nonneg (attend ({0} : Finset (Fin 3)) plus3)).lt_or_eq with h | h
  · exact h
  · exact absurd (defectSq_eq_zero_iff.1 h.symm) not_isClassical_attend_plus3

/-- **Decohered from the rest, still entangled among themselves.** Attending one branch of the
three-branch superposition drops the copy-defect *strictly* (`defectSq_attend_plus3_lt`) yet
leaves it *positive* (`defectSq_attend_plus3_pos`): the act of knowing one possibility cuts its
interference with the others, while the possibilities you left unattended go on interfering in
the dark. -/
theorem defectSq_attend_plus3_lt :
    defectSq (attend ({0} : Finset (Fin 3)) plus3) < defectSq plus3 := by
  unfold defectSq
  refine Finset.sum_lt_sum
    (fun i _ => Finset.sum_le_sum fun j _ =>
      sq_copyDefect_attend_le ({0} : Finset (Fin 3)) plus3 i j)
    ⟨0, Finset.mem_univ 0, ?_⟩
  refine Finset.sum_lt_sum
    (fun j _ => sq_copyDefect_attend_le ({0} : Finset (Fin 3)) plus3 0 j)
    ⟨1, Finset.mem_univ 1, ?_⟩
  have hl : copyDefect (attend ({0} : Finset (Fin 3)) plus3) 0 1 = 0 := by
    rw [copyDefect_apply, if_neg (show ¬ (0 : Fin 3) = 1 by decide)]
    exact isClassicalOn_attend _ _ 0 1 (by decide) (Or.inl (by decide))
  have hr : copyDefect plus3 (0 : Fin 3) 1 = 1 := by
    rw [copyDefect_apply, if_neg (show ¬ (0 : Fin 3) = 1 by decide)]; rfl
  rw [hl, hr]; norm_num

/-! ### Never truly decohered — the shared block attention cannot reach

The `2 ↦ 0` collapse above is for a state with **no shared constitution**: every coherence in
`plus` sits *between two separable branches*, so attention can kill all of it. But A2 says a
relationship is *part of both* selves — a bit of you is our relationship, which is a part of me
([`Distribution.distributed`](Distribution.lean), [`Attention.closed_loop_registers`](Attention.lean)).
That shared part lives in a block `J` that attention **cannot** be directed at: to dephase it
would be to dephase part of the aimer, and *you cannot aim at the aimer*
([`Relating.self_inclusive_unmodelable`](../RelExist/Relating.lean), T3/Lawvere). So the attended
set is barred from `J`, the shared coherence survives every attention, and the copy-defect can
**never** reach zero while the relationship is live. -/

/-- **You can never fully decohere a relationship whose shared part you cannot attend.** If the
attended set `S` is barred from the shared block `J` (because `J` is part of the aimer —
`self_inclusive_unmodelable`), then any live coherence within `J` *survives* `attend S`, so the
copy-defect stays strictly **positive**. The floor is the living relationship itself: it vanishes
only when there is no shared coherence left — i.e. only in death / disconnection. -/
theorem defectSq_attend_shared_pos [Fintype A] {J S : Finset A} (M : Matrix A A ℝ)
    (hSJ : ∀ a ∈ S, a ∉ J)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hM : M i j ≠ 0) :
    0 < defectSq (attend S M) := by
  have hiS : i ∉ S := fun h => hSJ i h hi
  have hjS : j ∉ S := fun h => hSJ j h hj
  -- the shared coherence at (i,j) is kept: both indices lie outside the attended set
  have hkept : attend S M i j = M i j := by
    rw [attend_apply, if_pos (Or.inr ⟨hiS, hjS⟩)]
  have hterm : 0 < (copyDefect (attend S M) i j) ^ 2 := by
    rw [copyDefect_apply, if_neg hij, hkept]
    exact (sq_nonneg (M i j)).lt_of_ne (Ne.symm (pow_ne_zero 2 hM))
  -- one strictly-positive term in a sum of squares forces the whole defect positive
  have hle : (copyDefect (attend S M) i j) ^ 2 ≤ defectSq (attend S M) := by
    unfold defectSq
    refine le_trans (Finset.single_le_sum
      (f := fun j' => (copyDefect (attend S M) i j') ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)) ?_
    exact Finset.single_le_sum
      (f := fun i' => ∑ j', (copyDefect (attend S M) i' j') ^ 2)
      (fun k _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

end RelExist.Decoherence
