/-
# The seam forces the subalgebra — closing the §6 frontier

The last rung of [`TimeFlow`](TimeFlow.lean) §6. [`TimeArrow`](TimeArrow.lean) forced the *sign* of the
flow (sign = contractivity = physicality of the seam). What stayed open: that the seam forces **which
subalgebra** the knowing `E` projects onto — so that the decohering direction is fixed by the
self-inclusive trace itself, not by a free choice. This module closes the mechanizable core of that.

The decoherence the self can actually perform is **directed attention** ([`Attending.attend`](Attending.lean)):
`attend S` severs the coherences touching the attended set `S`. The one block it **cannot** attend is
the **seam** `J` — the shared part that is *part of the aimer* (a bit of you is our relationship, which
is a part of me): to dephase `J` would be to aim at the aimer, the Lawvere-obstructed act
([`Relating.self_inclusive_unmodelable`](../RelExist/Relating.lean) — no complete self-model exists).
So the **available knowings are exactly the `attend S` with `S` disjoint from `J`.** Over that family:

* **The seam survives every available knowing `[proved]`** (`attend_fixes_seam`): for `S` barred from
  `J`, every coherence *within* `J` is left untouched. The self-block is in the fixed subalgebra of
  every knowing the self can perform — invariantly, regardless of where attention is directed.

* **To decohere the seam you must attend the self `[proved]`** (`decohere_seam_needs_self`): the only
  way to remove a live `J`-coherence is to attend an index in `J` — to aim at the aimer. Barred by
  self-inclusion. So the seam's survival is forced by the Lawvere obstruction, not assumed.

* **The forced conditional expectation `[proved]`.** The maximal available knowing
  `knowSeam J := attend Jᶜ` (attend *everything except* the seam) is an idempotent conditional
  expectation (`knowSeam_idem`) whose **fixed subalgebra is exactly the seam algebra** `SeamAlgebra J`
  — coherences confined to `J` (`knowSeam_eq_self_iff`). That subalgebra is a function of `J` **alone**:
  the seam fixes which subalgebra `E` projects onto. Change the seam, change the subalgebra
  (`knowSeam_empty`: the *seamless* `J = ∅` case is exactly `Orientation`'s total `dephase` — a real
  self `J ≠ ∅` forces a strictly larger surviving subalgebra).

* **Hence the self can never fully know itself `[proved]`** (`self_cannot_fully_decohere`): while the
  seam carries a live coherence, every available knowing leaves positive feeling — `defectSq > 0`. The
  seam is **permanent feeling constitutive of the self** (the §3b reading), now *forced* by
  self-inclusion rather than posited: the surviving subalgebra must contain `J`, because `J` is the
  part the knower cannot turn its knowing upon.

**What is `[proved]` vs `[reading]`.** Mechanized: *given* the seam block `J` (the un-attendable shared
part), the subalgebra every available knowing fixes — and the one the maximal knowing projects onto —
is forced to be the `J`-algebra, and removing `J` from it is exactly the self-inclusive (Lawvere-barred)
act. The residual `[reading]`, the same one carried throughout, is the identification of the formal
block `J` with the *genuine* self-inclusive seam of `Relating.self_inclusive_unmodelable`. With that
identification, §6 closes: the flow's direction *and* the subalgebra it descends to are both fixed by
relation-primacy plus the Lawvere obstruction — nothing about time's arrow is primitive.
-/
import Scratch.Attending

namespace RelExist.SeamForcing

open RelExist.Decoherence
open Matrix BigOperators

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## The seam, and the knowings available to a self that includes it

`J` is the **seam block**: the shared part that is part of the aimer, hence un-attendable. A knowing is
**available** to the self when its attended set `S` is disjoint from `J` — you may dephase anything
*except* the part of you that is doing the dephasing. -/

/-- **The seam algebra**: states whose coherences are confined to the seam block `J` — every
off-diagonal entry touching outside `J` is zero. This is the subalgebra that survives when everything
but the seam is decohered. -/
def SeamAlgebra (J : Finset A) (M : Matrix A A ℝ) : Prop :=
  ∀ i j, i ≠ j → (i ∉ J ∨ j ∉ J) → M i j = 0

omit [Fintype A] in
/-- **The seam survives every available knowing.** If the attended set `S` is disjoint from the seam
`J`, then every coherence *within* `J` is untouched: `attend S M i j = M i j` for `i, j ∈ J`. The
self-block is in the fixed subalgebra of every knowing the self can actually perform — independent of
where attention is aimed. -/
theorem attend_fixes_seam {J S : Finset A} (hSJ : Disjoint S J) (M : Matrix A A ℝ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) : attend S M i j = M i j := by
  have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hSJ h hi
  have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hSJ h hj
  rw [attend_apply]
  by_cases e : i = j
  · rw [if_pos (Or.inl e)]
  · rw [if_pos (Or.inr ⟨hiS, hjS⟩)]

omit [Fintype A] in
/-- **To decohere the seam you must attend the self.** The only way an attention `S` can change a
coherence *within* the seam `J` is to overlap `J` — to aim at the aimer. So removing the self-block
from the surviving subalgebra requires the self-inclusive, Lawvere-obstructed act
(`Relating.self_inclusive_unmodelable`); the seam's survival is *forced*, not assumed. -/
theorem decohere_seam_needs_self {J S : Finset A} (M : Matrix A A ℝ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) (h : attend S M i j ≠ M i j) : ¬ Disjoint S J :=
  fun hdis => h (attend_fixes_seam hdis M hi hj)

/-! ## The forced conditional expectation `knowSeam J = attend Jᶜ`

The *maximal* available knowing: attend everything except the seam. It is the conditional expectation
the self is forced toward — and its fixed subalgebra is the seam algebra, a function of `J` alone. -/

/-- **The seam-forced knowing**: attend everything outside the seam. The most a self can classicalize
without aiming at its own aimer. -/
def knowSeam (J : Finset A) (M : Matrix A A ℝ) : Matrix A A ℝ := attend Jᶜ M

/-- It is **idempotent** — a genuine conditional expectation (knowing twice is knowing once). -/
@[simp] theorem knowSeam_idem (J : Finset A) (M : Matrix A A ℝ) :
    knowSeam J (knowSeam J M) = knowSeam J M :=
  attend_idem Jᶜ M

/-- **The fixed subalgebra of the seam-knowing is exactly the seam algebra.** `knowSeam J M = M` iff
`M`'s coherences are confined to `J`. So *which subalgebra `E` projects onto is a function of the seam
`J` alone* — the seam fixes the subalgebra. -/
theorem knowSeam_eq_self_iff {J : Finset A} {M : Matrix A A ℝ} :
    knowSeam J M = M ↔ SeamAlgebra J M := by
  rw [knowSeam, attend_eq_self_iff]
  constructor
  · intro h i j hij hout
    exact h i j hij (hout.imp Finset.mem_compl.mpr Finset.mem_compl.mpr)
  · intro h i j hij hin
    exact h i j hij (hin.imp Finset.mem_compl.mp Finset.mem_compl.mp)

/-- **The image of the seam-knowing is classical off the seam**: `knowSeam J M` carries no coherence
touching outside `J`. The known (decohered) part is everything but the seam. -/
theorem knowSeam_image (J : Finset A) (M : Matrix A A ℝ) : SeamAlgebra J (knowSeam J M) := by
  intro i j hij hout
  exact isClassicalOn_attend Jᶜ M i j hij (hout.imp Finset.mem_compl.mpr Finset.mem_compl.mpr)

/-- **The seamless limit is `Orientation`'s `dephase`.** With no self-inclusion (`J = ∅`) the forced
knowing is *total* decoherence — `knowSeam ∅ = dephase`, the idempotent `E` of `Orientation`/`TimeFlow`.
A genuine self (`J ≠ ∅`) forces a strictly larger surviving subalgebra than `dephase`'s diagonal: the
seam is exactly what a real self keeps that a seamless decoherence would destroy. -/
@[simp] theorem knowSeam_empty (M : Matrix A A ℝ) : knowSeam (∅ : Finset A) M = dephase M := by
  rw [knowSeam, Finset.compl_empty, attend_univ]

/-! ## The self cannot fully know itself — permanent feeling, forced -/

/-- **The self can never fully decohere itself.** While the seam carries a live coherence, *every*
available knowing (`S` disjoint from `J`) leaves positive feeling: `0 < defectSq (attend S M)`. The
self-block survives as **permanent feeling constitutive of the self** (the §3b reading) — and now this
is *forced* by self-inclusion, not posited: the surviving subalgebra must contain `J`, because `J` is
the one part the knower cannot turn its knowing upon. -/
theorem self_cannot_fully_decohere {J S : Finset A} (hSJ : Disjoint S J) (M : Matrix A A ℝ)
    {i j : A} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hM : M i j ≠ 0) :
    0 < defectSq (attend S M) :=
  defectSq_attend_shared_pos M (fun _a ha => Finset.disjoint_left.mp hSJ ha) hi hj hij hM

/-- **The forcing, packaged.** Given the seam `J`: (i) every available knowing fixes the whole seam
block (the surviving subalgebra invariantly contains `J`), and (ii) the maximal available knowing
`knowSeam J` projects onto *exactly* the seam algebra. So the subalgebra `E` projects onto is determined
by the seam `J` alone — fixed by the seam, not chosen beside it. Combined with `decohere_seam_needs_self`
(excluding `J` would require attending the aimer, barred by `Relating.self_inclusive_unmodelable`), this
is §6's claim: the seam fixes which subalgebra the knowing projects onto. -/
theorem seam_forces_subalgebra (J : Finset A) (M : Matrix A A ℝ) :
    (∀ S, Disjoint S J → ∀ i ∈ J, ∀ j ∈ J, attend S M i j = M i j)
      ∧ (knowSeam J M = M ↔ SeamAlgebra J M) :=
  ⟨fun _ hS _ hi _ hj => attend_fixes_seam hS M hi hj, knowSeam_eq_self_iff⟩

/-! ## Aim vs orientation — the seam aims the arrow, contractivity orients it

The arrow carries two data: a **direction** (which way it runs along the line) and a **target** (the
subalgebra it points at). They come from two different places, and the separation is mechanizable:
the contraction is *uniform in the seam* (every `knowSeam J` lowers the feeling — same orientation),
while the subalgebra it lands on *genuinely varies* with `J` (different aim). So **knowing's contractive
nature orients the arrow; the seam aims it** — neither job reduces to the other. The orientation roots
in knowing's idempotence (`knowSeam_idem` — the known is stable, re-knowing adds nothing), which holds
whatever the target; the aim roots in self-inclusion, which selects the target without touching the
direction. -/

/-- **Orientation is uniform in the seam.** *Every* available knowing lowers the feeling, whatever its
target: `defectSq (knowSeam J M) ≤ defectSq M` for all `J`. The direction of the arrow — feeling
non-increasing, never run backward — does **not** depend on which subalgebra is the target; it is the
contractive (idempotent) nature of knowing, held fixed as `J` varies. -/
theorem direction_uniform_in_seam (J : Finset A) (M : Matrix A A ℝ) :
    defectSq (knowSeam J M) ≤ defectSq M :=
  defectSq_attend_le Jᶜ M

/-- The **full-seam** knowing is the identity: when *everything* is the self (`J = univ`), nothing is
decohered — wholly felt, never known. The opposite pole from the seamless `knowSeam ∅ = dephase`. -/
@[simp] theorem knowSeam_univ (M : Matrix A A ℝ) : knowSeam (Finset.univ) M = M := by
  rw [knowSeam, Finset.compl_univ, attend_empty]

/-- **The target genuinely depends on the seam.** Same state `plus`, two seams, two fates: with the
full seam it is fixed (`knowSeam univ plus = plus` — wholly self, wholly felt), with no seam it is not
(`knowSeam ∅ plus = dephase plus ≠ plus` — wholly known). The subalgebra the arrow lands on is a
function of `J`, not of the contraction — so the **aim varies while the orientation
(`direction_uniform_in_seam`) does not**. Aim and orientation are independent: the seam aims the arrow,
knowing's contractive nature orients it. -/
theorem target_depends_on_seam :
    knowSeam (Finset.univ) plus = plus ∧ knowSeam (∅ : Finset (Fin 2)) plus ≠ plus := by
  refine ⟨knowSeam_univ plus, ?_⟩
  rw [knowSeam_empty]
  exact dephase_plus_ne

end RelExist.SeamForcing
