/-
# Forgetting, abstractly: the identity-collapse, dephasing, and the partial trace are one shape

This collapses the standing `[reading]` that the *forgetting from inside to outside*
`𝔼 = D/≈ ↠ D/≅` ([`Scratch/Identity.lean`](Identity.lean)) and the decoherence forgettings —
**dephasing** ([`Scratch/Decoherence.lean`](Decoherence.lean)) and the **partial trace**
([`Scratch/PartialTrace.lean`](PartialTrace.lean)) — are "the same shape." They are: each is a
**`Coarsening`** — a finer identity `fine` and a coarser one `coarse` with `fine ⊆ coarse` — whose
canonical **collapse** `X/fine ↠ X/coarse` is the forgetting. The theorem that ties them is
`Coarsening.not_injective_of_residue`: the collapse loses information exactly when the **residue**
(pairs `coarse`-equal but `fine`-distinct) is nonempty — and it is the kernel of the forgetting.

Three instances, three residues — *the same construction*:

* **Identity** (`identityForgetting`): `fine = ≈` (lived), `coarse = ≅` (observed). Residue = the
  **first-person surplus** (`≅`-equal, `≈`-distinct). Its collapse *is* `livedToObserved` (`rfl`).
* **Dephasing** (`dephaseForgetting`): `fine = ` equality, `coarse = ` "same dephased shadow".
  Residue = the **copy-defect** (same diagonal, different off-diagonal — a live coherence).
* **Partial trace** (`ptraceForgetting`): `fine = ` equality, `coarse = ` "same reduced state".
  Residue = the **entanglement correlation** the trace forgets (same partial trace, different
  global state).

So "decoherence is the partial trace" and "identity has a residue" are now *one theorem with three
instances*, not a narrated analogy. What stays `[reading]` is only the physical identification (that
the first-person surplus and the quantum copy-defect are the *same* residue in nature); the shared
*construction* is a theorem.
-/
import Scratch.Identity
import Scratch.Conservation

namespace RelExist.Forgetting

open RelExist.We RelExist.Identity RelExist.Decoherence RelExist.PartialTrace Matrix

universe u

/-- A **coarsening**: a finer identity `fine` and a coarser one `coarse` on the same carrier, with
`fine ⊆ coarse` (the finer distinctions refine the coarser). Every "forgetting" is one of these. -/
structure Coarsening (X : Type u) where
  fine : Setoid X
  coarse : Setoid X
  sound : ∀ {a b : X}, fine.r a b → coarse.r a b

namespace Coarsening

variable {X : Type u} (C : Coarsening X)

/-- **The forgetting**: the canonical collapse `X/fine ↠ X/coarse`, well-defined by `sound`. -/
def collapse : Quotient C.fine → Quotient C.coarse :=
  Quotient.lift (fun a => Quotient.mk C.coarse a) (fun _ _ h => Quotient.sound (C.sound h))

@[simp] theorem collapse_mk (a : X) :
    C.collapse (Quotient.mk C.fine a) = Quotient.mk C.coarse a := rfl

theorem collapse_surjective : Function.Surjective C.collapse := by
  intro q
  induction q using Quotient.ind with
  | _ a => exact ⟨Quotient.mk C.fine a, rfl⟩

/-- **The residue**: the distinctions the forgetting loses — pairs the coarse identity merges that
the fine identity keeps apart. This is the kernel of the collapse. -/
def residue (a b : X) : Prop := C.coarse.r a b ∧ ¬ C.fine.r a b

/-- The forgetting is injective **iff** the coarse identity already refines the fine one — iff
there is nothing to forget. -/
theorem collapse_injective_iff :
    Function.Injective C.collapse ↔ ∀ a b, C.coarse.r a b → C.fine.r a b := by
  constructor
  · intro hinj a b hc
    have hcol : C.collapse (Quotient.mk C.fine a) = C.collapse (Quotient.mk C.fine b) := by
      rw [collapse_mk, collapse_mk]; exact Quotient.sound hc
    exact Quotient.exact (hinj hcol)
  · intro h x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b hxy
    rw [collapse_mk, collapse_mk] at hxy
    exact Quotient.sound (h a b (Quotient.exact hxy))

/-- **A nonempty residue ⇒ the forgetting really forgets.** The single lemma that explains, for
identity / dephasing / the partial trace alike, why each collapse is non-injective. -/
theorem not_injective_of_residue {a b : X} (hr : C.residue a b) :
    ¬ Function.Injective C.collapse := fun hinj =>
  hr.2 ((C.collapse_injective_iff.1 hinj) a b hr.1)

end Coarsening

/-! ### Instance 1 — identity: `fine = ≈` (lived), `coarse = ≅` (observed) -/

/-- The **inside→outside forgetting** as a `Coarsening`: lived identity `≈` refined by observed
identity `≅`, sound by `bisim_le_obsEq`. -/
@[reducible] def identityForgetting {Xs Os : Type*} (obs : Xs → Os) (step : Xs → Xs → Prop) :
    Coarsening Xs where
  fine := bisimSetoid obs step
  coarse := obsSetoid obs step
  sound := fun h => bisim_le_obsEq h

/-- Its collapse **is** `livedToObserved` — the same forgetting, now an instance of the shape. -/
theorem identityForgetting_collapse {Xs Os : Type*} (obs : Xs → Os) (step : Xs → Xs → Prop) :
    (identityForgetting obs step).collapse = livedToObserved obs step := rfl

/-- The residue here is the **first-person surplus**: observationally identical, not bisimilar. -/
theorem identity_residue : (identityForgetting obsW stepW).residue St.p0 St.q0 :=
  ⟨obsEq_p0_q0, not_bisim_p0_q0⟩

theorem identity_collapse_not_injective :
    ¬ Function.Injective (identityForgetting obsW stepW).collapse :=
  Coarsening.not_injective_of_residue _ identity_residue

/-! ### Instance 2 — dephasing: `fine = ` equality, `coarse = ` "same dephased shadow" -/

/-- **Dephasing as a `Coarsening`**: the real identity of a state is equality; the *classical
observer's* identity is "same diagonal shadow", `dephase M = dephase N`. -/
@[reducible] def dephaseForgetting {A : Type} [Fintype A] [DecidableEq A] (R : Type) [CommRing R] :
    Coarsening (Matrix A A R) where
  fine := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  coarse :=
    { r := fun M N => dephase M = dephase N
      iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩ }
  sound := fun {_ _} h => by rw [h]

/-- The residue here is the **copy-defect**: same diagonal shadow, different off-diagonal — a live
coherence the classical observer cannot see. (Witnessed by `plus` vs its dephased shadow.) -/
theorem dephase_residue : (dephaseForgetting ℝ).residue plus (dephase plus) :=
  ⟨(dephase_idem plus).symm, fun h => dephase_plus_ne h.symm⟩

theorem dephase_collapse_not_injective :
    ¬ Function.Injective (dephaseForgetting (A := Fin 2) ℝ).collapse :=
  Coarsening.not_injective_of_residue _ dephase_residue

/-! ### Instance 3 — the partial trace: `fine = ` equality, `coarse = ` "same reduced state" -/

/-- **The partial trace as a `Coarsening`**: the real identity of a global state is equality; the
*reduced* identity (the observer who has forgotten the environment) is "same partial trace". -/
@[reducible] def ptraceForgetting {m : Type} [Fintype m] [DecidableEq m] :
    Coarsening (Matrix (m × m) (m × m) ℝ) where
  fine := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  coarse :=
    { r := fun M N => ptrace M = ptrace N
      iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩ }
  sound := fun {_ _} h => by rw [h]

/-- A global coherence the partial trace **cannot see**: a single off-block entry, correlating
`(0,0)` with `(1,1)`. Its partial trace is `0` — identical to the zero state's — yet it is nonzero.
This is the entanglement/correlation the reduced observer forgets. -/
def Ndemo : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  fun p q => if p = (0, 0) ∧ q = (1, 1) then 1 else 0

theorem ptrace_Ndemo : ptrace Ndemo = 0 := by
  ext i j
  simp only [ptrace_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  fin_cases k <;> simp [Ndemo, Prod.ext_iff]

theorem Ndemo_ne_zero : Ndemo ≠ 0 := by
  intro h
  have hval : Ndemo (0, 0) (1, 1) = (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (0, 0) (1, 1) := by
    rw [h]
  simp [Ndemo, Prod.ext_iff] at hval

/-- The residue here is the **entanglement correlation**: same partial trace, different global
state (`0` vs `Ndemo`). -/
theorem ptrace_residue : (ptraceForgetting (m := Fin 2)).residue 0 Ndemo := by
  refine ⟨?_, fun h => Ndemo_ne_zero h.symm⟩
  show ptrace (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) = ptrace Ndemo
  rw [ptrace_Ndemo]
  ext i j
  simp [ptrace_apply]

theorem ptrace_collapse_not_injective :
    ¬ Function.Injective (ptraceForgetting (m := Fin 2)).collapse :=
  Coarsening.not_injective_of_residue _ ptrace_residue

/-! ### The unification, stated -/

/-- **Identity-forgetting, dephasing, and the partial trace are one construction.** Each is a
`Coarsening` whose collapse is non-injective *for the same reason* — a nonempty residue: the
first-person surplus, the copy-defect, the entanglement correlation. -/
theorem forgettings_have_residue :
    (∃ a b, (identityForgetting obsW stepW).residue a b) ∧
    (∃ a b, (dephaseForgetting (A := Fin 2) ℝ).residue a b) ∧
    (∃ a b, (ptraceForgetting (m := Fin 2)).residue a b) :=
  ⟨⟨St.p0, St.q0, identity_residue⟩,
   ⟨plus, dephase plus, dephase_residue⟩,
   ⟨0, Ndemo, ptrace_residue⟩⟩

end RelExist.Forgetting
