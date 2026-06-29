/-
# A non-cartesian reflexive object — `ℕ ≅ ℕ ⊗ ℕ` in compact-closed `Rel`

The seam bridge's deepest open part: **a linear / compact reflexive object** `D ≅ D* ⊗ D`, the
non-cartesian home of `Y`-as-the-trace (as opposed to the *cartesian* `Pω` of
[`GraphModel`](GraphModel.lean) / [`SelfApplication`](SelfApplication.lean), where `Y` is
self-application and copying is free).

[`RelCompact`](RelCompact.lean) proved **`Rel` is compact closed** and *non-cartesian* (its tensor `⊗ =
×` is the monoidal product, not the categorical product — `Rel` has no copying, `rel_no_cloning` below).
In a compact closed category the internal hom is `[A, B] = A* ⊗ B`; `Rel` is **self-dual** (`Aᵈ = A`),
so `[D, D] = D ⊗ D = D × D`. A **reflexive object** is therefore exactly a `D` with `D ≅ D × D`.

* **No finite object works** (`finite_not_reflexive`): `D ≅ D × D` forces `|D| = |D|²`, impossible for
  `1 < |D| < ∞`. This is the compact-side **Cantor obstruction**, mirroring
  [`no_reflexive_object_for_Bool`](../RelExist/ReflexiveSeam.lean) on the cartesian side.
* **`ℕ` works** (`natReflexive`): the pairing bijection `ℕ ≅ ℕ × ℕ` is a genuine isomorphism in `Rel`,
  so `ℕ ≅ ℕ ⊗ ℕ = ℕ* ⊗ ℕ = [ℕ, ℕ]`. A **non-cartesian reflexive object**, exactly where the finite
  obstruction is escaped — the linear/compact counterpart of `Pω`.

So the reflexive object exists on the compact (non-cartesian) side too; by `ReflexiveModel`'s duality
this is the **construction** side (it *builds* `Y`, never obstructs), orthogonal to the seam.
-/
import Aesop
import Scratch.RelCompact
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Basic

namespace RelExist.ReflexiveCompact

open RelExist.RelModel RelExist.Traced

universe u
variable {A B : Type u}

/-- The graph of a bijection, as a relation. -/
def graphRel (e : A ≃ B) : Rel A B := fun a b => e a = b

/-- An **isomorphism in `Rel`** between `A` and `B`: forward and backward relations composing to the
identities. (Isos in `Rel` are exactly graphs of bijections.) -/
structure RelIso (A B : Type u) where
  fwd : Rel A B
  bwd : Rel B A
  fwd_bwd : rcomp fwd bwd = rid A
  bwd_fwd : rcomp bwd fwd = rid B

/-- **Every bijection is a `Rel`-isomorphism.** -/
def relIsoOfEquiv (e : A ≃ B) : RelIso A B where
  fwd := graphRel e
  bwd := graphRel e.symm
  fwd_bwd := by funext a a'; simp [rcomp, graphRel, rid, eq_comm]
  bwd_fwd := by funext b b'; simp [rcomp, graphRel, rid, eq_comm]

/-- **No finite object with more than one point is reflexive.** `D ≅ D × D` forces `|D| = |D|²`,
hence `|D| ≤ 1` — the compact-side Cantor obstruction. -/
theorem finite_not_reflexive {D : Type*} [Fintype D] (e : D ≃ D × D) : Fintype.card D ≤ 1 := by
  have h : Fintype.card D = Fintype.card D * Fintype.card D := by
    rw [← Fintype.card_prod]; exact Fintype.card_congr e
  rcases Nat.lt_or_ge (Fintype.card D) 2 with hlt | hge
  · omega
  · have hmul : Fintype.card D * 2 ≤ Fintype.card D * Fintype.card D :=
      Nat.mul_le_mul (le_refl _) hge
    omega

/-- **`ℕ` is a reflexive object in compact-closed `Rel`**: `ℕ ≅ ℕ × ℕ = ℕ ⊗ ℕ = ℕ* ⊗ ℕ = [ℕ, ℕ]`, via
the pairing bijection. The non-cartesian counterpart of `Pω` — a reflexive object where copying is
*unavailable* (`rel_no_cloning`), so its `Y` is the trace, not self-application. -/
noncomputable def natReflexive : RelIso ℕ (ℕ × ℕ) := relIsoOfEquiv Nat.pairEquiv.symm

/-- **The home of the reflexive object is genuinely non-cartesian**: `Rel` admits no uniform
copying/deletion (its unit is not subterminal). So `ℕ ≅ ℕ ⊗ ℕ` is a reflexive object *without* the
cartesian copy — the linear setting the bridge wanted. -/
theorem rel_no_cloning : ¬ Compact.UnitSubterminal RelCompact.relCompactClosed.{0} := by
  have hfg : (rid Bool : Rel Bool Bool) ≠ (fun _ _ => True) := by
    intro h
    have h2 := congrFun (congrFun h false) true
    simp [rid] at h2
  exact Compact.no_cloning RelCompact.relCompactClosed.{0} hfg

end RelExist.ReflexiveCompact
