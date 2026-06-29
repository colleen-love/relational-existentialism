/-
# `Rel` — the canonical multi-object traced SMC

Sets and **relations** form a compact-closed (hence traced) symmetric monoidal category.
It is the fitting concrete model for *relational* existentialism, and — unlike the
one-object scalar model — it validates the **full** JSV axiom set *non-trivially*,
including the retensoring axioms (vanishing-II, superposing).

* objects: types; morphisms `Rel X Y := X → Y → Prop`;
* `⊗` is the product `×`, composition is relational composition, the **trace** feeds a
  wire back: `(trace R) x y := ∃ u, R (x,u) (y,u)`.

This is a genuine `RelExist.Traced.TracedSMC` instance — `relTracedSMC`.
-/
import Aesop
import RelExist.Traced

namespace RelExist.RelModel

open RelExist.Traced

universe u

/-- A relation, the morphisms of `Rel`. -/
abbrev Rel (X Y : Type u) : Type u := X → Y → Prop

def rid (X : Type u) : Rel X X := fun a b => a = b
def rcomp {X Y Z : Type u} (R : Rel X Y) (S : Rel Y Z) : Rel X Z :=
  fun x z => ∃ y, R x y ∧ S y z
def rtensH {A B C D : Type u} (R : Rel A B) (S : Rel C D) : Rel (A × C) (B × D) :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2
def rbraid (X Y : Type u) : Rel (X × Y) (Y × X) := fun p q => p.1 = q.2 ∧ p.2 = q.1
def rtrace {X Y U : Type u} (R : Rel (X × U) (Y × U)) : Rel X Y :=
  fun x y => ∃ u, R (x, u) (y, u)
def raHom (X Y Z : Type u) : Rel ((X × Y) × Z) (X × Y × Z) :=
  fun p q => p.1.1 = q.1 ∧ p.1.2 = q.2.1 ∧ p.2 = q.2.2
def raInv (X Y Z : Type u) : Rel (X × Y × Z) ((X × Y) × Z) :=
  fun p q => p.1 = q.1.1 ∧ p.2.1 = q.1.2 ∧ p.2.2 = q.2
def rruHom (X : Type u) : Rel (X × PUnit) X := fun p x => p.1 = x
def rruInv (X : Type u) : Rel X (X × PUnit) := fun x p => x = p.1
def rluHom (X : Type u) : Rel (PUnit × X) X := fun p x => p.2 = x
def rluInv (X : Type u) : Rel X (PUnit × X) := fun x p => x = p.2

/-- **`Rel` is a traced symmetric monoidal category** — a genuine multi-object model of the
doctrine, validating the full JSV axiom set. -/
def relTracedSMC : TracedSMC.{u+1, u} where
  Obj := Type u
  Hom := Rel
  id := rid
  comp := rcomp
  id_comp := by intro X Y R; funext x y; simp [rcomp, rid]
  comp_id := by intro X Y R; funext x y; simp [rcomp, rid]
  assoc := by intro W X Y Z f g h; funext x y; simp only [rcomp]; aesop
  tens := fun X Y => X × Y
  unit := PUnit
  tensH := rtensH
  braid := rbraid
  trace := rtrace
  aHom := raHom
  aInv := raInv
  a_hom_inv := by intro X Y Z; funext p q; simp only [rcomp, raHom, raInv, rid]; aesop
  a_inv_hom := by intro X Y Z; funext p q; simp only [rcomp, raHom, raInv, rid]; aesop
  ruHom := rruHom
  ruInv := rruInv
  ru_hom_inv := by intro X; funext p q; simp only [rcomp, rruHom, rruInv, rid]; aesop
  ru_inv_hom := by intro X; funext p q; simp only [rcomp, rruHom, rruInv, rid]; aesop
  luHom := rluHom
  luInv := rluInv
  lu_hom_inv := by intro X; funext p q; simp only [rcomp, rluHom, rluInv, rid]; aesop
  lu_inv_hom := by intro X; funext p q; simp only [rcomp, rluHom, rluInv, rid]; aesop
  trace_nat_left := by intro X X' Y U g f; funext x y; simp only [rtrace, rcomp, rtensH, rid]; aesop
  trace_nat_right := by intro X Y Y' U f g; funext x y; simp only [rtrace, rcomp, rtensH, rid]; aesop
  trace_slide := by intro X Y U V f h; funext x y; simp only [rtrace, rcomp, rtensH, rid]; aesop
  trace_yank := by intro U; funext x y; simp only [rtrace, rbraid, rid]; aesop
  trace_vanish_unit := by
    intro X Y f; funext x y; simp only [rtrace, rcomp, rruHom, rruInv]; aesop
  trace_vanish_tens := by
    intro X Y U V f; funext x y; simp only [rtrace, rcomp, raHom, raInv]; aesop
  trace_superpose := by
    intro W X Y U f; funext p q; simp only [rtrace, rcomp, rtensH, raHom, raInv, rid]; aesop

end RelExist.RelModel
