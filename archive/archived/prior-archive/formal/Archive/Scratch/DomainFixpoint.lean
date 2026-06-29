/-
# The Conway fixpoint trace, packaged — the category of domains is traced via feedback

[`ConwayTrace`](ConwayTrace.lean) built the Conway fixed-point operator and its load-bearing
identities (`pfp`, `rolling`, `diagonal`) and flagged the remaining work as the **categorical
packaging**: assembling them into a full `TracedSMC` *instance* on a genuine multi-object category of
domains. This module does that, on the simplest domains — **complete lattices** — with **monotone maps**
as morphisms, the **product** `×` as the monoidal tensor, and the **fixpoint trace**

`Tr(f)(a) := π₁ (f (a, lfp (u ↦ π₂ (f (a, u)))))`.

So this is the Hasegawa "only-if" direction in full: *a cartesian category with a Conway operator carries
a trace.* Where [`DomainTraced`](DomainTraced.lean) gave only the one-object **scalar** trace, this is the
genuine **fixpoint** trace on the multi-object category, with the full Joyal–Street–Verity axiom set
discharged from the `ConwayTrace` identities through the concrete product bookkeeping.

By `ReflexiveModel`'s duality this is the **construction** side — orthogonal to the seam.
-/
import Scratch.ConwayTrace
import RelExist.Traced
import Mathlib.Order.Hom.Basic

namespace RelExist.DomainFixpoint

open RelExist.Traced RelExist.ConwayTrace OrderHom

universe u

/-- **A bundled complete lattice** — the objects of the domain category. -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

attribute [instance] CLat.str

instance : CoeSort CLat (Type u) := ⟨CLat.carrier⟩

section combinators
variable {α β γ δ : Type u} [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]
  [CompleteLattice δ]

/-- The monotone product map `(f × g)(a,c) = (f a, g c)`. -/
def omProdMap (f : α →o β) (g : γ →o δ) : (α × γ) →o (β × δ) :=
  (f.comp OrderHom.fst).prod (g.comp OrderHom.snd)

@[simp] theorem omProdMap_apply (f : α →o β) (g : γ →o δ) (p : α × γ) :
    omProdMap f g p = (f p.1, g p.2) := rfl

/-- The braiding (swap). -/
def omSwap : (α × β) →o (β × α) := OrderHom.snd.prod OrderHom.fst

@[simp] theorem omSwap_apply (p : α × β) : omSwap p = (p.2, p.1) := rfl

/-- The associator `((a,b),c) ↦ (a,(b,c))`. -/
def omAssoc : ((α × β) × γ) →o (α × (β × γ)) :=
  (OrderHom.fst.comp OrderHom.fst).prod ((OrderHom.snd.comp OrderHom.fst).prod OrderHom.snd)

@[simp] theorem omAssoc_apply (p : (α × β) × γ) : omAssoc p = (p.1.1, (p.1.2, p.2)) := rfl

/-- The inverse associator `(a,(b,c)) ↦ ((a,b),c)`. -/
def omAssocInv : (α × (β × γ)) →o ((α × β) × γ) :=
  (OrderHom.fst.prod (OrderHom.fst.comp OrderHom.snd)).prod (OrderHom.snd.comp OrderHom.snd)

@[simp] theorem omAssocInv_apply (p : α × (β × γ)) : omAssocInv p = ((p.1, p.2.1), p.2.2) := rfl

/-- Right unitor inverse `a ↦ (a, ())`. -/
def omRuInv : α →o (α × PUnit) := OrderHom.id.prod (OrderHom.const _ PUnit.unit)

/-- Left unitor inverse `a ↦ ((), a)`. -/
def omLuInv : α →o (PUnit × α) := (OrderHom.const _ PUnit.unit).prod OrderHom.id

/-! ### The fixpoint trace -/

/-- The **feedback operator** of `f`: the curried map `a ↦ (u ↦ π₂ (f (a,u)))`, whose least fixed
point is the wire fed back through the loop. -/
def fb (f : (α × γ) →o (β × γ)) : α →o γ →o γ := OrderHom.curry (OrderHom.snd.comp f)

@[simp] theorem fb_apply (f : (α × γ) →o (β × γ)) (a : α) (u : γ) : fb f a u = (f (a, u)).2 := rfl

/-- **The fixpoint trace** `Tr(f)(a) = π₁ (f (a, lfp (fb f a)))`. -/
def tr (f : (α × γ) →o (β × γ)) : α →o β :=
  OrderHom.fst.comp (f.comp (OrderHom.id.prod (pfp (fb f))))

@[simp] theorem tr_apply (f : (α × γ) →o (β × γ)) (a : α) :
    tr f a = (f (a, pfp (fb f) a)).1 := rfl

/-- **The heterogeneous rolling rule** `lfp (g ∘ h) = g (lfp (h ∘ g))` for `g : α →o β`, `h : β →o α`
(the same proof as `ConwayTrace.rolling`, between two different lattices — exactly what the sliding
axiom needs when the two trace wires `U`, `V` are different objects). -/
theorem rolling' (g : α →o β) (h : β →o α) : lfp (g.comp h) = g (lfp (h.comp g)) := by
  apply le_antisymm
  · apply OrderHom.lfp_le
    show g (h (g (lfp (h.comp g)))) ≤ g (lfp (h.comp g))
    apply g.monotone
    show h (g (lfp (h.comp g))) ≤ lfp (h.comp g)
    exact le_of_eq (OrderHom.map_lfp (h.comp g))
  · have key : lfp (h.comp g) ≤ h (lfp (g.comp h)) := by
      apply OrderHom.lfp_le
      show h (g (h (lfp (g.comp h)))) ≤ h (lfp (g.comp h))
      apply h.monotone
      show g (h (lfp (g.comp h))) ≤ lfp (g.comp h)
      exact le_of_eq (OrderHom.map_lfp (g.comp h))
    calc g (lfp (h.comp g)) ≤ g (h (lfp (g.comp h))) := g.monotone key
      _ = lfp (g.comp h) := OrderHom.map_lfp (g.comp h)

/-- **Product Bekić.** The least fixed point of `F : U × V →o U × V` is computed by *nested* least
fixed points: solve the `V`-wire for each `u` (`W u`), then solve the `U`-wire of `u ↦ (F (u, W u)).1`
(`us`), and the joint fixed point is `(us, W us)`. The algebraic heart of `trace_vanish_tens` (trace
over `U ⊗ V` = nested traces). -/
theorem lfp_prod {U V : Type u} [CompleteLattice U] [CompleteLattice V] (F : (U × V) →o (U × V))
    (W : U →o V) (us : U)
    (hW : ∀ u, (F (u, W u)).2 = W u)
    (hWmin : ∀ u v, (F (u, v)).2 ≤ v → W u ≤ v)
    (hus : (F (us, W us)).1 = us)
    (husmin : ∀ u, (F (u, W u)).1 ≤ u → us ≤ u) :
    lfp F = (us, W us) := by
  apply le_antisymm
  · exact OrderHom.lfp_le F ⟨le_of_eq hus, le_of_eq (hW us)⟩
  · set ab := lfp F with hab
    have hFb : (F ab).2 = ab.2 := congrArg Prod.snd (OrderHom.map_lfp F)
    have hFa : (F ab).1 = ab.1 := congrArg Prod.fst (OrderHom.map_lfp F)
    have hWa : W ab.1 ≤ ab.2 := hWmin ab.1 ab.2 (le_of_eq hFb)
    have hua : us ≤ ab.1 := by
      apply husmin
      calc (F (ab.1, W ab.1)).1 ≤ (F (ab.1, ab.2)).1 :=
            (F.monotone (⟨le_refl _, hWa⟩ : (ab.1, W ab.1) ≤ (ab.1, ab.2))).1
        _ = ab.1 := hFa
    exact ⟨hua, le_trans (W.monotone hua) hWa⟩

/-- **Superposing** at the level of the trace: tracing `f` with a passive wire `W` alongside equals
`W` alongside the trace of `f` — because the feedback only ever touches the `U`-wire, leaving `W`
untouched. (The `trace_superpose` JSV axiom, as a fact about `tr`.) -/
theorem tr_superpose {W : Type u} [CompleteLattice W] (f : (β × γ) →o (δ × γ)) :
    tr ((omAssocInv.comp (omProdMap (OrderHom.id : W →o W) f)).comp omAssoc)
      = omProdMap (OrderHom.id : W →o W) (tr f) := by
  refine OrderHom.ext _ _ (funext fun p => ?_)
  have hfbeq : fb ((omAssocInv.comp (omProdMap (OrderHom.id : W →o W) f)).comp omAssoc) p
      = fb f p.2 := by ext u; rfl
  have hpfp : pfp (fb ((omAssocInv.comp (omProdMap (OrderHom.id : W →o W) f)).comp omAssoc)) p
      = pfp (fb f) p.2 := by simp only [pfp_apply]; rw [hfbeq]
  refine Prod.ext rfl ?_
  show (f (p.2, pfp (fb ((omAssocInv.comp (omProdMap (OrderHom.id : W →o W) f)).comp omAssoc)) p)).1
      = (f (p.2, pfp (fb f) p.2)).1
  rw [hpfp]

/-- **Vanishing-II** at the level of the trace: tracing over the product wire `U × V` equals tracing
over `U` the trace over `V`. The wiring of the nested traces onto the product Bekić `lfp_prod`. (The
`trace_vanish_tens` JSV axiom, as a fact about `tr`.) -/
theorem tr_vanish_tens {X Y U V : Type u} [CompleteLattice X] [CompleteLattice Y]
    [CompleteLattice U] [CompleteLattice V] (f : (X × (U × V)) →o (Y × (U × V))) :
    tr f = tr (tr ((omAssocInv.comp f).comp omAssoc)) := by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  set F := fb f x with hFdef
  set W := pfp (OrderHom.curry (OrderHom.snd.comp F)) with hWdef
  set Hmap := OrderHom.fst.comp (F.comp (OrderHom.id.prod W)) with hHdef
  -- the joint fixed point splits as nested ones (product Bekić); everything else is definitional
  have hbekic : lfp F = (lfp Hmap, W (lfp Hmap)) :=
    lfp_prod F W (lfp Hmap)
      (fun u => pfp_fixed (OrderHom.curry (OrderHom.snd.comp F)) u)
      (fun u v h => pfp_least (OrderHom.curry (OrderHom.snd.comp F)) u h)
      (OrderHom.map_lfp Hmap) (fun u h => OrderHom.lfp_le Hmap h)
  simp only [tr_apply, pfp_apply]
  rw [← hFdef, hbekic]
  rfl

end combinators

/-! ### The instance — the category of complete lattices is a traced SMC via the fixpoint trace -/

/-- **The category of domains (complete lattices) is a traced SMC**, with monotone maps as morphisms,
the product `×` as tensor, and the **Conway fixpoint trace** `tr`. The full Joyal–Street–Verity axiom
set is discharged from the `ConwayTrace` identities through the concrete product bookkeeping — the
Hasegawa "only-if" direction in full, on the simplest domains. -/
def domainFixpointTracedSMC : TracedSMC where
  Obj := CLat
  Hom := fun X Y => X.carrier →o Y.carrier
  id := fun X => OrderHom.id
  comp := fun f g => g.comp f
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  tens := fun X Y => ⟨X.carrier × Y.carrier⟩
  unit := ⟨PUnit⟩
  tensH := fun f g => omProdMap f g
  braid := fun _ _ => omSwap
  trace := fun f => tr f
  aHom := fun _ _ _ => omAssoc
  aInv := fun _ _ _ => omAssocInv
  a_hom_inv := fun _ _ _ => by ext p <;> rfl
  a_inv_hom := fun _ _ _ => by ext p <;> rfl
  ruHom := fun _ => OrderHom.fst
  ruInv := fun _ => omRuInv
  ru_hom_inv := fun _ => by ext p <;> first | rfl | exact Subsingleton.elim _ _
  ru_inv_hom := fun _ => by ext p; rfl
  luHom := fun _ => OrderHom.snd
  luInv := fun _ => omLuInv
  lu_hom_inv := fun _ => by ext p <;> first | rfl | exact Subsingleton.elim _ _
  lu_inv_hom := fun _ => by ext p; rfl
  trace_nat_left := fun g f => by ext a; rfl
  trace_nat_right := fun f g => by ext a; rfl
  trace_slide := fun {X Y U V} f h => by
    ext x
    show tr ((omProdMap OrderHom.id h).comp f) x = tr (f.comp (omProdMap OrderHom.id h)) x
    set a : U.carrier →o V.carrier :=
      OrderHom.snd.comp (f.comp ((OrderHom.const _ x).prod OrderHom.id)) with ha
    have hkf : fb ((omProdMap OrderHom.id h).comp f) x = h.comp a := by ext u; rfl
    have hmf : fb (f.comp (omProdMap OrderHom.id h)) x = a.comp h := by ext v; rfl
    have hroll : pfp (fb ((omProdMap OrderHom.id h).comp f)) x
        = h (pfp (fb (f.comp (omProdMap OrderHom.id h))) x) := by
      rw [pfp_apply, pfp_apply, hkf, hmf]; exact rolling' h a
    show (f (x, pfp (fb ((omProdMap OrderHom.id h).comp f)) x)).1
        = (f (x, h (pfp (fb (f.comp (omProdMap OrderHom.id h))) x))).1
    rw [hroll]
  trace_yank := fun U => by
    ext a
    show pfp (fb (omSwap : (U.carrier × U.carrier) →o _)) a = a
    rw [pfp_apply]
    exact (OrderHom.map_lfp (fb (omSwap : (U.carrier × U.carrier) →o _) a)).symm
  trace_vanish_unit := fun {X Y} f => by
    ext a
    show (f (a, pfp (fb f) a)).1 = (f (a, PUnit.unit)).1
    rw [Subsingleton.elim (pfp (fb f) a) PUnit.unit]
  trace_vanish_tens := fun {X Y U V} f => tr_vanish_tens f
  trace_superpose := fun {W X Y U} f => tr_superpose f

end RelExist.DomainFixpoint
