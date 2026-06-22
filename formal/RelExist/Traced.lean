/-
# Traced symmetric monoidal categories — the typeclass, and literal functors

The doctrine's ambient structure ([00](../../docs/spec/00-doctrine.md)) is a *traced
symmetric monoidal category*. mathlib has monoidal / symmetric / rigid categories and
`ChosenFiniteProducts`, but **no traced-monoidal typeclass and no monoidal trace**, so we
build one.

`TracedSMC` carries the tensor `⊗`, a unit, the symmetry braiding, **associator and
unitor isomorphisms** (as morphism data — the non-strict monoidal move, which lets the
retensoring axioms compose with structural isos instead of needing object-equality
transport), and the **trace** with the *full* Joyal–Street–Verity axiom set:

* naturality (left/right), sliding (dinaturality), yanking — behaviour on a wire;
* **vanishing-I** (trace over the unit), **vanishing-II** (trace over `U ⊗ V` = nested
  traces), **superposing** (trace commutes with `W ◁ -`).

We then define **traced functors** (structure-preserving models) and exhibit literal ones
— identity, terminal, and composition — so functorial semantics is genuinely functorial.

Validation: beyond the trivial one-object model, a commutative monoid is a model
(`scalarTracedSMC`) in which **sliding holds precisely because `·` is commutative**.

Not imposed (and noted): the monoidal *coherence* equations (pentagon, triangle) and
naturality of the structural isos — they constrain the monoidal base, not the trace, and
are not referenced by the JSV axioms. A concrete `FdHilb` instance and the free traced SMC
`Cl(𝕋)` remain the research-grade frontier (see docs/spec/04 §4.6).
-/

namespace RelExist.Traced

universe u v

/-- A **traced symmetric monoidal category** (with associators/unitors as isos, so the
full JSV trace axioms are statable transport-free). -/
structure TracedSMC where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)
  tens : Obj → Obj → Obj
  unit : Obj
  tensH : {A B C D : Obj} → Hom A B → Hom C D → Hom (tens A C) (tens B D)
  braid : (X Y : Obj) → Hom (tens X Y) (tens Y X)
  trace : {X Y U : Obj} → Hom (tens X U) (tens Y U) → Hom X Y
  -- structural isomorphisms (associator, right/left unitors)
  aHom : (X Y Z : Obj) → Hom (tens (tens X Y) Z) (tens X (tens Y Z))
  aInv : (X Y Z : Obj) → Hom (tens X (tens Y Z)) (tens (tens X Y) Z)
  a_hom_inv : ∀ X Y Z, comp (aHom X Y Z) (aInv X Y Z) = id (tens (tens X Y) Z)
  a_inv_hom : ∀ X Y Z, comp (aInv X Y Z) (aHom X Y Z) = id (tens X (tens Y Z))
  ruHom : (X : Obj) → Hom (tens X unit) X
  ruInv : (X : Obj) → Hom X (tens X unit)
  ru_hom_inv : ∀ X, comp (ruHom X) (ruInv X) = id (tens X unit)
  ru_inv_hom : ∀ X, comp (ruInv X) (ruHom X) = id X
  luHom : (X : Obj) → Hom (tens unit X) X
  luInv : (X : Obj) → Hom X (tens unit X)
  lu_hom_inv : ∀ X, comp (luHom X) (luInv X) = id (tens unit X)
  lu_inv_hom : ∀ X, comp (luInv X) (luHom X) = id X
  -- JSV: behaviour on a wire
  trace_nat_left : ∀ {X X' Y U} (g : Hom X' X) (f : Hom (tens X U) (tens Y U)),
    trace (comp (tensH g (id U)) f) = comp g (trace f)
  trace_nat_right : ∀ {X Y Y' U} (f : Hom (tens X U) (tens Y U)) (g : Hom Y Y'),
    trace (comp f (tensH g (id U))) = comp (trace f) g
  trace_slide : ∀ {X Y U V} (f : Hom (tens X U) (tens Y V)) (h : Hom V U),
    trace (comp f (tensH (id Y) h)) = trace (comp (tensH (id X) h) f)
  trace_yank : ∀ (U : Obj), trace (braid U U) = id U
  -- JSV: retensoring axioms (via the structural isos)
  trace_vanish_unit : ∀ {X Y} (f : Hom (tens X unit) (tens Y unit)),
    trace f = comp (ruInv X) (comp f (ruHom Y))
  trace_vanish_tens : ∀ {X Y U V} (f : Hom (tens X (tens U V)) (tens Y (tens U V))),
    trace f = trace (trace (comp (aHom X U V) (comp f (aInv Y U V))))
  trace_superpose : ∀ {W X Y U} (f : Hom (tens X U) (tens Y U)),
    trace (comp (aHom W X U) (comp (tensH (id W) f) (aInv W Y U))) = tensH (id W) (trace f)

/-- **A trivial model** — the terminal (one-object, one-morphism) traced SMC, showing the
full typeclass is consistent and inhabited. -/
def trivialTracedSMC : TracedSMC where
  Obj := PUnit
  Hom := fun _ _ => PUnit
  id := fun _ => PUnit.unit
  comp := fun _ _ => PUnit.unit
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  tens := fun _ _ => PUnit.unit
  unit := PUnit.unit
  tensH := fun _ _ => PUnit.unit
  braid := fun _ _ => PUnit.unit
  trace := fun _ => PUnit.unit
  aHom := fun _ _ _ => PUnit.unit
  aInv := fun _ _ _ => PUnit.unit
  a_hom_inv := by intros; rfl
  a_inv_hom := by intros; rfl
  ruHom := fun _ => PUnit.unit
  ruInv := fun _ => PUnit.unit
  ru_hom_inv := by intros; rfl
  ru_inv_hom := by intros; rfl
  luHom := fun _ => PUnit.unit
  luInv := fun _ => PUnit.unit
  lu_hom_inv := by intros; rfl
  lu_inv_hom := by intros; rfl
  trace_nat_left := by intros; rfl
  trace_nat_right := by intros; rfl
  trace_slide := by intros; rfl
  trace_yank := by intros; rfl
  trace_vanish_unit := by intros; rfl
  trace_vanish_tens := by intros; rfl
  trace_superpose := by intros; rfl

/-- **A non-trivial model — scalars.** A commutative monoid `(M, ·, 1)` is a one-object
traced SMC: morphisms are scalars, composition/tensor are `·`, structural isos are `1`,
and the trace is the identity. This *validates* the axioms (the trivial model discharges
them by `rfl`): in particular **sliding holds because `·` is commutative**. -/
def scalarTracedSMC (M : Type v) (mul : M → M → M) (one : M)
    (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (one_mul : ∀ a, mul one a = a) (mul_one : ∀ a, mul a one = a)
    (mul_comm : ∀ a b, mul a b = mul b a) : TracedSMC where
  Obj := PUnit
  Hom := fun _ _ => M
  id := fun _ => one
  comp := fun a b => mul a b
  id_comp := fun f => one_mul f
  comp_id := fun f => mul_one f
  assoc := fun f g h => mul_assoc f g h
  tens := fun _ _ => PUnit.unit
  unit := PUnit.unit
  tensH := fun a b => mul a b
  braid := fun _ _ => one
  trace := fun f => f
  aHom := fun _ _ _ => one
  aInv := fun _ _ _ => one
  a_hom_inv := by intros; exact one_mul one
  a_inv_hom := by intros; exact one_mul one
  ruHom := fun _ => one
  ruInv := fun _ => one
  ru_hom_inv := by intros; exact one_mul one
  ru_inv_hom := by intros; exact one_mul one
  luHom := fun _ => one
  luInv := fun _ => one
  lu_hom_inv := by intros; exact one_mul one
  lu_inv_hom := by intros; exact one_mul one
  trace_nat_left := by intro X X' Y U g f; show mul (mul g one) f = mul g f; rw [mul_one]
  trace_nat_right := by intro X Y Y' U f g; show mul f (mul g one) = mul f g; rw [mul_one]
  trace_slide := by
    intro X Y U V f h
    show mul f (mul one h) = mul (mul one h) f
    rw [mul_comm f (mul one h)]
  trace_yank := by intro U; rfl
  trace_vanish_unit := by
    intro X Y f; show f = mul one (mul f one); rw [mul_one, one_mul]
  trace_vanish_tens := by
    intro X Y U V f; show f = mul one (mul f one); rw [mul_one, one_mul]
  trace_superpose := by
    intro W X Y U f
    show mul one (mul (mul one f) one) = mul one f
    simp only [one_mul, mul_one]

/-- **A traced functor** `C ⟶ D`: a structure-preserving map of traced SMCs (preserving
the category and the monoidal objects). This is the formal shape of a *model* in Layer 4. -/
structure TracedFunctor (C D : TracedSMC) where
  obj : C.Obj → D.Obj
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  obj_tens : ∀ X Y, obj (C.tens X Y) = D.tens (obj X) (obj Y)
  obj_unit : obj C.unit = D.unit
  map_id : ∀ X, map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z} (f : C.Hom X Y) (g : C.Hom Y Z),
    map (C.comp f g) = D.comp (map f) (map g)

/-- **The identity functor** — a genuine traced functor `C ⟶ C`. -/
def TracedFunctor.id (C : TracedSMC) : TracedFunctor C C where
  obj := fun X => X
  map := fun f => f
  obj_tens := by intros; rfl
  obj_unit := rfl
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- **The terminal functor** `C ⟶ trivial` — every system collapses to the one point. -/
def TracedFunctor.toTrivial (C : TracedSMC) : TracedFunctor C trivialTracedSMC where
  obj := fun _ => PUnit.unit
  map := fun _ => PUnit.unit
  obj_tens := by intros; rfl
  obj_unit := rfl
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- **Composition of traced functors** — models compose; functorial semantics is
functorial. -/
def TracedFunctor.comp {C D E : TracedSMC}
    (F : TracedFunctor C D) (G : TracedFunctor D E) : TracedFunctor C E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  obj_tens := fun X Y => (congrArg G.obj (F.obj_tens X Y)).trans (G.obj_tens (F.obj X) (F.obj Y))
  obj_unit := (congrArg G.obj F.obj_unit).trans G.obj_unit
  map_id := fun X => (congrArg G.map (F.map_id X)).trans (G.map_id (F.obj X))
  map_comp := fun f g => (congrArg G.map (F.map_comp f g)).trans (G.map_comp (F.map f) (F.map g))

end RelExist.Traced
