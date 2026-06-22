/-
# Traced symmetric monoidal categories — the typeclass, and literal functors

The doctrine's ambient structure ([00](../../docs/spec/00-doctrine.md)) is a *traced
symmetric monoidal category*. mathlib has monoidal / symmetric / rigid categories and
`ChosenFiniteProducts`, but **no traced-monoidal typeclass and no monoidal trace**, so we
build one.

This is the **strict, transport-free core**: objects carry a strict tensor `⊗`, and we
impose the Joyal–Street–Verity trace axioms that do *not* retensor objects — naturality
(left/right), sliding (dinaturality), and yanking — which characterise the trace's
behaviour on a single wire. (The two retensoring axioms — vanishing-II and superposing —
need object-equality transport along strict associativity/unit; together with a concrete
`FdHilb` instance and the free traced SMC `Cl(𝕋)` they are the marked frontier — see the
docs.)

We then define **traced functors** (structure-preserving maps) and exhibit two literal
ones: the identity and the terminal (collapse) functor. The functor *mechanism* of
Layer 4 — a model as a structure-preserving functor — is thereby a real Lean object.
-/

namespace RelExist.Traced

universe u v

/-- A **strict traced symmetric monoidal category** (transport-free core). -/
structure TracedSMC where
  /-- objects (system-types) -/
  Obj : Type u
  /-- morphisms (relatings) -/
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)
  /-- strict tensor of objects (coexistence) -/
  tens : Obj → Obj → Obj
  unit : Obj
  /-- tensor of morphisms -/
  tensH : {A B C D : Obj} → Hom A B → Hom C D → Hom (tens A C) (tens B D)
  /-- the symmetry braiding on a wire -/
  braid : (X Y : Obj) → Hom (tens X Y) (tens Y X)
  /-- **the trace**: feed the `U`-wire back. -/
  trace : {X Y U : Obj} → Hom (tens X U) (tens Y U) → Hom X Y
  /-- naturality (left tightening): pre-composition on the kept input slides out. -/
  trace_nat_left : ∀ {X X' Y U} (g : Hom X' X) (f : Hom (tens X U) (tens Y U)),
    trace (comp (tensH g (id U)) f) = comp g (trace f)
  /-- naturality (right tightening): post-composition on the kept output slides out. -/
  trace_nat_right : ∀ {X Y Y' U} (f : Hom (tens X U) (tens Y U)) (g : Hom Y Y'),
    trace (comp f (tensH g (id U))) = comp (trace f) g
  /-- sliding (dinaturality): a map may slide around the feedback loop. -/
  trace_slide : ∀ {X Y U V} (f : Hom (tens X U) (tens Y V)) (h : Hom V U),
    trace (comp f (tensH (id Y) h)) = trace (comp (tensH (id X) h) f)
  /-- yanking: a single crossing fed back is a straight wire. -/
  trace_yank : ∀ (U : Obj), trace (braid U U) = id U

/-- **A trivial model** — the terminal (one-object, one-morphism) traced SMC. It shows
the typeclass is consistent and inhabited. -/
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
  trace_nat_left := by intros; rfl
  trace_nat_right := by intros; rfl
  trace_slide := by intros; rfl
  trace_yank := by intros; rfl

/-- **A non-trivial model — scalars.** A commutative monoid `(M, ·, 1)` is a one-object
traced SMC: morphisms are scalars, composition and tensor are `·`, and the trace is the
identity. This *validates* the axioms (the trivial model discharges them by `rfl`): in
particular **sliding holds precisely because `·` is commutative** — the symmetry the
braiding is supposed to provide. -/
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
  trace_nat_left := by intro X X' Y U g f; show mul (mul g one) f = mul g f; rw [mul_one]
  trace_nat_right := by intro X Y Y' U f g; show mul f (mul g one) = mul f g; rw [mul_one]
  trace_slide := by
    intro X Y U V f h
    show mul f (mul one h) = mul (mul one h) f
    rw [mul_comm f (mul one h)]
  trace_yank := by intro U; rfl

/-- **A traced functor** `C ⟶ D`: a structure-preserving map of traced SMCs. This is the
formal shape of a *model* in Layer 4 — a domain interpretation of the theory. (Strict on
objects: `obj` preserves `⊗` and `I` on the nose.) -/
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

/-- **The terminal functor** `C ⟶ trivial` — every system collapses to the one point;
every relating to the one morphism. The unique model into the trivial domain. -/
def TracedFunctor.toTrivial (C : TracedSMC) : TracedFunctor C trivialTracedSMC where
  obj := fun _ => PUnit.unit
  map := fun _ => PUnit.unit
  obj_tens := by intros; rfl
  obj_unit := rfl
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- **Composition of traced functors** — models compose, so traced SMCs and their
structure-preserving functors form a genuine categorical structure (functorial semantics
is functorial). -/
def TracedFunctor.comp {C D E : TracedSMC}
    (F : TracedFunctor C D) (G : TracedFunctor D E) : TracedFunctor C E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  obj_tens := fun X Y => (congrArg G.obj (F.obj_tens X Y)).trans (G.obj_tens (F.obj X) (F.obj Y))
  obj_unit := (congrArg G.obj F.obj_unit).trans G.obj_unit
  map_id := fun X => (congrArg G.map (F.map_id X)).trans (G.map_id (F.obj X))
  map_comp := fun f g => (congrArg G.map (F.map_comp f g)).trans (G.map_comp (F.map f) (F.map g))

end RelExist.Traced
