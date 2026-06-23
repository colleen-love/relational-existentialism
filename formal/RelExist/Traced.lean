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
are not referenced by the JSV axioms. A concrete matrix instance (`Scratch/MatrixModel.lean`,
trace = partial trace) is now built; only the free traced SMC `Cl(𝕋)` over all objects
remains the research-grade frontier (see docs/spec/04 §4.6).
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

/-! ### A literal functor out of a free object

The full free traced SMC `Cl(𝕋)` (a colored PROP) is research-grade. But its **scalar
fragment** — the endomorphisms of the unit — is, in the free traced SMC on one object, the
**free commutative monoid on one generator** (the generator being the loop/dimension
`δ = Tr(id)`). That free object *is* `(ℕ, +)`, which we can build concretely, with its
universal property, and so obtain a genuine literal functor determined by where the
generator goes. -/

/-- A commutative monoid, bundled — the data of a one-object (scalar) traced SMC. -/
structure CMon where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_comm : ∀ a b, mul a b = mul b a

/-- Every commutative monoid is a (one-object, scalar) traced SMC. -/
def CMon.toTracedSMC (A : CMon) : TracedSMC :=
  scalarTracedSMC A.carrier A.mul A.one A.mul_assoc A.one_mul A.mul_one A.mul_comm

/-- A homomorphism of commutative monoids. -/
structure CMonHom (A B : CMon) where
  toFun : A.carrier → B.carrier
  map_one : toFun A.one = B.one
  map_mul : ∀ a b, toFun (A.mul a b) = B.mul (toFun a) (toFun b)

/-- **A traced functor from a monoid homomorphism.** A hom `φ : A → B` *is* a model
interpreting the scalars of `A` in `B` — a literal traced functor carrying genuine data,
beyond identity/terminal. -/
def TracedFunctor.ofCMonHom {A B : CMon} (φ : CMonHom A B) :
    TracedFunctor A.toTracedSMC B.toTracedSMC where
  obj := fun _ => PUnit.unit
  map := fun f => φ.toFun f
  obj_tens := by intros; rfl
  obj_unit := rfl
  map_id := fun _ => φ.map_one
  map_comp := fun f g => φ.map_mul f g

/-- `n`-fold product of `b` — the action of the free generator iterated. -/
def CMon.npow (B : CMon) (b : B.carrier) : Nat → B.carrier
  | 0 => B.one
  | n + 1 => B.mul (B.npow b n) b

theorem CMon.npow_add (B : CMon) (b : B.carrier) (m n : Nat) :
    B.npow b (m + n) = B.mul (B.npow b m) (B.npow b n) := by
  induction n with
  | zero => exact (B.mul_one _).symm
  | succ n ih =>
    show B.mul (B.npow b (m + n)) b = B.mul (B.npow b m) (B.mul (B.npow b n) b)
    rw [ih, B.mul_assoc]

/-- **`(ℕ, +)` — the free commutative monoid on one generator** (the scalar fragment of
the free traced SMC on one object). -/
def natCMon : CMon where
  carrier := Nat
  mul := Nat.add
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_comm := Nat.add_comm

/-- **The universal map (existence).** Any choice of image `b` for the generator extends to
a homomorphism `ℕ → B`, `n ↦ bⁿ`. -/
def natCMon.lift (B : CMon) (b : B.carrier) : CMonHom natCMon B where
  toFun := B.npow b
  map_one := rfl
  map_mul := fun m n => B.npow_add b m n

/-- **The universal property (uniqueness).** Every homomorphism out of `ℕ` is the lift of
the image of `1` — so `ℕ` is genuinely free on one generator. -/
theorem natCMon.lift_unique (B : CMon) (ψ : CMonHom natCMon B) (n : Nat) :
    ψ.toFun n = B.npow (ψ.toFun (1 : Nat)) n := by
  induction n with
  | zero => exact ψ.map_one
  | succ n ih =>
    have h : ψ.toFun (n + 1) = B.mul (ψ.toFun n) (ψ.toFun (1 : Nat)) := ψ.map_mul n (1 : Nat)
    rw [h, ih]; rfl

/-- **A literal functor out of the free object.** Determined by the image `b` of the
generator (the loop/dimension `δ`): the universal traced functor from the free scalar SMC.
The full free traced SMC `Cl(𝕋)` over all objects remains the research-grade construction;
this is its scalar fragment, done. -/
def TracedFunctor.fromFreeScalar (B : CMon) (b : B.carrier) :
    TracedFunctor natCMon.toTracedSMC B.toTracedSMC :=
  TracedFunctor.ofCMonHom (natCMon.lift B b)

/-! ### Free on `k` generators — the multi-color scalar fragment

The one-generator result extends to `k` generators: `ℕᵏ` is the free commutative monoid on
`k` generators (the scalar fragment of the free traced SMC on `k` objects/colors), with its
full universal property — existence (`freeCMon.lift`) and uniqueness (`freeCMon.lift_unique`).
-/

/-- Middle-four interchange in a commutative monoid: `(ab)(cd) = (ac)(bd)`. The fact that
makes a *tuple* of independent generators combine coherently — commutativity is exactly
what lets the factors be regrouped. -/
theorem CMon.mul_mul_mul_comm (B : CMon) (a b c d : B.carrier) :
    B.mul (B.mul a b) (B.mul c d) = B.mul (B.mul a c) (B.mul b d) :=
  calc B.mul (B.mul a b) (B.mul c d)
      = B.mul a (B.mul b (B.mul c d)) := B.mul_assoc a b _
    _ = B.mul a (B.mul (B.mul b c) d) := by rw [← B.mul_assoc b c d]
    _ = B.mul a (B.mul (B.mul c b) d) := by rw [B.mul_comm b c]
    _ = B.mul a (B.mul c (B.mul b d)) := by rw [B.mul_assoc c b d]
    _ = B.mul (B.mul a c) (B.mul b d) := (B.mul_assoc a c _).symm

/-- Prepend a free generator: `ℕ ×' B`, the product of `(ℕ,+)` with `B` (carrier literally
`Nat × B.carrier`, so numerals and `+` on the new generator are the genuine `Nat` ones). -/
def CMon.natProd (B : CMon) : CMon where
  carrier := Nat × B.carrier
  mul := fun x y => (x.1 + y.1, B.mul x.2 y.2)
  one := (0, B.one)
  mul_assoc := fun a b c => by
    show (a.1 + b.1 + c.1, B.mul (B.mul a.2 b.2) c.2)
       = (a.1 + (b.1 + c.1), B.mul a.2 (B.mul b.2 c.2))
    rw [Nat.add_assoc, B.mul_assoc]
  one_mul := fun a => by
    show (0 + a.1, B.mul B.one a.2) = a
    rw [Nat.zero_add, B.one_mul]
  mul_one := fun a => by
    show (a.1 + 0, B.mul a.2 B.one) = a
    rw [Nat.add_zero, B.mul_one]
  mul_comm := fun a b => by
    show (a.1 + b.1, B.mul a.2 b.2) = (b.1 + a.1, B.mul b.2 a.2)
    rw [Nat.add_comm a.1, B.mul_comm a.2]

/-- The trivial (one-element) commutative monoid — the free monoid on *zero* generators. -/
def trivCMon : CMon where
  carrier := PUnit
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl
  mul_comm := fun _ _ => rfl

/-- **The free commutative monoid on `k` generators**, `ℕᵏ`, built by prepending one free
generator at a time — the scalar fragment of the free traced SMC on `k` objects (colors). -/
def freeCMon : Nat → CMon
  | 0 => trivCMon
  | k + 1 => CMon.natProd (freeCMon k)

/-- The `i`-th generator of `freeCMon k`: the basis tuple `eᵢ` (one in slot `i`, zero
elsewhere). Indices `i ≥ k` collapse to the unit. -/
def freeCMon.gen : (k : Nat) → Nat → (freeCMon k).carrier
  | 0, _ => PUnit.unit
  | _ + 1, 0 => (1, (freeCMon _).one)
  | k + 1, i + 1 => (0, freeCMon.gen k i)

/-- **The universal map (existence).** Any choice of images `g i` for the generators
extends to a homomorphism `freeCMon k → B`, sending the tuple `(n₀,…,n_{k-1})` to
`g₀^{n₀} · … · g_{k-1}^{n_{k-1}}`. -/
def freeCMon.lift (B : CMon) : (k : Nat) → (Nat → B.carrier) → CMonHom (freeCMon k) B
  | 0, _ =>
    { toFun := fun _ => B.one
      map_one := rfl
      map_mul := fun _ _ => (B.one_mul B.one).symm }
  | k + 1, g =>
    let tail := freeCMon.lift B k (fun i => g (i + 1))
    { toFun := fun p => B.mul (B.npow (g 0) p.1) (tail.toFun p.2)
      map_one := by
        show B.mul (B.npow (g 0) 0) (tail.toFun (freeCMon k).one) = B.one
        rw [tail.map_one]; exact B.one_mul B.one
      map_mul := fun x y => by
        show B.mul (B.npow (g 0) (x.1 + y.1)) (tail.toFun ((freeCMon k).mul x.2 y.2))
           = B.mul (B.mul (B.npow (g 0) x.1) (tail.toFun x.2))
                   (B.mul (B.npow (g 0) y.1) (tail.toFun y.2))
        rw [B.npow_add, tail.map_mul,
            B.mul_mul_mul_comm (B.npow (g 0) x.1) (B.npow (g 0) y.1)
              (tail.toFun x.2) (tail.toFun y.2)] }

/-- **The universal property (uniqueness).** Every homomorphism `ψ` out of `freeCMon k` is
the lift of the images it assigns to the generators — so `freeCMon k` is genuinely free on
`k` generators. -/
theorem freeCMon.lift_unique (B : CMon) :
    ∀ (k : Nat) (ψ : CMonHom (freeCMon k) B) (p : (freeCMon k).carrier),
      ψ.toFun p = (freeCMon.lift B k (fun i => ψ.toFun (freeCMon.gen k i))).toFun p
  | 0, ψ, _ => ψ.map_one
  | k + 1, ψ, p => by
    obtain ⟨m, r⟩ := p
    -- restrict ψ along the second injection  r ↦ (0, r)  to get a hom out of freeCMon k
    let ψ' : CMonHom (freeCMon k) B :=
      { toFun := fun r => ψ.toFun ((0 : Nat), r)
        map_one := ψ.map_one
        map_mul := fun r r' => ψ.map_mul ((0 : Nat), r) ((0 : Nat), r') }
    -- step 2: along the first injection  n ↦ (n, one),  ψ is the npow of ψ(e₀)
    have hfirst : ∀ n : Nat,
        ψ.toFun (n, (freeCMon k).one) = B.npow (ψ.toFun (freeCMon.gen (k+1) 0)) n := by
      intro n
      induction n with
      | zero => exact ψ.map_one
      | succ n ih =>
        have hpair : ((n + 1 : Nat), (freeCMon k).one)
            = (freeCMon (k+1)).mul (n, (freeCMon k).one) ((1 : Nat), (freeCMon k).one) := by
          show ((n + 1 : Nat), (freeCMon k).one)
             = ((n + 1 : Nat), (freeCMon k).mul (freeCMon k).one (freeCMon k).one)
          rw [(freeCMon k).mul_one]
        rw [hpair, ψ.map_mul, ih]; rfl
    -- step 1: split  (m, r) = (m, one) · (0, r)
    have hpairP : ((m, r) : (freeCMon (k+1)).carrier)
        = (freeCMon (k+1)).mul (m, (freeCMon k).one) ((0 : Nat), r) := by
      show ((m, r) : (freeCMon (k+1)).carrier) = (m, (freeCMon k).mul (freeCMon k).one r)
      rw [(freeCMon k).one_mul]
    have hsplit : ψ.toFun (m, r)
        = B.mul (ψ.toFun (m, (freeCMon k).one)) (ψ.toFun ((0 : Nat), r)) :=
      (congrArg ψ.toFun hpairP).trans (ψ.map_mul _ _)
    -- step 3: the restricted hom ψ' is its own lift, by induction on k
    have hsnd : ψ.toFun ((0 : Nat), r)
        = (freeCMon.lift B k (fun i => ψ.toFun ((0 : Nat), freeCMon.gen k i))).toFun r :=
      freeCMon.lift_unique B k ψ' r
    rw [hsplit, hfirst, hsnd]; rfl

/-- **The literal functor out of the free object on `k` generators.** A model is fixed by
where the `k` generators (colors) are sent — `TracedFunctor.ofCMonHom` of the universal
lift. The one-generator case is `fromFreeScalar`; this is its full multi-color form. -/
def TracedFunctor.fromFreeCMon (B : CMon) (k : Nat) (g : Nat → B.carrier) :
    TracedFunctor (freeCMon k).toTracedSMC B.toTracedSMC :=
  TracedFunctor.ofCMonHom (freeCMon.lift B k g)

end RelExist.Traced
