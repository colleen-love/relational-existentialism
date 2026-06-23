/-
# Monoidal coherence — the layer the trace doesn't need, made explicit

`TracedSMC` deliberately omits the monoidal *coherence* equations (naturality of the
structural isos, pentagon, triangle, braiding naturality, symmetry, hexagon): they constrain
the monoidal **base**, not the trace, and the JSV trace axioms never reference them. This file
**layers them back on** as a refinement `CoherentTracedSMC extends TracedSMC`, so that a
"coherent traced SMC" is the fully-fledged notion — and shows it is non-vacuous (the trivial
and scalar models are coherent; `Rel` is too, see `Scratch/RelCoherence.lean`).

The eight coherence laws are the standard symmetric-monoidal ones:
* naturality of the associator and the two unitors;
* the **pentagon** (associativity coherence) and **triangle** (unit coherence);
* naturality of the braiding, its **symmetry** (`σ∘σ = id`), and the **hexagon**.
-/
import RelExist.Traced

namespace RelExist.Traced

universe u v

/-- A **coherent** traced symmetric monoidal category: a `TracedSMC` whose structural isos
additionally satisfy the symmetric-monoidal coherence equations (naturality, pentagon,
triangle, braiding symmetry and hexagon). -/
structure CoherentTracedSMC extends TracedSMC.{u, v} where
  /-- naturality of the associator -/
  assoc_nat : ∀ {X X' Y Y' Z Z'} (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z'),
    comp (tensH (tensH f g) h) (aHom X' Y' Z') = comp (aHom X Y Z) (tensH f (tensH g h))
  /-- naturality of the left unitor -/
  lu_nat : ∀ {X Y} (f : Hom X Y), comp (tensH (id unit) f) (luHom Y) = comp (luHom X) f
  /-- naturality of the right unitor -/
  ru_nat : ∀ {X Y} (f : Hom X Y), comp (tensH f (id unit)) (ruHom Y) = comp (ruHom X) f
  /-- the **pentagon**: the two reassociations of `((W⊗X)⊗Y)⊗Z` agree -/
  pentagon : ∀ W X Y Z,
    comp (aHom (tens W X) Y Z) (aHom W X (tens Y Z))
      = comp (tensH (aHom W X Y) (id Z))
          (comp (aHom W (tens X Y) Z) (tensH (id W) (aHom X Y Z)))
  /-- the **triangle**: associator and unitors agree on `(X⊗I)⊗Y` -/
  triangle : ∀ X Y,
    comp (aHom X unit Y) (tensH (id X) (luHom Y)) = tensH (ruHom X) (id Y)
  /-- naturality of the braiding -/
  braid_nat : ∀ {X X' Y Y'} (f : Hom X X') (g : Hom Y Y'),
    comp (tensH f g) (braid X' Y') = comp (braid X Y) (tensH g f)
  /-- **symmetry**: the braiding is its own inverse, `σ∘σ = id` -/
  braid_symm : ∀ X Y, comp (braid X Y) (braid Y X) = id (tens X Y)
  /-- the **hexagon**: braiding is compatible with the associator -/
  hexagon : ∀ X Y Z,
    comp (aHom X Y Z) (comp (braid X (tens Y Z)) (aHom Y Z X))
      = comp (tensH (braid X Y) (id Z)) (comp (aHom Y X Z) (tensH (id Y) (braid X Z)))

/-- **The trivial model is coherent** — every coherence law holds by `rfl`, so the augmented
typeclass is consistent. -/
def trivialCoherentTracedSMC : CoherentTracedSMC where
  toTracedSMC := trivialTracedSMC
  assoc_nat := by intros; rfl
  lu_nat := by intros; rfl
  ru_nat := by intros; rfl
  pentagon := by intros; rfl
  triangle := by intros; rfl
  braid_nat := by intros; rfl
  braid_symm := by intros; rfl
  hexagon := by intros; rfl

/-- **A commutative monoid is a coherent model.** Each coherence law reduces to a
commutative-monoid identity — associativity for the associator laws, commutativity for the
braiding laws — so the scalar model validates the full coherent typeclass, not just the trace
axioms. -/
def scalarCoherentTracedSMC (M : Type v) (mul : M → M → M) (one : M)
    (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
    (one_mul : ∀ a, mul one a = a) (mul_one : ∀ a, mul a one = a)
    (mul_comm : ∀ a b, mul a b = mul b a) : CoherentTracedSMC :=
  { toTracedSMC := scalarTracedSMC M mul one mul_assoc one_mul mul_one mul_comm
    assoc_nat := by
      intro X X' Y Y' Z Z' f g h
      show mul (mul (mul f g) h) one = mul one (mul f (mul g h))
      rw [mul_one, one_mul, mul_assoc]
    lu_nat := by
      intro X Y f; show mul (mul one f) one = mul one f
      rw [mul_one, one_mul]
    ru_nat := by
      intro X Y f; show mul (mul f one) one = mul one f
      rw [mul_one, mul_one, one_mul]
    pentagon := by
      intro W X Y Z
      show mul one one = mul (mul one one) (mul one (mul one one))
      simp only [one_mul, mul_one]
    triangle := by
      intro X Y; show mul one (mul one one) = mul one one
      simp only [one_mul, mul_one]
    braid_nat := by
      intro X X' Y Y' f g
      show mul (mul f g) one = mul one (mul g f)
      rw [mul_one, one_mul, mul_comm]
    braid_symm := by
      intro X Y; show mul one one = one
      rw [one_mul]
    hexagon := by
      intro X Y Z
      show mul one (mul one one) = mul (mul one one) (mul one (mul one one))
      simp only [one_mul, mul_one] }

end RelExist.Traced
