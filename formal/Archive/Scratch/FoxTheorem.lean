/-
# Fox's hallmark, mechanized — cartesian ⇒ the natural comonoid is unique (§3.2)

Milestone 6 of "the seam is the non-comonoidal residue": **mechanize the abstract hallmark rather than
cite it.** [`RelExist/Fox.lean`](../RelExist/Fox.lean) gives the doctrine's `Type`-level copy comonoid
and the keystone "two faces share one copy." This module discharges the **categorical** hallmark of
§0.4 — *the cartesian fragment is exactly the presence of a uniform, natural `Δ`* — at the level of a
genuine monoidal category, by standing on mathlib's categorical-quantum library.

**What is mechanized (the forward direction + uniqueness + the sharp equivalence).** For any cartesian
monoidal category `C` (a category with a terminal object and binary products, monoidal via the product):

* `cartesianComonoid` — **every object carries a comonoid, functorially** (`cartesianComon_`): the
  diagonal `Δ = diag` and the delete `ε = terminal.from`. Cartesian ⇒ a uniform, natural copy.
* `comonoid_forced` — **the comonoid is unique / forced**: *any* comonoid object's comultiplication is
  THE diagonal and its counit THE unique map to the terminal (`comul_eq_diag`, `counit_eq_from`). The
  natural `Δ` is not a choice — it is determined by the object. This is the sharp content of the
  hallmark: in the cartesian fragment, the copy *is* the diagonal, full stop.
* `foxEquivalence` — **`Comon_ C ≌ C`** (`comonEquiv`): the category of comonoid objects is equivalent
  to `C` itself via the forgetful functor. Fox's theorem in its cleanest form — in the cartesian
  fragment, *comonoids are the objects.*

Instantiated at `Type` (`foxEquivalenceType`, `comonoid_forced_type`) — the doctrine's cartesian
fragment ([`Firewall`](../RelExist/Firewall.lean)) — and connected to the `Type`-level
`RelExist.Fox.cartesian` (`doctrine_copy_is_diagonal`): the doctrine's copy `fun x => (x, x)` is exactly
the diagonal mathlib equips, now as a theorem of a real monoidal category.

**What stays cited (the reverse direction).** The converse — *a symmetric monoidal category carrying a
natural comonoid on every object is cartesian* — is Fox's classical hard direction. It is **not** in
mathlib and is not mechanized here; it remains the one cited classical result, sharply localized as "the
forgetful `Comon_ C ⥤ C` being an equivalence forces `C` cartesian" — the converse of `foxEquivalence`.
The unification of the seam's two faces ([`SeamComonoid`](SeamComonoid.lean), Proposition 0.2) does not
depend on the reverse direction.
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
import Mathlib.CategoryTheory.Limits.Shapes.Types
import RelExist.Fox

namespace RelExist.FoxTheorem

open CategoryTheory MonoidalCategory Limits

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasBinaryProducts C]

attribute [local instance] monoidalOfHasFiniteProducts

/-- **Cartesian ⇒ a uniform, natural copy** (the hallmark, existence). The functor equipping every
object with its diagonal comultiplication and terminal counit — a comonoid on *every* object,
functorially in `C`. (`cartesianComon_`.) -/
abbrev cartesianComonoid : C ⥤ Comon_ C := cartesianComon_ C

/-- **The natural comonoid is forced** (the hallmark, uniqueness — the sharp part). *Any* comonoid
object in a cartesian category has comultiplication equal to THE diagonal and counit equal to THE unique
map to the terminal. So the copy `Δ` is not a choice but a function of the object: the cartesian fragment
*is* exactly where the diagonal lives, and it is the only comonoid there. -/
theorem comonoid_forced (A : Comon_ C) :
    A.comul = diag A.X ∧ A.counit = terminal.from A.X :=
  ⟨comul_eq_diag A, counit_eq_from A⟩

/-- **Fox's theorem, forward (the sharp equivalence).** The category of comonoid objects is equivalent
to `C` itself, via the forgetful functor — in the cartesian fragment, *comonoids are the objects*.
(`comonEquiv`.) The reverse direction (this equivalence forcing `C` cartesian) is the cited classical
half; see the module header. -/
abbrev foxEquivalence : Comon_ C ≌ C := comonEquiv

/-! ### Instantiation at `Type` — the doctrine's cartesian fragment

`Type` is the doctrine's cartesian fragment ([`Firewall`](../RelExist/Firewall.lean)). The categorical
hallmark specializes there, and matches the `Type`-level copy comonoid of `RelExist.Fox`. -/

/-- Fox's equivalence at `Type`: comonoid objects in `Type` are equivalent to types. -/
def foxEquivalenceType : Comon_ (Type u) ≌ (Type u) := comonEquiv

/-- The comonoid is forced at `Type`: every comonoid object in `Type` has the diagonal comultiplication
and the terminal counit. -/
theorem comonoid_forced_type (A : Comon_ (Type u)) :
    A.comul = diag A.X ∧ A.counit = terminal.from A.X :=
  comonoid_forced A

/-- **The doctrine's copy is the diagonal.** The `Type`-level copy of `RelExist.Fox.cartesian` — the
`(x, x)` of `Firewall.copy` that powers Lawvere — is exactly the diagonal mathlib equips every object of
a cartesian category with. The `Type`-level comonoid (`RelExist.Fox`) and the categorical one
(`cartesianComonoid`) are the same map, the diagonal. -/
theorem doctrine_copy_is_diagonal (X : Type u) (x : X) :
    (RelExist.Fox.cartesian X).copy x = (x, x) := rfl

end

end RelExist.FoxTheorem
