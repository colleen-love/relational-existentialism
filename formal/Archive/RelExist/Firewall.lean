/-
# The firewall — Layer 4, the cartesian side (sociology / mental health)

The plan's firewall: the social and mental-health domains sit in the **cartesian
fragment** (free copying, projections), so the **compact-closed / entanglement**
structure of the quantum fragment cannot be faithfully imported. "Two people are
entangled" is not merely unwise — it is *ill-typed*.

This module states the cartesian-side content, mathlib-free in `Type`:

* `copy` — the diagonal is free in a cartesian domain (the very copying that powers
  Lawvere in [`RelExist.Mirror`](Mirror.lean), and that the quantum fragment lacks).
* `joint_factors` — every joint state is determined by its marginals, so there is no
  irreducible "between." Entanglement (a joint *not* fixed by its marginals) is
  therefore inexpressible here.

The full categorical statement — *a category that is both cartesian and compact closed
is thin (a preorder), so any such functor collapses* — requires the symmetric-monoidal
infrastructure left unbuilt; what is recorded here is the `Type`-level obstruction the
firewall rests on.
-/

namespace RelExist.Firewall

universe u v

/-- **Copying is free in a cartesian domain.** The diagonal exists for every type —
the same `(x, x)` move (`g a a`) that powers Lawvere's diagonal in `Mirror`, and that a
compact-closed (no-cloning) fragment does not admit. -/
def copy {X : Type u} : X → X × X := fun x => (x, x)

/-- **The firewall (cartesian side).** In a product (cartesian) domain a joint state is
determined by its marginals: if two joints agree on both parts, they are equal. So a
joint carries nothing beyond its parts — there is no irreducible "between," hence no
entanglement. A non-factoring (entangled) joint is not expressible here: importing the
compact-closed "co-determination" is ill-typed. -/
theorem joint_factors {X : Type u} {Y : Type v} (p q : X × Y)
    (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  cases p
  cases q
  simp_all

end RelExist.Firewall
