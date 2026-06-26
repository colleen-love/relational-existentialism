/-
# An explicit `TracedSMC` instance for domains — the honest, bounded version

`GraphModel` placed `Pω` in "a traced category" via the `[reading]` that the category of domains is
traced (Hasegawa/Hyland: a cartesian trace *is* a Conway fixed-point operator). Mechanizing *that* — the
**fixpoint trace** on the multi-object category of cpos, with the full JSV axioms — is the
Conway/Bekić identities, a genuinely hard multi-turn undertaking, and (by `ReflexiveModel`'s duality)
the *construction* side, orthogonal to the theory. It is **not** done here.

What *is* done here is the bounded honest instance: the **simplest domains — complete lattices — form a
traced SMC**, via their join-monoid `(⊔, ⊥)`. `domainTracedSMC` instantiates `Traced.scalarTracedSMC`
(a commutative monoid is a one-object traced SMC) at the join, which is commutative, associative, and
unital with `⊥`. So a complete lattice is a `TracedSMC`, validating the typeclass for a domain-flavoured
model.

**Be precise about the limitation.** The trace here is the **scalar (identity) trace** — `scalarTracedSMC`
has one object and `trace = id`. It is *not* the Hasegawa **fixpoint** trace, which needs the
multi-object category whose morphisms are continuous functions (so a fixpoint can be taken). So this
instance says "complete lattices are traced SMCs," **not** "the category of domains is traced via
feedback." The latter — the interesting one — remains the open Conway-identities work flagged in
`GraphModel`. This file does not overclaim it.
-/
import RelExist.Traced
import Mathlib.Order.CompleteLattice

namespace RelExist.DomainTraced

open RelExist.Traced

/-- **The simplest domains as a traced SMC.** A complete lattice `L` is a one-object traced SMC via its
join-monoid `(⊔, ⊥)`: morphisms are lattice elements, composition and tensor are `⊔`, the unit is `⊥`,
and the trace is the (scalar) identity. The JSV axioms are validated through `scalarTracedSMC` — in
particular sliding holds because `⊔` is commutative.

*Honest scope:* this is the **scalar/identity** trace, not the Hasegawa **fixpoint** trace (which needs
the multi-object category of continuous maps; see the module docstring). -/
def domainTracedSMC (L : Type*) [CompleteLattice L] : TracedSMC :=
  scalarTracedSMC L (· ⊔ ·) ⊥
    (fun a b c => sup_assoc a b c)
    (fun a => bot_sup_eq a)
    (fun a => sup_bot_eq a)
    (fun a b => sup_comm a b)

end RelExist.DomainTraced
