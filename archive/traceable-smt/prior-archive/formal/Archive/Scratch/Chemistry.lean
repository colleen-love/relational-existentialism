/-
# The chemistry functor — Layer 4, first domain

The plan's **best non-quantum fit**: a reaction network model, in which an
**autocatalytic set is a fixed point** of a production operator — i.e. an *eigenform*,
exactly the `ν`/`gfp` structure of the theory. So the functor `Cl(𝕋) → 𝒟_chem` reuses
the very machinery built for `≈` and attention.

* `produces` / `prodOp` — given the molecules present, what the network can make (a
  monotone operator on the lattice of molecule-sets).
* `autocatalyticCore := ν(prodOp)` — the maximal **self-sustaining** set: closed under
  its own production (`autocatalyticCore_selfSustaining`) and greatest such
  (`autocatalytic_greatest`, coinduction).
* `selfTrace_eq_autocatalyticCore` — **the functor, witnessed**: the theory's
  self-trace (D1, `νP`) of the production operator *is* the autocatalytic core. "A
  looped self" maps to "a self-sustaining autocatalytic set," definitionally.
-/
import Mathlib.Data.Set.Lattice
import Scratch.Trace

namespace RelExist.Chemistry

variable {M : Type*}

/-- A reaction network on molecules `M`: each reaction needs a set of molecules
(reactants + catalyst) and yields a product. -/
structure ReactionSystem (M : Type*) where
  Reaction : Type*
  needs : Reaction → Set M
  product : Reaction → M

/-- Given the molecules in `X`, the molecules the network can produce: products of
reactions whose needs are all met within `X`. -/
def produces (R : ReactionSystem M) (X : Set M) : Set M :=
  { m | ∃ r : R.Reaction, R.product r = m ∧ R.needs r ⊆ X }

/-- Production is monotone: more available molecules can only enable more reactions. -/
def prodOp (R : ReactionSystem M) : Set M →o Set M where
  toFun := produces R
  monotone' := by
    intro X Y hXY m hm
    simp only [produces, Set.mem_setOf_eq] at hm ⊢
    obtain ⟨r, hr, hsub⟩ := hm
    exact ⟨r, hr, hsub.trans hXY⟩

/-- **The autocatalytic core** `ν(prodOp)`: the maximal self-sustaining set of
molecules — the chemistry domain's eigenform. -/
def autocatalyticCore (R : ReactionSystem M) : Set M := (prodOp R).gfp

/-- The core is **self-sustaining**: it reproduces exactly itself. -/
theorem autocatalyticCore_selfSustaining (R : ReactionSystem M) :
    produces R (autocatalyticCore R) = autocatalyticCore R :=
  (prodOp R).map_gfp

/-- **Maximality / coinduction.** Any self-sustaining set (`X ⊆ produces R X`) lies
within the autocatalytic core. -/
theorem autocatalytic_greatest (R : ReactionSystem M) {X : Set M}
    (h : X ⊆ produces R X) : X ⊆ autocatalyticCore R :=
  (prodOp R).le_gfp h

/-- **The functor `Cl(𝕋) → 𝒟_chem`, witnessed.** The theory's self-trace (`νP`, axiom
D1 / [`Scratch.Trace`](Trace.lean)) of the production operator *is* the autocatalytic
core: a looped self maps to a self-sustaining autocatalytic set, definitionally. This
is the near-literal fit the plan claimed, as a one-line theorem. -/
theorem selfTrace_eq_autocatalyticCore (R : ReactionSystem M) :
    RelExist.Trace.selfTrace (prodOp R) = autocatalyticCore R := rfl

end RelExist.Chemistry
