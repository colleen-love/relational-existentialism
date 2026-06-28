/-
# Biology — Rosen's (M,R)-systems and closure to efficient causation (Layer 4, fifth domain)

The plan's biology verdict: **Rosen relational biology / (M,R)-systems**, "strong, with an
ancestor" — Rosen's metabolism–repair systems *predate and anticipate* the doctrine's
looped-self/eigenform idea. An organism is **closed to efficient causation**: it fabricates
all of its own parts, *including its own maintainers* — an impredicative, self-referential
closure. That is exactly a greatest fixed point, the `ν`/`gfp` eigenform of the theory.

Unlike chemistry's single production operator, an (M,R)-system **couples two** operators —
metabolism (what the present components make) and repair (what regenerates the makers) — and
the organism is the fixed point of their composite. So:

* `MRSystem` — a metabolism `metabolize` and a repair `repair`, monotone operators on the
  lattice of component-sets;
* `fabricate := repair ∘ metabolize` — the coupled fabrication operator;
* `organism := ν(fabricate)` — the maximal self-fabricating whole (`organism_closed`,
  `organism_greatest` = coinduction);
* `mr_cycle_closes` — the **metabolism–repair cycle closes** on the organism: it is repaired
  from its own metabolites;
* `closed_to_efficient_causation` — a component the system fabricates *from itself* lies in
  the organism: the efficient cause of its own maintenance is **internal**;
* `selfTrace_eq_organism` — **the functor, witnessed**: the theory's self-trace (`νP`, D1) of
  the fabrication operator *is* the Rosennean organism, definitionally.

The impredicative self-reference ("the repairer is itself repaired") is the same loop the
[mirror](../RelExist/Mirror.lean) makes precise on the σ-side — biology's ancestor of the
doctrine's self-modelling.
-/
import Mathlib.Order.FixedPoints
import Scratch.Trace

namespace RelExist.Biology

variable {Comp : Type*}

/-- A **metabolism–repair system** on components `Comp`: a monotone `metabolize` (what the
present components collectively make) and a monotone `repair` (what regenerates the makers
from the metabolites). Components may *be* the makers — Rosen's impredicativity. -/
structure MRSystem (Comp : Type*) where
  /-- metabolism: the components produced from those present -/
  metabolize : Set Comp →o Set Comp
  /-- repair: the makers regenerated from the metabolites -/
  repair : Set Comp →o Set Comp

/-- The **coupled fabrication operator** `repair ∘ metabolize`: present components are
metabolized, and the metabolites repair the makers. Monotone, so it has a greatest fixed
point. -/
def MRSystem.fabricate (S : MRSystem Comp) : Set Comp →o Set Comp :=
  S.repair.comp S.metabolize

/-- **The organism** `ν(fabricate)`: the maximal self-fabricating set of components — the
biology domain's eigenform, the formal content of *closure to efficient causation*. -/
def organism (S : MRSystem Comp) : Set Comp := S.fabricate.gfp

/-- The organism is **closed**: fabricating it reproduces exactly itself. -/
theorem organism_closed (S : MRSystem Comp) : S.fabricate (organism S) = organism S :=
  S.fabricate.map_gfp

/-- **Maximality / coinduction.** Any self-fabricating set (`X ⊆ fabricate X`) lies within
the organism. To show components persist as a living whole, exhibit such a set. -/
theorem organism_greatest (S : MRSystem Comp) {X : Set Comp}
    (h : X ⊆ S.fabricate X) : X ⊆ organism S :=
  S.fabricate.le_gfp h

/-- **The metabolism–repair cycle closes.** The organism is *repaired from its own
metabolites*: feeding it through metabolism then repair returns the organism. This is the
two-operator heart of an (M,R)-system, holding on the eigenform. -/
theorem mr_cycle_closes (S : MRSystem Comp) :
    S.repair (S.metabolize (organism S)) = organism S :=
  S.fabricate.map_gfp

/-- **Closure to efficient causation.** A component the system fabricates *from itself alone*
belongs to the organism: the efficient cause of its own maintenance is **internal**, needing
no external fabricator — Rosen's defining property, as a one-line consequence of coinduction. -/
theorem closed_to_efficient_causation (S : MRSystem Comp) {c : Comp}
    (h : c ∈ S.fabricate {c}) : c ∈ organism S := by
  have hsub : ({c} : Set Comp) ⊆ organism S := by
    apply organism_greatest
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact h
  exact hsub rfl

/-- **The functor `Cl(𝕋) → 𝒟_bio`, witnessed.** The theory's self-trace (`νP`, definition D1 /
[`Scratch.Trace`](Trace.lean)) of the fabrication operator *is* the Rosennean organism: a
looped self maps to a self-fabricating organism, definitionally. The "strong fit with an
ancestor" the plan claimed, as a one-line theorem. -/
theorem selfTrace_eq_organism (S : MRSystem Comp) :
    RelExist.Trace.selfTrace S.fabricate = organism S := rfl

end RelExist.Biology
