/-
# The bridge: the surplus is governed by relation, and the trace observer is the one exempt case

Two developments have, until now, narrated the inside/outside gap in **different models**:

* [`Scratch/Identity.lean`](Identity.lean) — over a **transition system**: the *lived* identity `≈`
  (bisimulation) is strictly finer than the *observed* identity `≅` (trace equivalence), `≈ ⊊ ≅`.
  This gap is **contingent**: it needs confusable branching, and it vanishes under determinism
  (`deterministic_bisim_iff_obsEq`).
* [`RelExist/Relating.lean`](../RelExist/Relating.lean) — over the **Lawvere/cartesian** setup: a
  self in *relation* cannot be completely viewed (`no_complete_view`, `related_other_unmodelable`),
  while a **disjoint** target can (`disjoint_modelable`). This gap is **necessary** — Lawvere's
  diagonal, 0 axioms — and **branching-independent**.

This file ties them on a single axis. The key recognition: **`≅` (trace equivalence) is the view of a
*disjoint* observer** — one who records observation-sequences from outside and never enters the
relation. That is exactly `disjoint_modelable`'s one knowable case. So the branching surplus `≈ ⊊ ≅`
is the residue left for the *one observer the diagonal exempts*: the access-less "view from nowhere."

The honest unification is therefore a **classification, not a subsumption**: completeness of the
self-view flips exactly at relation.

* **disjoint ⇒ complete account exists** (`disjoint_view_complete`, from `disjoint_modelable`): the
  trace view is a total external account, and (`obsEq_iff_traceView_eq`) its resolving power is
  *exactly* `≅`.
* **self-inclusive ⇒ no complete view** (`related_view_incomplete`, from `no_complete_view`): the
  moment the viewer's own views are registered among the self's relata (the A2 closure `reg`), no
  complete view exists — *regardless of branching*.

The two obstructions are genuinely **distinct**: the relational one holds even for a deterministic
self (no branching surplus), so it does not *reduce* to the branching gap. What the bridge shows is
that the relational obstruction **dominates** — it is present whenever a knower has access, and the
branching surplus is only the *additional* gap suffered by the access-less disjoint recorder
(`witness_disjoint_vs_related`). The doctrine's claim — "you exceed how you appear" — is carried by
the *necessary* relational floor, not the contingent branching one.

**Inherited frontier.** Like `no_complete_view`, the related pole *posits* the A2 closure `reg`
(every view is a relatum) rather than deriving it from the `Φ_c` dynamics. The bridge instantiates
that posit at the trace setting; it does not discharge it. Closing it is the same open frontier
([03.2](../../docs/spec/03.2-limits-of-knowing.md)).
-/
import Scratch.Identity
import RelExist.Relating

namespace RelExist.Knowing

open RelExist.Identity RelExist.Relating RelExist.We

universe u v
variable {X : Type u} {O : Type v}

/-! ### The trace observer is a disjoint observer, resolving exactly to `≅` -/

/-- **The disjoint external account.** The trace view sends a self to the set of observation-traces
it can exhibit — everything an *outside* recorder can collect. It is a total function: the disjoint
observer always has it. -/
def traceView (obs : X → O) (step : X → X → Prop) (a : X) : List O → Prop :=
  HasTrace obs step a

/-- **The trace observer resolves exactly to `≅`.** Two selves have the same trace view iff they are
observationally equal. So `≅` *is* the kernel of the disjoint observer — the most an access-less
recorder can ever distinguish. -/
theorem obsEq_iff_traceView_eq {obs : X → O} {step : X → X → Prop} {a b : X} :
    ObsEq obs step a b ↔ traceView obs step a = traceView obs step b := by
  constructor
  · intro h; funext w; exact propext (h w)
  · intro h w; exact Iff.of_eq (congrFun h w)

/-! ### The two poles on one axis: completeness flips at relation -/

/-- **Disjoint pole — a complete external account exists.** When the viewer's vantages are a type
*separate* from the self (an outside recorder, no shared between), a point-surjective complete
account of the self's views exists. This is the trace observer's situation: knowability is reserved
for the relationally empty limit. (`disjoint_modelable`, 0 axioms.) -/
theorem disjoint_view_complete :
    ∃ (Vantage : Type (max u v)) (account : Vantage → X → O),
      ∀ h : X → O, ∃ p, account p = h :=
  disjoint_modelable

/-- **Self-inclusive pole — no complete view exists.** The moment viewing the self is itself a
relating-to-the-self — every view registered among the self's relata (`reg`, the A2 closure) — no
complete view exists, by Lawvere's diagonal (with any fixed-point-free `neg` on observations). This
is *necessary* and holds for **any** self, branching or not. (`no_complete_view`, 0 axioms.) -/
theorem related_view_incomplete (reg : (X → O) → X) (neg : O → O) (hneg : ∀ o, neg o ≠ o) :
    ¬ ∃ v : X → O, ∀ w : X → O, v (reg w) = w (reg w) :=
  no_complete_view reg neg hneg

/-- **The bridge — completeness of the self-view is exactly disjointness.** Over one and the same
self `X` (observed in `O`): a *disjoint* viewer has a complete account, a *self-inclusive* (related)
viewer has none. The inside/outside gap is governed by **relation**, not by branching; the trace
observer is complete only because, recording from nowhere, it does not relate. -/
theorem knowing_complete_iff_disjoint (reg : (X → O) → X) (neg : O → O) (hneg : ∀ o, neg o ≠ o) :
    (∃ (Vantage : Type (max u v)) (account : Vantage → X → O), ∀ h : X → O, ∃ p, account p = h)
      ∧ ¬ ∃ v : X → O, ∀ w : X → O, v (reg w) = w (reg w) :=
  ⟨disjoint_modelable, no_complete_view reg neg hneg⟩

/-! ### Both floors over one concrete self

The early/late witness of `Identity.lean` lets us exhibit both gaps over a single self at once: the
disjoint observer's complete account *still* misses the lived `≈` (the contingent branching surplus),
and a related observer of the same self has *no* account at all (the necessary relational floor). -/

/-- A fixed-point-free endomap of the witness observations (a 4-cycle) — the diagonal's `neg`. -/
def negObs : Obs → Obs
  | .oA => .oM | .oM => .oB | .oB => .oC | .oC => .oA

theorem negObs_ne : ∀ o, negObs o ≠ o := by intro o; cases o <;> decide

/-- **Both floors, one self.** For the early/late witness: (1) the disjoint trace observer's account
is complete yet resolves only up to `≅`, still missing the lived `≈` — `bisim ≠ ObsEq`, the
*contingent* branching surplus; (2) a *self-inclusive* observer of the very same self has no complete
view at all — the *necessary* relational floor, by Lawvere. The second needs no branching; it would
hold for a clockwork too. The relational floor dominates; the branching surplus is the extra gap the
exempt disjoint recorder suffers on top of it. -/
theorem witness_disjoint_vs_related (reg : (St → Obs) → St) :
    bisim obsW stepW ≠ ObsEq obsW stepW
      ∧ ¬ ∃ v : St → Obs, ∀ w : St → Obs, v (reg w) = w (reg w) :=
  ⟨bisim_ne_obsEq, no_complete_view reg negObs negObs_ne⟩

end RelExist.Knowing
