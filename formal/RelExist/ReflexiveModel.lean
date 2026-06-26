/-
# Constructing a reflexive object — and the duality that resolves route 1

[`ReflexiveSeam`](ReflexiveSeam.lean) left route 1 needing an actual reflexive object. Constructing one
is illuminating, because it exposes a duality that *dissolves* the route-1 goal rather than completing
it.

**A reflexive object exists — the trivial one.** `Unit` is reflexive: `appU : Unit → (Unit → Unit)` is
point-surjective (`unit_isReflexive`), so the machinery of `ReflexiveSeam` runs on a *concrete* object
(`unit_fixpoint`). Route 1's precondition is satisfiable, not vacuous.

**But it is the *only* finite one, and the duality is the reason.** Lawvere
(`reflexive_gives_fixpoint`) says a reflexive object for observables in `B` **forces every `B`-observable
to settle** (have a fixed point). Contrapositive (`ReflexiveSeam.no_reflexive_self_trace`): a
*settling-refusing* observable — a `neg` with no fixed point — makes a reflexive object **impossible**.
So on any given `B`:

> reflexive object **xor** settling-refusing observable — never both.

`Unit` is reflexive (every `Unit`-observable settles, trivially); `Bool` is **not** reflexive
(`no_reflexive_object_for_Bool` — `not` never settles, Cantor). The two examples are the two horns.

**Why this resolves route 1.** Route 1 wanted "the Lawvere diagonal *obstructing* the actual trace." But
the diagonal *on* a reflexive object is the **construction** — it builds a fixed point, GoI's `Y`
(`fixpoint_is_selfApplication`), not an obstruction. The **obstruction** (the seam) is exactly the
*non-existence* of a reflexive observation into a settling-refusing `B` — which is already a theorem
(`no_reflexive_self_trace`, Cantor/Lawvere, `0` axioms). These are two halves of one contrapositive and
cannot coexist on one `B`. So "construct a reflexive object so the diagonal obstructs the trace" is
self-undermining: the obstruction *is* the reflexive object's absence. The obstruction side of route 1
was already done; there is no reflexive object that makes Lawvere obstruct, because obstruction = no
reflexive object.

**What a non-trivial reflexive object would (and wouldn't) add.** A *non-trivial* reflexive object —
necessarily infinite (`|D| = |D→D|` fails finitely for `|D| ≥ 2`): Scott's `D∞`, the graph model `Pω`,
a domain `D ≅ [D→D]` of *continuous* maps — would make the **trace concrete**: a real infinite feedback
domain on which GoI's `Y` literally runs (the *construction* side). It would **not** change the
obstruction, which is settled. Building `D∞`/`Pω` is a substantial domain-theoretic formalization
(inverse limits / Scott continuity / the retraction) that mathlib does not support and that is **not done
here** — and, by the duality, it would realize the Y-combinator in a real model, not the seam. So the
honest end of route 1: the *obstruction* is proved (it is the non-existence); the *construction* in a
genuine traced domain is real, large, separate work that does not bear on the seam.
-/
import RelExist.ReflexiveSeam

namespace RelExist.ReflexiveModel

open RelExist.Mirror RelExist.ReflexiveSeam

universe u v

/-! ### The trivial reflexive object: `Unit` -/

/-- Self-application on `Unit`. -/
def appU : Unit → Unit → Unit := fun _ _ => ()

/-- Its section. -/
def lamU : (Unit → Unit) → Unit := fun _ => ()

theorem hsplitU : ∀ g : Unit → Unit, appU (lamU g) = g :=
  fun _ => funext fun _ => Subsingleton.elim _ _

/-- **`Unit` is a reflexive object.** `appU` is point-surjective — so a reflexive object genuinely
*exists*, and route 1's precondition is satisfiable. -/
theorem unit_isReflexive : ∃ app : Unit → Unit → Unit, PointSurjective app :=
  ⟨appU, fun h => ⟨(), hsplitU h⟩⟩

/-- The `ReflexiveSeam` machinery runs on this concrete object: every `Unit`-observable has a fixed
point (trivially — the construction side, on a real object). -/
theorem unit_fixpoint (f : Unit → Unit) : ∃ b, f b = b :=
  reflexive_gives_fixpoint appU lamU hsplitU f

/-! ### The duality: reflexive existence xor a settling-refusing observable -/

/-- **A reflexive object forces every observable to settle** (= `Mirror.lawvere`). With
`no_reflexive_self_trace` (the contrapositive) this is the whole story: reflexive existence and the seam
are two halves of one contrapositive. -/
theorem reflexive_imp_settles {D : Type u} {B : Type v} (app : D → D → B)
    (hsurj : PointSurjective app) (f : B → B) : ∃ b, f b = b :=
  lawvere app hsurj f

/-- **The two horns, witnessed.** `Unit` *is* reflexive (every observable settles); `Bool` is **not**
(`not` never settles — Cantor). The reflexive object and the seam never coexist on one `B`: the
obstruction side of route 1 *is* the non-existence, already a theorem. -/
theorem reflexive_xor_unsettling :
    (∃ app : Unit → Unit → Unit, PointSurjective app) ∧
      ¬ ∃ app : Bool → Bool → Bool, PointSurjective app :=
  ⟨unit_isReflexive, no_reflexive_object_for_Bool⟩

end RelExist.ReflexiveModel
