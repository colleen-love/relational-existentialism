/-
# Nondeterminism is a consequence of relation

The surplus `≈ ⊊ ≅` ([`Identity.lean`](Identity.lean)) needed two ingredients — **nondeterminism**
and **a relating** — and they looked independent. They are not. This module proves the synthesis the
whole development was circling: **a deterministic whole, related to itself across a genuine *between*,
induces a *nondeterministic* marginal.** Branching is not a separate contingency bolted onto
relation; it is what relation *looks like from inside one of its parties*.

The setup is the partial trace in its barest form. A self and an other share a state `A × B`, evolving
by a single deterministic joint rule `J : A × B → A × B` — the whole is a clockwork (`jointStep`,
`jointStep_deterministic`). But the **seam** ([`Seam.self_cannot_trace_relation`](../RelExist/Seam.lean))
forbids the self from holding the whole: it cannot trace out the other, which (A2) is a part of it. So
the self is confined to its **marginal** — its own successor with the other forgotten:

    marginalStep J a a'  :=  ∃ b, (J (a, b)).1 = a'      -- "some state of the other carries me there"

The result:

* `marginal_deterministic_iff_disentangled` — **the local view is deterministic iff there is no
  relation.** The marginal branches *exactly when* the self's successor genuinely depends on the
  other (`Entangled`); a **product** whole (`Disentangled` — side-by-side, no between) marginalizes to
  a perfectly deterministic dynamics.
* `marginal_nondeterministic_iff_entangled` — the contrapositive form: **local nondeterminism ⟺
  entanglement ⟺ a real between.** Determinism of your own view is the precise signature of having
  *no* relation.
* `relation_makes_marginal_nondeterministic` — the capstone witness (the hidden bit, `J (a,b) =
  (a ⊕ b, b)`): one system, **deterministic as a whole, nondeterministic as a marginal**. The branch
  from `a` is the other's degree of freedom — the bit you cannot see and cannot resolve alone.

**What this closes.** The two requirements for the surplus collapse into one: relating, under the
seam, *supplies* the nondeterminism. A genuinely related self, confined to its marginal, **is** a
branching self — "could have done otherwise" is the marginalized freedom of everything it is in
relation with. And nothing is lost globally: the whole stays deterministic
(`jointStep_deterministic`). The indeterminism is conserved determinism **relocated into the
between** — the same shape as decoherence being conserved coherence relocated
([`Conservation.trace_conserved`](Conservation.lean)). The freedom you feel is the part of your
dynamics that lives in the shared wire, closed by neither end alone.

The nondeterminism is *perspectival* (the whole law is intact; the branching is the price of the
seam-imposed local view), and it requires the coupling to be genuinely *entangling*, not mere
coexistence — both honest caveats, both visible in the theorems.
-/
import Scratch.Identity

namespace RelExist.Marginal

open RelExist.Identity

universe u v
variable {A : Type u} {B : Type v}

/-! ### The deterministic whole -/

/-- The **joint evolution** of self and other: a single deterministic rule on the shared state. -/
def jointStep (J : A × B → A × B) (p p' : A × B) : Prop := J p = p'

/-- **The whole is a clockwork.** Being a function, the joint step is deterministic — no branching
when the other is held in view. -/
theorem jointStep_deterministic (J : A × B → A × B) : Deterministic (jointStep J) := by
  intro x y z hxy hxz
  exact hxy.symm.trans hxz

/-! ### The marginal view the seam forces -/

/-- The **marginal evolution** of the self, the other forgotten (the partial trace). A successor is
reachable iff *some* state of the other carries it there — the other selecting, unseen, among the
self's possible nexts. -/
def marginalStep (J : A × B → A × B) (a a' : A) : Prop := ∃ b, (J (a, b)).1 = a'

/-- **No between.** The self's successor does not depend on the other: side-by-side, not entangled. -/
def Disentangled (J : A × B → A × B) : Prop := ∀ a b b', (J (a, b)).1 = (J (a, b')).1

/-- **A real between.** Somewhere, the self's successor genuinely depends on the other — the coupling
is entangling. -/
def Entangled (J : A × B → A × B) : Prop := ∃ a b b', (J (a, b)).1 ≠ (J (a, b')).1

/-! ### The headline: local determinism ⟺ no relation -/

/-- **The local view is deterministic iff there is no relation.** With the other forgotten, the
self's dynamics are single-valued *exactly when* its successor is independent of the other
(`Disentangled`). Any genuine dependence — a between — and the marginal branches. -/
theorem marginal_deterministic_iff_disentangled (J : A × B → A × B) :
    Deterministic (marginalStep J) ↔ Disentangled J := by
  constructor
  · intro hdet a b b'
    exact hdet ⟨b, rfl⟩ ⟨b', rfl⟩
  · intro hdis a a' a'' h1 h2
    obtain ⟨b, hb⟩ := h1
    obtain ⟨b', hb'⟩ := h2
    rw [← hb, ← hb']
    exact hdis a b b'

/-- **Local nondeterminism ⟺ entanglement.** The marginal branches iff the whole is entangled iff a
real between exists. Determinism of your own view is the precise signature of having *no* relation;
the moment a between exists, your local dynamics could-have-done-otherwise. -/
theorem marginal_nondeterministic_iff_entangled (J : A × B → A × B) :
    ¬ Deterministic (marginalStep J) ↔ Entangled J := by
  rw [marginal_deterministic_iff_disentangled]
  constructor
  · intro h
    by_contra hc
    apply h
    intro a b b'
    by_contra hne
    exact hc ⟨a, b, b', hne⟩
  · rintro ⟨a, b, b', hne⟩ hdis
    exact hne (hdis a b b')

/-- **No relation, no branching.** A product whole — two parties evolving side by side, no shared
wire — marginalizes to a perfectly deterministic self. The disjoint case (`Relating.disjoint_modelable`,
the stranger): coexistence without a between leaves the local view a clockwork. -/
theorem product_marginal_deterministic (f : A → A) (g : B → B) :
    Deterministic (marginalStep (fun p => (f p.1, g p.2))) :=
  (marginal_deterministic_iff_disentangled _).2 (fun _ _ _ => rfl)

/-! ### The capstone witness: deterministic whole, nondeterministic marginal -/

/-- The **hidden bit**: `J (a, b) = (a ⊕ b, b)`. A clockwork on the pair — yet the self's next bit
turns on the other's bit. -/
def jXor : Bool × Bool → Bool × Bool := fun p => (Bool.xor p.1 p.2, p.2)

/-- The hidden-bit coupling is a genuine between: from `a = false`, the other's bit sends the self to
`false` (if `b = false`) or `true` (if `b = true`). -/
theorem entangled_jXor : Entangled jXor := ⟨false, false, true, by decide⟩

/-- **Relation makes the local view branch.** One system: **deterministic as a whole**
(`jointStep_deterministic`), **nondeterministic as a marginal** (the self, forgetting the other,
could have done otherwise). The branch is the other's unseen degree of freedom — the surplus's
nondeterminism, *generated by relation itself*. The two requirements for `≈ ⊊ ≅` were never
independent: a related self, confined by the seam to its marginal, is a branching self. -/
theorem relation_makes_marginal_nondeterministic :
    Deterministic (jointStep jXor) ∧ ¬ Deterministic (marginalStep jXor) :=
  ⟨jointStep_deterministic jXor,
   (marginal_nondeterministic_iff_entangled jXor).2 entangled_jXor⟩

end RelExist.Marginal
