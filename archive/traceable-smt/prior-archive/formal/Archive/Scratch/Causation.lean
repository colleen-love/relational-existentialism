/-
# Mechanizing a causality reading: the missing cause is the other you can't see

The theory's strongest causal claim — *local indeterminism is relational causation behind the seam* —
was stated as a `[reading]` on top of [`Marginal`](Marginal.lean) (a deterministic whole has a
nondeterministic marginal). Its formal core *can* be made a theorem, and that is what this file does.

The content: the marginal's branching is not acausality. Decompose your possible nexts by the other's
hidden state. Each **other-conditioned** step `condStep J b` — your successor *given* the other is in
state `b` — is **deterministic** (`condStep_deterministic`); and the marginal is exactly the
existential over the other of these deterministic fibers (`marginalStep_iff_exists_cond`). So:

> the only source of local indeterminism is the quantification over the other you cannot view —
> **condition on the other (view it) and causation is single-valued.** *The cause is present, behind the
> seam.*

With `Marginal.marginal_nondeterministic_iff_entangled` (the marginal branches iff the coupling is
entangling — iff the other *matters*), the causal picture is complete and proved: **your local openness
is exactly your ignorance of the other you are coupled to.**

**What this mechanizes, and what stays a reading.** Mechanized: the conditional-determinism core — the
indeterminism *is* the un-viewed other, deterministic once conditioned — **and** the structural core of
"knowing decoheres" (`knowing_decoheres`, below). Already proved elsewhere: self-causation as a fixed
point (`Biology.closed_to_efficient_causation`), separable-vs-relational
(`Marginal.marginal_deterministic_iff_disentangled`). Still irreducibly a `[reading]`: *calling* the
structure "causation," and the *phenomenal* identifications (felt knowing — the hard problem), which are
not specific to this. This is the deterministic-whole case (the conservation/Everettian framing); the
robust relational-whole case is `RelationalMarginal`.
-/
import Scratch.Marginal

namespace RelExist.Causation

open RelExist.Identity RelExist.Marginal

universe u v
variable {A : Type u} {B : Type v}

/-- The **other-conditioned step**: your successor *given* that the other is in state `b`. -/
def condStep (J : A × B → A × B) (b : B) (a a' : A) : Prop := (J (a, b)).1 = a'

/-- **Conditioning on the other restores determinism.** For each fixed state `b` of the other, your
step is single-valued — the relational cause, once viewed, is deterministic. -/
theorem condStep_deterministic (J : A × B → A × B) (b : B) : Deterministic (condStep J b) := by
  intro x y z hy hz
  exact hy.symm.trans hz

/-- **The marginal indeterminism is exactly the un-viewed other.** Your possible nexts are the
existential, over the other's hidden state, of the (deterministic) conditioned steps. The only source
of local indeterminism is the quantification over the other you cannot see. -/
theorem marginalStep_iff_exists_cond (J : A × B → A × B) (a a' : A) :
    marginalStep J a a' ↔ ∃ b, condStep J b a a' := Iff.rfl

/-- **Indeterminism is causation behind the seam.** The marginal step is the union over the other's
hidden states of conditioned steps, each deterministic. So local openness is not acausality — it is
exactly the quantification over the unviewed other; the cause is present, and viewing the other
(conditioning) restores determinism. *The missing cause is the other.* -/
theorem indeterminism_is_unviewed_cause (J : A × B → A × B) :
    (∀ a a', marginalStep J a a' ↔ ∃ b, condStep J b a a') ∧
      (∀ b, Deterministic (condStep J b)) :=
  ⟨fun a a' => marginalStep_iff_exists_cond J a a', condStep_deterministic J⟩

/-! ### Knowing decoheres — the structural core (correcting an over-classification)

"Knowing = decoherence" is *not* irreducibly a reading: its structural core is provable via the trace.
The doctrine's "knowing" is the **objectifying σ-move = the trace** (to know a subsystem is to hold its
complete account, i.e. trace it out), and the trace **collapses** the relational structure. Concretely:
not knowing the other, your marginal is open — nondeterministic iff the coupling is entangling, a
"superposition" of the branches the other could induce
(`Marginal.marginal_nondeterministic_iff_entangled`); knowing it (conditioning, `condStep`) is
**deterministic** — a definite trajectory. So **knowing the other decoheres your dynamics**: open when
unknown, collapsed when known. -/

/-- **Knowing decoheres.** For an entangling whole, the marginal is open (unknown ⇒ nondeterministic)
while every conditioned step is deterministic (known ⇒ definite). The act of knowing the other — the
objectifying trace — collapses the relational openness. (This is the classical/marginal face; the
literal quantum face is `Conservation.decoherence_is_partial_trace` — tracing out the environment is the
classical reduction. Both are the *same trace operation* collapsing the relational structure. Only
*phenomenal* knowing — the felt act — stays a `[reading]`, the hard-problem residue.) -/
theorem knowing_decoheres {J : A × B → A × B} (hJ : Entangled J) :
    ¬ Deterministic (marginalStep J) ∧ ∀ b, Deterministic (condStep J b) :=
  ⟨(marginal_nondeterministic_iff_entangled J).2 hJ, condStep_deterministic J⟩

end RelExist.Causation
