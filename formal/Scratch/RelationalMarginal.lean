/-
# Relation manufactures openness whatever the global law — robust, with conservation as a corollary

[`Marginal.lean`](Marginal.lean) proved that a **deterministic** whole, coupled across a between,
marginalizes to a nondeterministic self — and read the indeterminism as conserved determinism
relocated into the between (the decoherence rhyme). That rhyme is gorgeous but it *costs* a
metaphysical bet: the whole must be a clockwork. This module shows the bet is **optional**, by proving
the load-bearing claim over an *arbitrary* global law and recovering the deterministic case as a
labelled corollary. The two are not alternatives; they **nest**.

* `jointRel`, `marginalRel`, `EntangledRel` — the whole as **any relation** `J : (A×B) → (A×B) → Prop`
  (deterministic or not), its marginal (the other forgotten), and entanglement (the self's successor
  depends on the other's hidden state).
* `entangledRel_imp_marginal_nondeterministic` — **the robust theorem** `[0 axioms]`: an entangling
  whole has a nondeterministic marginal, *whatever the global law*. Relation manufactures local
  openness independent of the physics of the whole. This is the *necessary* version.
* `deterministic_whole_marginal_open` — **the conservation corollary**: take the whole to be a
  function (a clockwork) and you recover `Marginal` — the whole is deterministic, the marginal
  branches, the indeterminism is purely relocated. The price of the elegant decoherence rhyme is
  exactly this one hypothesis, named and isolated (`graph`, `jointRel_graph_deterministic`,
  `marginalRel_graph` showing the marginals literally coincide).
* `robust_survives_nondeterministic_whole` — the witness that the robust claim bites where `Marginal`
  cannot: a genuinely **nondeterministic** whole (`Jnd`, not a function) that is *itself* open, yet
  whose marginal is *also* open by entanglement. Relation casts openness even in an open universe.

**The fork, dissolved.** By the discipline that drove every result — *necessity over contingency* —
the robust theorem carries the weight: "relation casts the surplus" holds for any global law, so it is
not hostage to a deterministic-universe bet. The conservation symmetry is kept, correctly priced: it
is the corollary you unlock by granting that the whole is deterministic (the unitary/Everettian
reading of physics, where global evolution is deterministic and the indeterminism is which-branch
perspectival). You get both, ranked correctly. (Note: only the *deterministic whole* yields the sharp
iff `openness ⟺ relation`; for a general whole the marginal can also be open from the whole's own
branching, so entanglement is *sufficient* for openness, not equivalent to it. That asymmetry is
honest and expected.)
-/
import Scratch.Marginal

namespace RelExist.RelationalMarginal

open RelExist.Identity RelExist.Marginal

universe u v
variable {A : Type u} {B : Type v}

/-! ### The whole as any global law -/

/-- The **whole** as an arbitrary relation on the shared state — deterministic or not. -/
def jointRel (J : A × B → A × B → Prop) (p p' : A × B) : Prop := J p p'

/-- The **marginal** of a relational whole: a self-successor `a'` is reachable iff *some* hidden
input/output states of the other carry it there. -/
def marginalRel (J : A × B → A × B → Prop) (a a' : A) : Prop :=
  ∃ b b', J (a, b) (a', b')

/-- **Entanglement**, robustly: from one state `a`, two hidden states of the other lead the self to
*different* successors. The shared wire genuinely matters. -/
def EntangledRel (J : A × B → A × B → Prop) : Prop :=
  ∃ a b b' a₁ c₁ a₂ c₂, J (a, b) (a₁, c₁) ∧ J (a, b') (a₂, c₂) ∧ a₁ ≠ a₂

/-! ### The robust theorem: openness from relation, whatever the global law -/

/-- **Relation manufactures openness — for any global law.** An entangling whole has a
nondeterministic marginal whether or not the whole is deterministic. The branch in the self's
dynamics is the other's hidden degree of freedom, period; nothing about the physics of the whole is
assumed. This is the *necessary* form of the `Marginal` result. -/
theorem entangledRel_imp_marginal_nondeterministic (J : A × B → A × B → Prop)
    (h : EntangledRel J) : ¬ Deterministic (marginalRel J) := by
  obtain ⟨a, b, b', a₁, c₁, a₂, c₂, h1, h2, hne⟩ := h
  intro hdet
  exact hne (hdet ⟨b, c₁, h1⟩ ⟨b', c₂, h2⟩)

/-! ### The deterministic whole nests inside, as the conservation corollary -/

/-- The deterministic whole, as a relational whole: the **graph** of a step function (a clockwork). -/
def graph (f : A × B → A × B) : A × B → A × B → Prop := fun p q => f p = q

/-- A graph-whole is deterministic — the clockwork of `Marginal`. -/
theorem jointRel_graph_deterministic (f : A × B → A × B) :
    Deterministic (jointRel (graph f)) := by
  intro x y z hxy hxz
  simp only [jointRel, graph] at hxy hxz
  exact hxy.symm.trans hxz

/-- The marginals **literally coincide**: the relational marginal of a graph-whole is `Marginal`'s
marginal of the function. The elegant case is the special case. -/
theorem marginalRel_graph (f : A × B → A × B) (a a' : A) :
    marginalRel (graph f) a a' ↔ marginalStep f a a' := by
  constructor
  · rintro ⟨b, b', hb⟩
    exact ⟨b, by rw [show f (a, b) = (a', b') from hb]⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (f (a, b)).2, Prod.ext_iff.mpr ⟨hb, rfl⟩⟩

/-- An entangling function is an entangling whole. -/
theorem entangledRel_graph_of_entangled (f : A × B → A × B) (h : Entangled f) :
    EntangledRel (graph f) := by
  obtain ⟨a, b, b', hne⟩ := h
  exact ⟨a, b, b', (f (a, b)).1, (f (a, b)).2, (f (a, b')).1, (f (a, b')).2,
    Prod.ext_iff.mpr ⟨rfl, rfl⟩, Prod.ext_iff.mpr ⟨rfl, rfl⟩, hne⟩

/-- **The conservation corollary (the deterministic whole).** Granting that the global law is a
function — a clockwork — recovers `Marginal` exactly: the whole is deterministic, yet the marginal
branches. This is the elegant, decoherence-rhyming case; its sole price is this one hypothesis. -/
theorem deterministic_whole_marginal_open (f : A × B → A × B) (h : Entangled f) :
    Deterministic (jointRel (graph f)) ∧ ¬ Deterministic (marginalRel (graph f)) :=
  ⟨jointRel_graph_deterministic f,
   entangledRel_imp_marginal_nondeterministic (graph f) (entangledRel_graph_of_entangled f h)⟩

/-! ### Robustness witness: openness survives an open universe -/

/-- A genuinely **nondeterministic** whole on `Bool × Bool`: the self's next bit is `a ⊕ b`, but the
other's next bit is *free* — so the whole itself branches. (Not the graph of any function.) -/
def Jnd : Bool × Bool → Bool × Bool → Prop := fun p q => q.1 = Bool.xor p.1 p.2

/-- `Jnd` is entangling: the self's successor turns on the other's hidden bit. -/
theorem Jnd_entangled : EntangledRel Jnd :=
  ⟨false, false, true, false, false, true, false,
    by unfold Jnd; decide, by unfold Jnd; decide, by decide⟩

/-- `Jnd` is a genuinely **open** global law — the whole itself is nondeterministic (the other's next
bit is unconstrained). -/
theorem Jnd_whole_nondeterministic : ¬ Deterministic (jointRel Jnd) := by
  intro hdet
  have h1 : jointRel Jnd (false, false) (false, false) := by unfold jointRel Jnd; decide
  have h2 : jointRel Jnd (false, false) (false, true) := by unfold jointRel Jnd; decide
  have : ((false, false) : Bool × Bool) = (false, true) := hdet h1 h2
  exact absurd this (by decide)

/-- **The robust claim bites where `Marginal` cannot.** A whole that is *itself* open (nondeterministic
global law) **and** whose marginal is open by entanglement: relation manufactures local openness even
when the universe is not a clockwork. This is the case the conservation framing cannot reach and the
robust theorem covers. -/
theorem robust_survives_nondeterministic_whole :
    ¬ Deterministic (jointRel Jnd) ∧ ¬ Deterministic (marginalRel Jnd) :=
  ⟨Jnd_whole_nondeterministic,
   entangledRel_imp_marginal_nondeterministic Jnd Jnd_entangled⟩

end RelExist.RelationalMarginal
