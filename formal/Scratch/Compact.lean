/-
# Compact closure and the firewall collapse — Layer 4, categorical

This closes the gap left in [04 §4.4](../../docs/spec/04-functorial-semantics.md): the
firewall stated as a *categorical theorem*, not just a `Type`-level fact.

We axiomatize the **operative content of compact closure** — the *name* bijection
`(A ⟶ B) ≃ (A ⊗ Bᵈ ⟶ I)` that defines a dual — rather than reconstruct the full traced
symmetric monoidal category (mathlib has symmetric/braided/rigid monoidal categories
and `ChosenFiniteProducts`, but no traced-monoidal or compact-closed typeclass; the
coherence-heavy free traced SMC `Cl(𝕋)` is the remaining infrastructure). From that
minimal structure:

* `collapse` — **the firewall**: a compact-closed structure that *also* has cartesian
  copying (a terminal unit) is **thin** — all parallel morphisms coincide. You cannot
  have entanglement and free copying together without trivialising.
* `no_cloning` — the contrapositive: a non-trivial compact-closed structure admits **no**
  uniform copying. This is no-cloning, categorically — the defining feature of the
  quantum/physics fragment and the reason the social (cartesian) firewall holds.
-/
import Mathlib.Logic.Equiv.Defs

namespace RelExist.Compact

universe u v

/-- A **minimal compact-closed structure**: objects and hom-types with a monoidal
product `⊗`, a unit `I`, a duality `(·)ᵈ` on objects, and the defining *name* bijection
of compact closure, `(A ⟶ B) ≃ (A ⊗ Bᵈ ⟶ I)`. (This is the operative fragment; the full
traced symmetric monoidal coherence is deliberately not reconstructed.) -/
structure CompactClosed where
  Obj : Type u
  Hom : Obj → Obj → Type v
  tensor : Obj → Obj → Obj
  unit : Obj
  dual : Obj → Obj
  /-- compact closure: every morphism has a *name* as a state of `A ⊗ Bᵈ`. -/
  name : ∀ A B, Hom A B ≃ Hom (tensor A (dual B)) unit

variable (C : CompactClosed)

/-- The **cartesian** hypothesis: the unit is (sub)terminal — at most one morphism into
it. This is the structural form of free copying / deletion (`! : X → I`), the hallmark of
the social and mental-health domains. -/
def UnitSubterminal : Prop := ∀ X, Subsingleton (C.Hom X C.unit)

/-- **The firewall, as a categorical theorem (the collapse).** A compact-closed structure
whose unit is (sub)terminal — i.e. that also has cartesian copying — is **thin**: any two
parallel morphisms are equal. So "compact-closed + cartesian" forces triviality; you
cannot host entanglement and free copying in the same domain. -/
theorem collapse (hUnit : UnitSubterminal C) (A B : C.Obj) :
    Subsingleton (C.Hom A B) := by
  have : Subsingleton (C.Hom (C.tensor A (C.dual B)) C.unit) := hUnit _
  exact ⟨fun f g => (C.name A B).injective (Subsingleton.elim _ _)⟩

/-- **No-cloning, categorically.** If a compact-closed structure is non-trivial — it has
two distinct parallel morphisms anywhere — then its unit is **not** subterminal: it
admits no uniform copying/deletion. Entanglement excludes cloning; this is why
"two people are entangled" cannot be imported into a cartesian (social) domain. -/
theorem no_cloning {A B : C.Obj} {f g : C.Hom A B} (hfg : f ≠ g) :
    ¬ UnitSubterminal C := by
  intro hUnit
  have : Subsingleton (C.Hom A B) := collapse C hUnit A B
  exact hfg (Subsingleton.elim f g)

end RelExist.Compact
