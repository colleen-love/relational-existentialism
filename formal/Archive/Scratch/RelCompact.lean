/-
# `Rel` is compact closed — the snake equations, concretely

The `Int`-construction bridge ([04 §4.6](../../docs/spec/04-functorial-semantics.md),
[`IntConstruction`](IntConstruction.lean)) wanted the **compact-closed axioms — the snake / triangle
(zigzag) equations** — discharged. Over an *abstract* non-strict traced SMC that is the full
Joyal–Street–Verity / Abramsky–Haghverdi–Scott theorem (a long structural-iso chase). Here we close it
**concretely**, in the canonical model: **`Rel` (sets and relations) is compact closed**, and its snake
equations hold on the nose.

`Rel` is **self-dual** — `Aᵈ = A` — with the diagonal as the cup and the cap:

* `cup A : I → A ⊗ A`, relating `∗` to the diagonal `(a, a)`;
* `cap A : A ⊗ A → I`, relating `(a, a)` to `∗`.

The two **zigzag / snake equations** — bend a wire down and back up, or up and back down, and it is the
straight wire — are proved equal to the identity (`rel_snake_right`, `rel_snake_left`), threading the
non-strict associators and unitors and discharged by `aesop` exactly as `Rel`'s seven JSV trace axioms
are in [`Rel`](Rel.lean). We also instantiate the repo's minimal
[`Compact.CompactClosed`](Compact.lean) (the *name* bijection `(A ⟶ B) ≃ (A ⊗ Bᵈ ⟶ I)`) for `Rel`
(`relCompactClosed`), so `Rel` is compact closed in the firewall sense *and* the full zigzag sense.

We also close **composition via the trace** here: the GoI composition `relIntComp` (an `∃` over the
shared `B`-loop) makes `Int(Rel)` a genuine **category** — identity and associativity laws verified.

**Honest scope.** This closes the **snake equations and the trace-composition** for the canonical
compact-closed model concretely (`sorry`-free, `aesop`). The fully *abstract* `Int(C)`
composition-via-trace for an arbitrary non-strict `C`, and the linear *reflexive object* inside it,
remain the named research-grade remainder ([`IntConstruction`](IntConstruction.lean)).
-/
import Aesop
import Scratch.Rel
import Scratch.Compact
import Scratch.IntConstruction

namespace RelExist.RelCompact

open RelExist.RelModel RelExist.Traced

universe u

variable (A : Type u)

/-- **The cup** `η_A : I → A ⊗ A` — relate `∗` to the diagonal `(a, a)`. -/
def cup : Rel PUnit (A × A) := fun _ p => p.1 = p.2

/-- **The cap** `ε_A : A ⊗ A → I` — relate the diagonal `(a, a)` to `∗`. -/
def cap : Rel (A × A) PUnit := fun p _ => p.1 = p.2

/-- **The right zigzag** `A ≅ A⊗I →[id⊗η] A⊗(A⊗A) ≅ (A⊗A)⊗A →[ε⊗id] I⊗A ≅ A`. -/
def zigR : Rel A A :=
  rcomp (rruInv A)
    (rcomp (rtensH (rid A) (cup A))
      (rcomp (raInv A A A)
        (rcomp (rtensH (cap A) (rid A)) (rluHom A))))

/-- **The left zigzag** `A ≅ I⊗A →[η⊗id] (A⊗A)⊗A ≅ A⊗(A⊗A) →[id⊗ε] A⊗I ≅ A`. -/
def zigL : Rel A A :=
  rcomp (rluInv A)
    (rcomp (rtensH (cup A) (rid A))
      (rcomp (raHom A A A)
        (rcomp (rtensH (rid A) (cap A)) (rruHom A))))

/-- **Snake equation (right zigzag) = identity.** Bending the wire down via the cup and back up via the
cap is the straight wire — the defining triangle identity of a compact-closed dual. -/
theorem rel_snake_right : zigR A = rid A := by
  funext a c
  simp only [zigR, rcomp, rtensH, rruInv, rluHom, raInv, rid, cup, cap]
  aesop

/-- **Snake equation (left zigzag) = identity** — the mirror triangle identity. -/
theorem rel_snake_left : zigL A = rid A := by
  funext a c
  simp only [zigL, rcomp, rtensH, rluInv, rruHom, raHom, rid, cup, cap]
  aesop

/-- **The compact-closure *name* bijection** for `Rel`: a relation `A ⟶ B` *is* a state of `A ⊗ Bᵈ`
(here `A × B`, since `Rel` is self-dual), `R ↦ (R as a subset of A × B)`. -/
def relName (A B : Type u) : Rel A B ≃ Rel (A × B) PUnit where
  toFun R := fun p _ => R p.1 p.2
  invFun R' := fun a b => R' (a, b) PUnit.unit
  left_inv _ := by funext a b; rfl
  right_inv _ := by funext p u; rfl

/-- **`Rel` is compact closed** (in the repo's minimal, firewall sense): self-dual, with the defining
name bijection. Together with `rel_snake_{right,left}` this is the full concrete compact-closed
structure — the arena the `Int` construction abstracts. -/
def relCompactClosed : Compact.CompactClosed.{u+1, u} where
  Obj := Type u
  Hom := Rel
  tensor := fun X Y => X × Y
  unit := PUnit
  dual := fun X => X
  name := relName

/-! ### The GoI composition in `Int(Rel)` — composition via the trace, concretely

The `Int`-construction bridge also wanted **composition via the trace**. In the canonical model it is
the Geometry-of-Interaction "execution" formula made literal: trace out the shared `B`-loop with an
existential. We verify it forms a **category** — identity and associativity laws — by `aesop`. -/

open RelExist.IntConstruction

/-- **The GoI composition** `g ∘ f` in `Int(Rel)`: feed `f`'s `B⁺` output into `g`'s `B⁺` input and
`g`'s `B⁻` output into `f`'s `B⁻` input, tracing the shared `B`-loop `∃ b⁺ b⁻`. This *is* the trace
over `B⁺ ⊗ B⁻` of the rewired `f, g`, written out as a relation. -/
def relIntComp {X Y Z : IntObj relTracedSMC}
    (f : IntHom relTracedSMC X Y) (g : IntHom relTracedSMC Y Z) :
    IntHom relTracedSMC X Z :=
  fun p q => ∃ b1 b2, f (p.1, b2) (b1, q.2) ∧ g (b1, p.2) (q.1, b2)

/-- **Left identity law** — `IntId ∘ f = f`. -/
theorem relIntComp_id_left {X Y : IntObj relTracedSMC} (f : IntHom relTracedSMC X Y) :
    relIntComp (IntId relTracedSMC X) f = f := by
  funext p q
  simp only [relIntComp, IntId, relTracedSMC, rid]
  aesop

/-- **Right identity law** — `f ∘ IntId = f`. -/
theorem relIntComp_id_right {X Y : IntObj relTracedSMC} (f : IntHom relTracedSMC X Y) :
    relIntComp f (IntId relTracedSMC Y) = f := by
  funext p q
  simp only [relIntComp, IntId, relTracedSMC, rid]
  aesop

/-- **Associativity** — `(h ∘ g) ∘ f = h ∘ (g ∘ f)`: the two ways of tracing the two loops agree. So
`Int(Rel)` is a genuine category under the GoI trace composition. -/
theorem relIntComp_assoc {W X Y Z : IntObj relTracedSMC}
    (f : IntHom relTracedSMC W X) (g : IntHom relTracedSMC X Y) (h : IntHom relTracedSMC Y Z) :
    relIntComp (relIntComp f g) h = relIntComp f (relIntComp g h) := by
  funext p q
  simp only [relIntComp]
  apply propext
  constructor
  · rintro ⟨b1, b2, ⟨c1, c2, hf, hg⟩, hh⟩; exact ⟨c1, c2, hf, b1, b2, hg, hh⟩
  · rintro ⟨c1, c2, hf, b1, b2, hg, hh⟩; exact ⟨b1, b2, ⟨c1, c2, hf, hg⟩, hh⟩

end RelExist.RelCompact
