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

**Honest scope.** This closes the **snake equations** for the canonical compact-closed model concretely
(`sorry`-free, `aesop`). The fully *abstract* `Int(C)` composition-via-trace for an arbitrary non-strict
`C`, and the linear *reflexive object* inside it, remain the named research-grade remainder
([`IntConstruction`](IntConstruction.lean)).
-/
import Aesop
import Scratch.Rel
import Scratch.Compact

namespace RelExist.RelCompact

open RelExist.RelModel

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

end RelExist.RelCompact
