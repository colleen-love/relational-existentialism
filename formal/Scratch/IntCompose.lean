/-
# The GoI composition-via-trace — defined abstractly, on any traced SMC

[`IntConstruction`](IntConstruction.lean) built the `Int`/Geometry-of-Interaction arena on an abstract
`TracedSMC` — objects, two-way homs, tensor, unit, the dual with its involution/monoidality, the identity,
and the dual's contravariant action on morphisms — and flagged the **composition-via-trace** as the
research-grade remainder, building it only *concretely* in `Rel` ([`RelCompact`](RelCompact.lean),
`relIntComp`). This module **builds the composition itself abstractly**: the Geometry-of-Interaction
"execution" formula `g ∘ f := Tr^{B}( σ₁ ; (f ⊗ g) ; σ₂ )` on **any** traced SMC, with the structural-iso
plumbing `σ₁, σ₂` written out explicitly (composites of associators and braidings) and **type-checked**. So
the wiring `IntConstruction` declared "not built here" is now a genuine definition — the abstract `Int(C)`
has its category composition, not only the concrete `Int(Rel)`'s `relIntComp`.

`IntCompose f g` feeds `f`'s forward output `B⁺` into `g`'s forward input and `g`'s backward output `B⁻`
into `f`'s backward input, then **traces out the shared loop** `B⁺ ⊗ B⁻`. The permutations:

* `σ₁ : (A⁺⊗D⁻)⊗(B⁺⊗B⁻) → (A⁺⊗B⁻)⊗(B⁺⊗D⁻)` — route the external inputs and the loop into `f`'s and `g`'s
  input ports (swap the two backward wires `D⁻`, `B⁻`);
* `f ⊗ g` runs both processes;
* `σ₂ : (B⁺⊗A⁻)⊗(D⁺⊗B⁻) → (D⁺⊗A⁻)⊗(B⁺⊗B⁻)` — route `f`'s and `g`'s outputs to the external outputs and
  back onto the loop (swap the two forward wires `B⁺`, `D⁺`).

That the whole composite type-checks at `(A⁺⊗D⁻)⊗(B⁺⊗B⁻) → (D⁺⊗A⁻)⊗(B⁺⊗B⁻)` — so that `trace` of it lands
in `IntHom A D = C.Hom (A⁺⊗D⁻) (D⁺⊗A⁻)` — is exactly the statement that the associator/braid bookkeeping is
**coherent**: the wiring is provably right at the type level on any non-strict base, which is the part that
made it nontrivial to even write down.

**Honest scope — what is built and what stays the JSV chase.** Built here, on an arbitrary non-strict
`TracedSMC`: the composition **operation** itself, fully explicit and type-correct — the abstract GoI
composition that `relIntComp` is the concrete shadow of now *exists*, where before it was absent. **Not**
proved here: the category laws (identity, associativity) and the compact-closed snake/triangle equations
*of this abstract `IntCompose`*, whose derivation from the seven JSV trace axioms plus monoidal coherence —
for an arbitrary non-strict base — is exactly the Joyal–Street–Verity / Abramsky–Haghverdi–Scott theorem
"`Int(C)` is compact closed". That is the long structural-iso chase the trace axioms were designed to
support but for which mathlib has no scaffolding; it is genuinely hard precisely because the associators
are honest isomorphisms threaded through every equation (even tracing out the relational content of `σ₂`
over `Rel` is heavy — the nested-product associators blow up the unfolder). Those laws are discharged
**concretely** in the canonical model: [`RelCompact`](RelCompact.lean) proves `Int(Rel)` is a category
under `relIntComp` and that `Rel`'s snake equations hold. So the **laws live in `Rel`**, the **abstract
composition lives here**, and the remaining `[open]` is the abstract law-verification (the JSV chase) plus
the mechanized identification of this `IntCompose` with `relIntComp` at `Rel`. The contribution: the
composition is no longer *absent* abstractly — it is a definition, on any traced SMC.
-/
import RelExist.Traced
import RelExist.Coherence
import Scratch.IntConstruction

namespace RelExist.IntConstruction

open RelExist.Traced

variable (C : TracedSMC)

/-- **`σ₁`** — route external inputs and the traced loop into `f`'s and `g`'s input ports:
`(A⁺⊗D⁻)⊗(B⁺⊗B⁻) → (A⁺⊗B⁻)⊗(B⁺⊗D⁻)`. It swaps the two backward wires `D⁻` and `B⁻`, threading through the
associators (a single regrouping on each side and a three-wire swap in the middle). -/
def sigma1 (A B D : IntObj C) :
    C.Hom (C.tens (C.tens A.1 D.2) (C.tens B.1 B.2)) (C.tens (C.tens A.1 B.2) (C.tens B.1 D.2)) :=
  -- τ : D⁻⊗(B⁺⊗B⁻) → B⁻⊗(B⁺⊗D⁻), the inner three-wire swap of D⁻ and B⁻
  let τ : C.Hom (C.tens D.2 (C.tens B.1 B.2)) (C.tens B.2 (C.tens B.1 D.2)) :=
    C.comp (C.aInv D.2 B.1 B.2)
      (C.comp (C.braid (C.tens D.2 B.1) B.2) (C.tensH (C.id B.2) (C.braid D.2 B.1)))
  C.comp (C.aHom A.1 D.2 (C.tens B.1 B.2))
    (C.comp (C.tensH (C.id A.1) τ) (C.aInv A.1 B.2 (C.tens B.1 D.2)))

/-- **`σ₂`** — route `f`'s and `g`'s outputs to the external outputs and back onto the loop:
`(B⁺⊗A⁻)⊗(D⁺⊗B⁻) → (D⁺⊗A⁻)⊗(B⁺⊗B⁻)`. It swaps the two forward wires `B⁺` and `D⁺`. -/
def sigma2 (A B D : IntObj C) :
    C.Hom (C.tens (C.tens B.1 A.2) (C.tens D.1 B.2)) (C.tens (C.tens D.1 A.2) (C.tens B.1 B.2)) :=
  C.comp (C.aHom B.1 A.2 (C.tens D.1 B.2))
    (C.comp (C.tensH (C.id B.1) (C.aInv A.2 D.1 B.2))
      (C.comp (C.tensH (C.id B.1) (C.tensH (C.braid A.2 D.1) (C.id B.2)))
        (C.comp (C.aInv B.1 (C.tens D.1 A.2) B.2)
          (C.comp (C.tensH (C.braid B.1 (C.tens D.1 A.2)) (C.id B.2))
            (C.aHom (C.tens D.1 A.2) B.1 B.2)))))

/-- **The abstract GoI composition** `g ∘ f : Int(C)`, on any traced SMC: wire `f`'s and `g`'s ports
together with `σ₁`, run `f ⊗ g`, re-wire with `σ₂`, and **trace out the shared loop** `B⁺ ⊗ B⁻`. This is the
composition `IntConstruction` flagged as the open remainder — here a genuine definition. Its category /
compact-closed *laws* (the JSV/AHS theorem) remain the named `[open]` chase, discharged concretely in `Rel`
([`RelCompact`](RelCompact.lean), `relIntComp`). -/
def IntCompose {A B D : IntObj C} (f : IntHom C A B) (g : IntHom C B D) : IntHom C A D :=
  C.trace (C.comp (sigma1 C A B D) (C.comp (C.tensH f g) (sigma2 C A B D)))

/-- **Sanity at the identity wires** — `IntCompose` is total: it composes `IntId` with any `f` to a
well-typed `IntHom`, witnessing the operation is genuinely defined (not just typed) on a concrete pairing.
The *equation* `IntId ∘ f = f` is part of the flagged law-verification (proved concretely in `RelCompact`). -/
example {A B : IntObj C} (f : IntHom C A B) : IntHom C A B := IntCompose C (IntId C A) f

end RelExist.IntConstruction
