/-
# The GoI / `Int` construction — the non-cartesian, fully-dual arena, on any traced SMC

[`SelfApplication`](SelfApplication.lean) built the *cartesian* reflexive object (`Pω`, where `Y` is
self-application and copy is free). The genuinely **non-cartesian** reflexive object — where `Y` is the
**trace** with no cartesian copy — lives in a *compact closed* category, and the canonical way to produce
one from a traced symmetric monoidal category `C` is the **`Int` (Geometry-of-Interaction) construction**
of Joyal–Street–Verity / Abramsky–Haghverdi–Scott. This module mechanizes its **object-level structure**
on the abstract [`TracedSMC`](../RelExist/Traced.lean) typeclass: the compact, fully-dualizable arena
itself, on *any* traced SMC.

`Int(C)` has:

* **Objects** `IntObj` — pairs `(A⁺, A⁻)`: a "forward" and a "backward" wire.
* **Homs** `IntHom (A⁺,A⁻) (B⁺,B⁻) := C.Hom (A⁺ ⊗ B⁻) (B⁺ ⊗ A⁻)` — a *single* `C`-morphism carrying
  both directions at once. This is the two-way hom that makes the category compact.
* **Tensor / unit** `IntTens`, `IntUnit` — pointwise on the two wires.
* **Dual** `IntDual (A⁺,A⁻) := (A⁻, A⁺)` — *swap the wires.* Every object is dualizable; this is the
  compact-closed structure, and `Int(C)` is **not cartesian** (the firewall: a non-trivial compact
  category has no diagonal). The dual is proved here to be an **involution**, **monoidal** (distributes
  over `⊗`), and **unit-fixing** — the object-level compact data, all definitional.
* **Identity** `IntId` — the straight wire `C.id (A⁺ ⊗ A⁻)`.

**What is built, and what is the flagged remainder.** Built and verified: the object-level compact
structure — objects, two-way homs, tensor, unit, the dual with its involution / monoidality / unit
laws, and the identity — **and the dual's action on morphisms**: the contravariant transpose `IntDualHom`
(`f : A → B ↦ fᵈ : Bᵈ → Aᵈ`, by conjugating with the braidings), proved to **preserve identities**
(`IntDualHom_id`) and be **involutive** (`IntDualHom_involutive`, `(fᵈ)ᵈ = f`) over a *coherent* traced
SMC — both **0 axioms**, the two swap-braids cancelling by the symmetry `γ∘γ = id`. This is the *arena*
plus the dual functor on arrows: every traced SMC embeds into its compact closed `Int(C)`, the
non-cartesian setting a reflexive object would inhabit. **Not** built here (the research-grade
remainder): **composition via the trace** — the GoI move `(g ∘ f) := Tr^{B}(wiring of f, g)` that feeds
`f`'s output wire into `g` and back — and the **compact-closed axioms** (the snake/triangle equations),
whose verification from the seven JSV axioms is a long structural-iso chase. (Full *functoriality* of the
dual, `(g∘f)ᵈ = fᵈ∘gᵈ`, likewise waits on that composition.) Composition's *type* is
`IntHom A B → IntHom B C → IntHom A C`, realized by a trace over the shared object `B⁺ ⊗ B⁻`; getting
that wiring provably right (not merely type-correct) is the work left. By `ReflexiveModel`'s duality this
whole construction is the **construction** side — it would host `Y` as the trace, orthogonal to the seam.

**Why composition + snake are research-grade (the grounded status).** The composition `g ∘ f` permutes
`A⁺⊗C⁻⊗B⁺⊗B⁻` into `f`'s and `g`'s inputs, applies `f ⊗ g`, re-permutes the outputs, and traces over
`B⁺⊗B⁻` — a long composite of braids and associators — after which the category laws (`id`, `assoc`)
and the **snake/triangle** equations must be derived from the seven JSV trace axioms *plus* the
symmetric-monoidal coherence ([`Coherence`](../RelExist/Coherence.lean)). This is exactly the
Joyal–Street–Verity / Abramsky–Haghverdi–Scott theorem "`Int(C)` is compact closed", and it is hard
precisely because the base is **non-strict**: the associators/unitors are honest isomorphisms threaded
through every equation (even the concrete `Rel` model is non-strict — its `raHom`/`raInv` relate the
*distinct* types `(X×Y)×Z` and `X×(Y×Z)`). mathlib has no traced/compact-closed scaffolding to inherit.
Everything verifiable *without* this composition is a single `C`-level conjugation — which is why
`IntDualHom` and its laws close (above), and why the morphism layer stops exactly there. The **snake /
triangle (zigzag) equations are nonetheless closed concretely** in the canonical model — see
[`RelCompact`](RelCompact.lean): `Rel` is compact closed with both zigzag identities proved `= id`. So
the compact-closed *axioms* are discharged in `Rel`; what stays the named research-grade remainder is
the **abstract `Int(C)` composition-via-trace** for an arbitrary non-strict `C`, and the linear
*reflexive object* inside the compact arena.

**Honest scope.** A rederivation (the `Int` construction is standard) mechanized at the object level on
our bespoke `TracedSMC`. The contribution is exhibiting the compact, fully-dual, *non-cartesian* arena
concretely on any traced SMC — the home of the linear reflexive object — with the morphism layer
precisely scoped as the remaining build.
-/
import RelExist.Traced
import RelExist.Coherence

namespace RelExist.IntConstruction

open RelExist.Traced

variable (C : TracedSMC)

/-- **Objects of `Int(C)`**: a pair of a forward wire `A⁺` and a backward wire `A⁻`. -/
def IntObj : Type _ := C.Obj × C.Obj

/-- **The two-way hom**: a single `C`-morphism `A⁺ ⊗ B⁻ → B⁺ ⊗ A⁻` carrying both the forward and
backward directions. Packing both directions into one arrow is what makes `Int(C)` compact. -/
def IntHom (A B : IntObj C) : Type _ := C.Hom (C.tens A.1 B.2) (C.tens B.1 A.2)

/-- **Tensor**: pointwise on the two wires. -/
def IntTens (A B : IntObj C) : IntObj C := (C.tens A.1 B.1, C.tens A.2 B.2)

/-- **Unit**: the unit on both wires. -/
def IntUnit : IntObj C := (C.unit, C.unit)

/-- **Dual**: *swap the forward and backward wires.* Every object of `Int(C)` is dualizable — this is
the compact-closed structure, and the reason `Int(C)` is non-cartesian. -/
def IntDual (A : IntObj C) : IntObj C := (A.2, A.1)

/-- **The dual is an involution** — `(Aᵈ)ᵈ = A`. The defining feature of a compact (fully self-dual)
arena, here definitional (swap twice). -/
@[simp] theorem IntDual_involutive (A : IntObj C) : IntDual C (IntDual C A) = A := rfl

/-- **The dual is monoidal** — it distributes over the tensor: `(A ⊗ B)ᵈ = Aᵈ ⊗ Bᵈ`. (Swapping wires
commutes with pointwise tensoring.) -/
@[simp] theorem IntDual_tens (A B : IntObj C) :
    IntDual C (IntTens C A B) = IntTens C (IntDual C A) (IntDual C B) := rfl

/-- **The dual fixes the unit** — `Iᵈ = I`. -/
@[simp] theorem IntDual_unit : IntDual C (IntUnit C) = IntUnit C := rfl

/-- **The identity morphism** of `Int(C)` — the straight wire `A⁺ ⊗ A⁻ → A⁺ ⊗ A⁻` (`C.id`). -/
def IntId (A : IntObj C) : IntHom C A A := C.id (C.tens A.1 A.2)

/-- **The hom into the dual is the transpose hom.** `IntHom A B` and `IntHom Bᵈ Aᵈ` are the *same*
`C`-hom type up to swapping the tensor factors: both are a `C`-morphism between `A⁺⊗B⁻`-flavoured and
`B⁺⊗A⁻`-flavoured objects. Concretely `IntHom C (IntDual C B) (IntDual C A)` unfolds to
`C.Hom (B⁻ ⊗ A⁺) (A⁻ ⊗ B⁺)` — the contravariant transpose of `IntHom C A B = C.Hom (A⁺ ⊗ B⁻) (B⁺ ⊗ A⁻)`.
This is the object-level shadow of `(f : A → B) ↦ (fᵈ : Bᵈ → Aᵈ)`, the compact dagger of morphisms (the
braided identification of the two is part of the flagged morphism layer). -/
theorem IntHom_dual_eq (A B : IntObj C) :
    IntHom C (IntDual C B) (IntDual C A) = C.Hom (C.tens B.2 A.1) (C.tens A.2 B.1) := rfl

/-- **The dual (transpose) of a morphism** — `f : A → B` ↦ `fᵈ : Bᵈ → Aᵈ`, the contravariant action
of the dual on arrows. Concretely it conjugates `f` by the braidings that swap the two wires of each
object: `fᵈ = (B⁻⊗A⁺ →[γ] A⁺⊗B⁻ →[f] B⁺⊗A⁻ →[γ] A⁻⊗B⁺)`. Definable on any traced SMC (it uses only the
braiding); the laws below need the symmetry coherence. -/
def IntDualHom {A B : IntObj C} (f : IntHom C A B) : IntHom C (IntDual C B) (IntDual C A) :=
  C.comp (C.braid B.2 A.1) (C.comp f (C.braid B.1 A.2))

/-! ### The dual is a contravariant involutive functor on morphisms

Over a **coherent** traced SMC (where the braiding is a genuine symmetry, `γ∘γ = id`), the
morphism-dual preserves identities and is involutive — the action of the compact dual on arrows. (Full
functoriality `(g∘f)ᵈ = fᵈ∘gᵈ` needs the GoI composition, which — with the snake equations — is the
flagged research-grade remainder.) -/

variable (K : CoherentTracedSMC)

/-- **The dual preserves identities**: `(id_A)ᵈ = id_{Aᵈ}` — the two swap-braids cancel by symmetry. -/
theorem IntDualHom_id (A : IntObj K.toTracedSMC) :
    IntDualHom K.toTracedSMC (IntId K.toTracedSMC A) = IntId K.toTracedSMC (IntDual K.toTracedSMC A) := by
  show K.comp (K.braid A.2 A.1) (K.comp (K.id (K.tens A.1 A.2)) (K.braid A.1 A.2))
      = K.id (K.tens A.2 A.1)
  rw [K.id_comp, K.braid_symm]

/-- **The dual is involutive on morphisms**: `(fᵈ)ᵈ = f`. The four conjugating braids cancel in two
symmetric pairs (`γ∘γ = id`), leaving `f` — the morphism-level shadow of `IntDual_involutive`. -/
theorem IntDualHom_involutive {A B : IntObj K.toTracedSMC} (f : IntHom K.toTracedSMC A B) :
    IntDualHom K.toTracedSMC (IntDualHom K.toTracedSMC f) = f := by
  show K.comp (K.braid A.1 B.2)
        (K.comp (K.comp (K.braid B.2 A.1) (K.comp f (K.braid B.1 A.2))) (K.braid A.2 B.1)) = f
  calc K.comp (K.braid A.1 B.2)
          (K.comp (K.comp (K.braid B.2 A.1) (K.comp f (K.braid B.1 A.2))) (K.braid A.2 B.1))
      = K.comp (K.comp (K.braid A.1 B.2) (K.comp (K.braid B.2 A.1) (K.comp f (K.braid B.1 A.2))))
          (K.braid A.2 B.1) := (K.assoc _ _ _).symm
    _ = K.comp (K.comp (K.comp (K.braid A.1 B.2) (K.braid B.2 A.1)) (K.comp f (K.braid B.1 A.2)))
          (K.braid A.2 B.1) := by rw [← K.assoc]
    _ = K.comp (K.comp (K.id (K.tens A.1 B.2)) (K.comp f (K.braid B.1 A.2))) (K.braid A.2 B.1) := by
          rw [K.braid_symm]
    _ = K.comp (K.comp f (K.braid B.1 A.2)) (K.braid A.2 B.1) := by rw [K.id_comp]
    _ = K.comp f (K.comp (K.braid B.1 A.2) (K.braid A.2 B.1)) := K.assoc _ _ _
    _ = K.comp f (K.id (K.tens B.1 A.2)) := by rw [K.braid_symm]
    _ = f := K.comp_id _

end RelExist.IntConstruction
