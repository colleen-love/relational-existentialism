# 01 — The Signature

> *The philosophy as a presented theory.* The doctrine ([00](00-doctrine.md)) fixes
> the *kind* of language. The signature fixes the *specific* language: the sorts,
> the generating morphisms, and the one piece of genuinely added structure —
> **attention as a bounded resource** — that the philosophy needs and the doctrine
> does not supply for free.

We present a theory `𝕋`. Its **classifying category** `Cl(𝕋)` is the free
traced-symmetric-monoidal-with-`ν` category on the data below, quotiented by the
axioms of [02](02-axioms.md). A **model** is a structure-preserving functor
`Cl(𝕋) → 𝒟` into some semantic category `𝒟` (Layer 4).

---

## 1.1 Sorts

- A distinguished object **`D`** — the sort of **systems** (the things that can come
  to be selves). Other objects are built from `D` by `⊗`, `I`, and `×` (in the
  cartesian fragment).
- The unit **`I`**. A **state** of a system is a point `s : I → D`. States are the
  inhabitants we ultimately care about; "a self" will be a *distinguished kind of
  state* (an eigenform), not a primitive sort.

`[definitional]`

---

## 1.2 Generators from the doctrine

`Cl(𝕋)` carries, by being an instance of the doctrine:

| Generator | Type | Reading |
| --- | --- | --- |
| `id_A` | `A → A` | trivial self-relating |
| `∘` | `(B→C) × (A→B) → (A→C)` | relating through |
| `⊗` | bifunctor | coexistence |
| `γ_{A,B}` | `A⊗B → B⊗A` | order-indifference of coexistence |
| `Tr^U_{A,B}` | `𝒞(A⊗U, B⊗U) → 𝒞(A,B)` | feedback / looping |
| `Δ_A`, `!_A` | `A → A×A`, `A → 1` | **cartesian fragment only**: copy, delete |
| `out` | `νF → F(νF)` | the `ν`-modality's unfolding |

No further *relating* generators are primitive. Specific relatings (a conversation,
a parenting, a measurement) are introduced per-model, as the image of generic
morphisms under a semantic functor. The theory itself is deliberately thin: its
content is in the **axioms** and in the **resource grading** below, not in a rich
stock of named arrows.

---

## 1.3 Attention as a bounded resource

This is the honest part — flagged in the plan as *added structure, not derived*.
The doctrine gives looping (`Tr`) but says nothing about its **cost** or its
**finiteness**. The philosophy's central refinement — *not every relation makes a
self, because you cannot return to everything* — requires us to add exactly that.

### 1.3.1 The attention monoid `[structural]`

Fix a **commutative ordered monoid**

$$
(R,\ \cdot,\ 1,\ \le)
$$

— `R` a set of *attention-budget* values, `·` associative-commutative with unit
`1`, and `≤` a partial order compatible with `·` (`a ≤ a'` and `b ≤ b'` imply
`a·b ≤ a'·b'`). The intended reading: `·` accumulates expenditure, `≤` compares
total spend. The canonical instance is `(ℝ_{≥0}, +, 0, ≤)`, but the abstract monoid
keeps us honest about what is actually used.

Fix a **global bound** `β ∈ R`. This single element is the entire formal content of
*"you cannot return to everything."* `β = ⊤` (unbounded) recovers the degenerate
"everything stabilizes" regime that the philosophy rejects; the interesting theory
is `β` finite.

### 1.3.2 The cost grading `[structural]`

A **cost grading** assigns to each active coupling a value in `R`:

$$
c : \mathrm{Mor}(\mathcal{C}) \longrightarrow R
$$

required to be **lax monoidal and lax compositional**:

- `c(id) = 1`,
- `c(g ∘ f) ≤ c(g) · c(f)`,
- `c(f ⊗ g) ≤ c(f) · c(g)`,
- `c(Tr^U(f)) ≥ c(f)` for non-trivial `U` — *looping costs at least as much as the
  underlying relating*, and strictly more per return (see 1.3.3).

The inequalities (rather than equalities) let a model *economize* — shared
sub-relatings need not be paid for twice — while guaranteeing that feedback is never
free. A coupling is **affordable under `β`** iff `c(f) ≤ β`.

### 1.3.3 Budgeted iteration and `loop_R` `[definitional]`

Self-relation is iterated under budget. Write `σ = Tr` (the self-relation operator,
[00 §0.3](00-doctrine.md)). For a state `s` and `n ≥ 0` define the `n`-fold return
`σ^n(s)` (with `σ^0(s) = s`). Each return charges a **per-return cost** `ε(s) ∈ R`
with `1 < ε(s)` (strictly, in `≤`), so that the accumulated cost of `n` returns is
`ε(s)^n`. Define the **budgeted loop**

$$
\mathrm{loop}_R(s) \;=\; \sigma^{\,N(s)}(s),
\qquad
N(s) \;=\; \max\{\, n : \varepsilon(s)^{\,n} \le \beta \,\}.
$$

`N(s)` is the number of returns the budget `β` can fund for `s`. The map `loop_R`
is "iterate self-relation as far as the budget allows." It is the formal engine of
Axiom **A4** and the sparsity result of [03](03-sparsity-conjecture.md): because
`β` is fixed and `ε(s) > 1`, `N(s)` is **finite and uniformly bounded** by
`log_{ε}(β)`.

> **Modeling assumption (stabilization depth).** A relating becomes a *self* only by
> closing a loop, and a loop closes only on **return** — being lived again. We
> therefore require a **stabilization depth** `d(s) ≥ 2`: a state must be returned
> to at least twice for its self-relation to hold. One-off encounters have effective
> depth `1` and never close. This `d ≥ 2` threshold, together with `ε > 1` and finite
> `β`, is what makes selfhood *rare* rather than *automatic*. `[posit]`

---

## 1.4 The relational sort `≈`

We add a distinguished **relation object**

$$
{\approx}\ \rightarrowtail\ D \otimes D
$$

— a subobject of `D ⊗ D` — for **observational identity**. It is *not* an
endomorphism `D → D` (that would be the σ-move, the diagonal, the cartesian
self-look); it is a relation living one level up. This type-level distinction is the
whole of Axiom **A6**: `σ` (an endomap, cartesian, Lawvere-obstructed) fragments;
`≈` (a relation, coinductive, fragment-neutral) does not. The two are different
*kinds of arrow*, and that difference is the formal image of "knowing vs feeling."

`≈` is not freely generated — it is pinned down coinductively by Axiom **A5** as a
greatest fixed point `νΘ`. Its quotient `𝔼 := D/≈` is the **shared world**.

`[definitional]`

---

## 1.5 What a model is (preview of Layer 4)

A **model** of `𝕋` is a functor `M : Cl(𝕋) → 𝒟` preserving the structure a given
domain has:

- preserving `⊗`, `γ`, `Tr`, `ν` → a **monoidal** model (e.g. `FdHilb`: physics);
- preserving additionally `Δ`, `!` → a **cartesian** model (e.g. social /
  mental-health framings, which have copying but no entanglement);
- preserving the grading `c` and bound `β` → a model that **respects attention**,
  in which the sparsity statement of [03](03-sparsity-conjecture.md) can even be
  asked.

The **firewall theorem** previewed in the plan lives exactly here: because the
cartesian-only domains have a natural `Δ` and the compact-closed fragment provably
does not, there is **no** structure-preserving functor from the compact-closed
fragment into them. "Two people are entangled" is not unwise — it is *ill-typed*.

The next file states the six axioms that cut `Cl(𝕋)` down from the free theory to
*this* one.
