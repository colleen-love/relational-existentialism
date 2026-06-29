# 01 — The Signature

> **Normalized axioms (handoff XX/XXI) — read alongside [`AXIOMS.md`](AXIOMS.md).** This essay predates the
> axiom normalization; read its axiom references through the canonical four: **A3 is now a *process***
> (relations co-direct attention asymmetrically in the relata), with the **self its *derived* fixed point**,
> not a posited eigenform; **D1** generalizes `σ = Tr` to the **modular flow** (the trace its
> infinite-temperature limit); **A1** is one dimension-generic arena. The four axioms are one canonical,
> version-pinned layer in `theory/`.

> *The philosophy as a presented theory.* The doctrine ([00](00-doctrine.md)) fixes
> the *kind* of language. The signature fixes the *specific* language: the sorts,
> the generating morphisms, and the one piece of genuinely added structure —
> **attention as a bounded resource** — that the philosophy needs and the doctrine
> does not supply for free.
>
> **Paper-one scope.** Paper one uses the signature's sorts, the trace, and the relational sort `≈`. The
> *bounded-resource* machinery (`(R, ·, 1, ≤, β)`, mechanized in the **archived** `Attention.lean` /
> `Loop.lean`) is the quantitative substrate of paper three (sparsity); it is presented here but is not
> load-bearing for paper one's headline.

We present a theory `𝕋`. Its **classifying category** `Cl(𝕋)` is the free
traced-symmetric-monoidal-with-`ν` category on the data below, quotiented by the
axioms of [02](AXIOMS.md). A **model** is a structure-preserving functor
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
content is in the **axioms** and in the **co-directed attention operator** below, not
in a rich stock of named arrows.

---

## 1.3 Attention as co-directed eigenstructure

Earlier drafts bolted attention on as an **external budget**: a private scalar `β` a
self spends down, finiteness imposed from outside. That quietly smuggled in a
*pre-relational* self — the one who "has" the attention and "allocates" it — which is
exactly what relation-primacy denies. This section replaces it. Attention is a
**consequence of the relational structure**: co-directed, generative, and finite *by
constitution* rather than by allowance. Everything below is mechanized in
[`formal/Archive/Scratch/Attention.lean`](../../archive/formal/Archive/Scratch/Attention.lean).

### 1.3.1 Finiteness is constitutive, not imposed `[structural]`

A perspective is finite *by definition* — bounded integration capacity is part of what
being a located someone *is*, the same un-closable mirror as [3.3](../../paper-1/spec/paper-one.md). We
encode it as a **bounded capacity** `α` (a complete lattice, with top `⊤`); an
attention **field** assigns each relatum a standing, `att : V → α`. The only bound is
`⊤` of `α` — the perspective's own limit — and there is **no budget parameter `β`
anywhere** in the account. Attention-scarcity, perspectival partiality, and the
generativity of relation thus become three faces of one fact, rather than a posit
standing apart from the doctrine.

### 1.3.2 The co-directed attention operator `[structural]`

A relation co-directs the attention of *both* relaters; having a relation is what
elicits and routes attention, so the **coupling is the operator**. Given a coupling
`c` on relata (read `c i j` as "`i` relates to `j`"; **not** required symmetric, so
co-direction is asymmetric), define

$$
\Phi_c(att)(i) \;=\; \bigsqcup_{j} \ \bigsqcup_{c\,i\,j}\ att(j).
$$

Your sustained standing is the supremum of the standing of those you relate to. Two
properties carry the philosophy:

- **Receiving raises giving** (`couplingOp_mono`): `Φ_c` is *monotone* — more standing
  among those who relate to you yields at least as much for you. This positive
  feedback, not a depleting allowance, is what shapes attention. Structurally it is the
  recursion of eigenvector centrality, `xᵢ ∝ Σⱼ Aᵢⱼ xⱼ`.
- **Asymmetry, perspective-dependence**: `c` (and quantitatively its weights) need not
  be symmetric and is read through each node's whole field, so the same edge expresses
  differently at each end.

**The operator-algebraic reading.** In the intended operator-algebraic semantics, the
relations form an algebra `A` (C*/von Neumann), and `Φ_c` is a **unital completely-positive
map `A → A`** in the **Heisenberg picture** — attention acts on the algebra of relations,
codirected by the configuration of `A` itself (relation-primacy applied to attention), never a
state over it. The order-theoretic `Φ_c` above is the projection-lattice / support shadow of
that map: the same `ν`-modality, one resolution coarser. This operator-first framing — attention
as an operator on the algebra, not a state — is what the whole signature serves.

### 1.3.3 The self as an eigenform; generativity `[the load-bearing reframing]`

A **self is an eigenform of co-directed attention** — a fixed point of `Φ_c`. The
sustained self is the *greatest* such field,

$$
\text{self} \;:=\; \nu\Phi_c \quad(\texttt{sustainedField}),
\qquad
\Phi_c(\nu\Phi_c) = \nu\Phi_c \quad(\texttt{sustainedField\_fixed}),
$$

via the same `ν`-modality (Knaster–Tarski / `OrderHom.gfp`) used for `≈` in
[3.2](../../paper-1/spec/paper-one.md): the self is *the most attention that can be co-sustained*. Two
mechanized consequences make this **generative**, not allocative:

- **Accumulation** (`orbit_ascending`, `orbit_le_gfp`): from a self-reinforcing seed
  (`a ≤ Φ_c a`), iterated relating only *grows* the field, never depletes it, bounded
  above by the self. "Receiving more increases what you can give" is a theorem.
- **Maximality / coinduction** (`sustainedField_greatest`): to show a standing is
  sustained, exhibit a self-upholding field carrying it.

This is where **Mozart** lives: a node whose biological substrate is gone still carries
weight in `νΦ_c`, because the edges — scores, recordings, each listener's return — keep
the coupling live; he radiates attention *through the fabric*. Death is those edges
decaying, the weight fading *on the timescale of others' returning* — the same
distributed-self story as [3.2](../../paper-1/spec/paper-one.md)'s `𝔼`.

### 1.3.4 The resource budget as a special case `[reduction]`

The old budget model is not *wrong*; it is the **uniform, conserved, depleting** regime
— attention treated as one conserved scalar drawn down at a fixed per-return cost.
There, "how many times can I return to this one relation" collapses to `N = ⌊β/λ⌋` and
the eigenform condition collapses to a threshold `d·λ ≤ β`. That regime is the subject of
[`formal/Archive/RelExist/Loop.lean`](../../archive/formal/Archive/RelExist/Loop.lean) — though the file works with an
**abstract** self-relation endomap, and identifying *its* `σ` and depth `d` with `Φ_c` and the
*convergence depth* of the orbit `Φ_c^{\,n}` is a **modeling reading, not mechanized**. The depth
floor `d ≥ 2` — a self needs genuine return, not a one-off — is the posit that keeps selfhood rare;
it is assumed, not derived (nothing forces a fixed point to require two returns). `[posit]`

---

## 1.4 The relational sort `≈`

We add a distinguished **relation object**

$$
{\approx}\ \rightarrowtail\ D \otimes D
$$

— a subobject of `D ⊗ D` — for the **lived identity** (the greatest bisimulation). It is *not* an
endomorphism `D → D` (that would be the σ-move, the diagonal, the cartesian
self-look); it is a relation living one level up. This type-level distinction is the
whole of Theorem **3.3**: `σ` (an endomap, cartesian, Lawvere-obstructed) fragments;
`≈` (a relation, coinductive, fragment-neutral) does not. The two are different
*kinds of arrow*, and that difference is the formal image of "knowing vs feeling."

`≈` is not freely generated — it is pinned down coinductively by Theorem **3.2** as a
greatest fixed point `νΘ`. Its quotient `𝔼 := D/≈` is the **shared world**.

`[definitional]`

---

## 1.5 What a model is (preview of Layer 4)

A **model** of `𝕋` is a functor `M : Cl(𝕋) → 𝒟` preserving the structure a given
domain has:

- preserving `⊗`, `γ`, `Tr`, `ν` → a **monoidal** model (e.g. `FdHilb`: physics);
- preserving additionally `Δ`, `!` → a **cartesian** model (e.g. social /
  mental-health framings, which have copying but no entanglement);
- preserving the coupling and capacity `α` (the co-directed attention operator `Φ_c`
  of §1.3) → a model that **carries attention**, in which the sparsity statement of
  [03.7](../../archive/spec/03.7-sparsity.md) can even be asked.

The **firewall theorem** previewed in the plan lives exactly here: because the
cartesian-only domains have a natural `Δ` and the compact-closed fragment provably
does not, there is **no** structure-preserving functor from the compact-closed
fragment into them. "Two people are entangled" is not unwise — it is *ill-typed*.

The next file states the commitments — three axioms (**A1–A3**), a definition (**D1**),
and three theorems (**3.1–3.3**) — that cut `Cl(𝕋)` down from the free theory to *this* one.
