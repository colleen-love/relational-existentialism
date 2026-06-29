# 01 — Signature: the vocabulary, with the self left undefined

> *The doctrine ([`00-domain.md`](00-domain.md)) fixed the kind of arena. This page fixes the **specific
> language** — sorts, generators, and the one genuinely added piece of structure, **attention as codirected
> eigenstructure**.* It fixes the language only. **It does not name the self.** The self is defined in
> [`02-axioms.md`](02-axioms.md) (as the fixed point of the process) and derived as theorems in the
> formalization pass; a signature that already named it would smuggle the paper's output in as vocabulary and
> short-circuit the whole derivation.

## 1.1 Sorts

- A distinguished object **`D`** — the sort of **systems**, the things that can come to be selves. Other
  objects are built from `D` by `⊗`, `I`, and (in the cartesian fragment) `×`.
- The unit **`I`**. A **state** of a system is a point `s : I → D`. States are the inhabitants we ultimately
  care about; **"a self" will be a distinguished kind of state, never a primitive sort** — and it is not
  named here.

## 1.2 Generators from the doctrine

`Cl(𝕋)` carries, by being an instance of the doctrine, the generic structural maps: identities and
composition (`id`, `∘` — trivial and through-relating), the tensor and symmetry (`⊗`, `γ` — coexistence and
its order-indifference), the **trace** `Tr` (feedback / looping), the cartesian-fragment-only copy and delete
(`Δ`, `!`), and the `ν`-modality's unfolding (`out`). No further *relating* generators are primitive: specific
relatings (a conversation, a measurement) enter per-model, as images of generic morphisms. The theory is
deliberately thin — its content is in the **axioms** and in the **attention operator** below, not in a rich
stock of named arrows.

## 1.3 Attention as codirected eigenstructure

The one piece of structure the philosophy needs and the bare doctrine does not supply is **attention** — and
it must be added *without* smuggling in a pre-relational self who "has" and "spends" it.

### 1.3.1 Finiteness is constitutive, not an external budget

Earlier drafts bolted attention on as an **external budget**: a private scalar `β` a self draws down. That
quietly presupposes the self — the one who owns the budget — which is exactly what relation-primacy denies. We
drop it. Attention finiteness is **constitutive**: a perspective is finite *by definition*, bounded
integration capacity being part of what being a located someone *is*. We encode it as a **capacity** `α` — a
top element `⊤` of a complete lattice, the perspective's own ceiling — and there is **no budget parameter `β`
anywhere**. `α` is finite by constitution, not by allowance.

### 1.3.2 The codirected attention operator

A relation codirects the attention of *both* relata: having a relation is what elicits and routes attention,
so **the coupling is the operator**. Given a coupling `c` on relata — read `c i j` as "`i` relates to `j`",
**not** required symmetric, so codirection is **asymmetric** — the attention field is routed along the
coupling: a relatum's sustained standing draws on the standing of those it relates to. Two properties carry
the philosophy:

- **Receiving raises giving** — the operator is **monotone**: more standing among those who relate to you
  yields at least as much for you. This is positive feedback, not a depleting allowance (structurally, the
  recursion of eigenvector centrality, `xᵢ ∝ Σⱼ Aᵢⱼ xⱼ`).
- **Asymmetry / perspective-dependence** — the coupling need not be symmetric and is read through each node's
  whole field, so the same edge expresses differently at each end.

**One operator, two resolutions.** The order-theoretic operator above (on the projection lattice) and the
matrix-level dynamics used in the concrete model are the **same operator seen at two resolutions** — the
coarser the support shadow of the finer. There are not two parallel half-defined operators; there is **one**
codirected attention operator, and the signature's job is to fix *that* — its sorts, its capacity `α`, its
codirected action. **A3** (in [`02-axioms.md`](02-axioms.md)) states the character this operator must have;
the **self is its fixed point**, defined there and derived later — it is deliberately **not** part of the
signature.

> **Removed: the self-definition.** Earlier drafts of this signature ended by *defining* `self := νΦ_c` (the
> greatest fixed point) as vocabulary. That is removed here, on purpose. Naming the self in the signature
> posits the paper's conclusion as a definition and makes the derivation circular. The signature fixes the
> language; the self is what the language's process turns out to have as a fixed point — a result, not a
> name.

## 1.4 The relational sort `≈`

We add a distinguished **relation object** `≈ ↣ D ⊗ D` — a subobject of `D ⊗ D` — for **lived identity** (the
greatest bisimulation). It is deliberately **not** an endomorphism `D → D` (that would be the σ-move, the
cartesian self-look); it is a relation living one level up. This type-level distinction is load-bearing: an
endomap self-look is cartesian and Lawvere-obstructed (it fragments at the seam), whereas a *relation* is
coinductive and fragment-neutral (it does not). The two are different *kinds of arrow* — the formal image of
"knowing vs feeling." `≈` is pinned down coinductively by **A2** as a greatest fixed point; its quotient
`𝔼 := D/≈` is the **shared world**.

## 1.5 What a model is (preview)

A **model** of `𝕋` is a structure-preserving functor `M : Cl(𝕋) → 𝒟` into a semantic category, preserving
whatever structure that domain has: `⊗, γ, Tr, ν` for a **monoidal** model (e.g. finite-dimensional Hilbert
spaces — physics), additionally `Δ, !` for a **cartesian** model (social / mental framings, which copy but do
not entangle), and the coupling and capacity `α` for a model that **carries attention**. The seam reappears
here as a typing fact: because the cartesian domains have a natural `Δ` and the compact-closed fragment
provably does not, there is **no** structure-preserving functor from the compact-closed fragment into them —
"two people are entangled" is not unwise, it is *ill-typed*.

The next file states the four commitments — **A1, A2, A3, D1** — that cut `Cl(𝕋)` down to *this* theory, with
A3 stated as an abstract character and the self defined (not yet derived) as the joint fixed point.
