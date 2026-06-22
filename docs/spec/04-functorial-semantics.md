# 04 — Functorial Semantics (Layer 4)

> *The domains, as functors out of the theory.* A model of `𝕋` is a
> structure-preserving functor `Cl(𝕋) → 𝒟_domain`. The **existence or non-existence of
> each functor is itself the cross-domain claim** — and the verdicts are not equal.

---

## 4.1 What a model is

A **model** interprets the theory's structure in a domain: `⊗` as the domain's
coexistence, `Tr`/`ν` as its feedback/fixed points, `Δ` (where present) as its copying.
A domain *receives* a functor exactly when it has the structure the theory exports. So:

- a domain with the doctrine's **fixed-point/eigenform** structure receives the `ν`-part;
- a **cartesian** domain (copying, projections) additionally receives `Δ`, `!`;
- a **compact-closed** (quantum) domain receives the entanglement/no-cloning structure
  — and, crucially, **cannot** also be cartesian without collapsing (§4.4).

We do not have the full traced-symmetric-monoidal `Cl(𝕋)` as a Lean object (it is left
as categorical infrastructure). But the **operative content** the functors carry — the
eigenform/`gfp` structure (A2–A5) and the cartesian copy/Lawvere structure (A6) — *is*
mechanized, so a functor can be exhibited at that level, which is what §4.3 does.

## 4.2 The domains, with verdicts

| Domain | Target | Verdict | Status |
| --- | --- | --- | --- |
| **Physics (quantum)** | `FGModuleCat`/`FdHilb`; `Tr` = partial trace, co-determination = entanglement | literal monoidal functor — **redescriptive, not predictive**; the distinctive fact is **no-cloning** | ✅ **no-cloning mechanized** (§4.5) |
| **Chemistry** | reaction networks (Baez–Pollard); autocatalytic sets = looped eigenforms | **strong, near-literal** — best non-quantum fit | ✅ **mechanized** (§4.3) |
| Biology | Rosen relational biology / (M,R)-systems | strong, with an ancestor | future |
| AI | semantics of recurrence; Geometry of Interaction *is* traced categories | design-principle functor | future |
| Sociology, mental health | **cartesian fragment only** | framing; the firewall (§4.4) | ✅ **firewall mechanized** (categorical) |

## 4.3 Chemistry — the first functor (mechanized)

An **autocatalytic set** is a set of molecules that collectively sustains its own
production — a self-sustaining loop. That is a *fixed point* of a production operator,
i.e. an **eigenform**, so the chemistry functor reuses the theory's `ν`/`gfp`
machinery wholesale. In [`formal/Scratch/Chemistry.lean`](../../formal/Scratch/Chemistry.lean):

- `prodOp R : Set M →o Set M` — given the molecules present, what the network can make
  (monotone: more inputs ⇒ more reactions);
- `autocatalyticCore R := ν(prodOp R)` — the maximal self-sustaining set, with
  `autocatalyticCore_selfSustaining` (`produces (core) = core`) and
  `autocatalytic_greatest` (any self-sustaining set lies within it — coinduction);
- **the functor, witnessed:** `selfTrace_eq_autocatalyticCore` proves
  `selfTrace (prodOp R) = autocatalyticCore R` *definitionally* — the theory's
  self-trace (`νP`, [A2](02-axioms.md)) of the production operator **is** the
  autocatalytic core. A *looped self* in the theory maps to a *self-sustaining
  autocatalytic set* in chemistry. The "near-literal fit" is a one-line theorem.

## 4.4 The firewall — the cartesian side (mechanized: `Type`-level *and* categorical)

Social and mental-health domains live in the **cartesian fragment**: copying and
projections are free. The firewall is that this *forbids* the compact-closed
(entanglement) structure — "two people are entangled" is **ill-typed**, not just
unwise. In [`formal/RelExist/Firewall.lean`](../../formal/RelExist/Firewall.lean)
(mathlib-free):

- `copy` — the diagonal is free for every type (the same `(x,x)` that powers Lawvere
  in `Mirror`, and that the quantum fragment lacks);
- `joint_factors` — **every joint state is determined by its marginals**, so a joint
  carries nothing beyond its parts: there is no irreducible "between," hence no
  entangled (non-factoring) joint. Importing the compact-closed co-determination has no
  faithful image.

**Now the categorical theorem too.** The collapse is mechanized in
[`formal/Scratch/Compact.lean`](../../formal/Scratch/Compact.lean). Axiomatizing the
operative content of compact closure — the *name* bijection `(A ⟶ B) ≃ (A ⊗ Bᵈ ⟶ I)` —
together with a (sub)terminal unit (cartesian copying), `collapse` proves the structure
is **thin**: every parallel pair of morphisms coincides. So "compact-closed + cartesian"
*provably* collapses to triviality — you cannot host entanglement and free copying in one
domain. `no_cloning` is the contrapositive: a non-trivial compact-closed structure admits
no uniform copying. This is what makes "two people are entangled" ill-typed for the
cartesian social domain, as a theorem rather than a stance.

This axiomatizes compact closure minimally (the dual adjunction) rather than deriving it
from a fully reconstructed traced symmetric monoidal category; mathlib has
symmetric/braided/**rigid** monoidal categories and `ChosenFiniteProducts`, but not
traced-monoidal or a compact-closed typeclass, and the free traced SMC `Cl(𝕋)` itself is
the remaining heavy infrastructure (see §4.6).

## 4.5 Physics — the quantum fragment and no-cloning (mechanized)

Physics is the most *literal* functor (categorical quantum mechanics in
`FGModuleCat`/`FdHilb`: `Tr` is the partial trace, co-determination is entanglement),
but "redescriptive, not predictive." Its **distinctive, theory-relevant fact** is
exactly what separates it from the cartesian domains: **no-cloning**.

- **Categorical** ([`Scratch/Compact.lean`](../../formal/Scratch/Compact.lean),
  `no_cloning`): a non-trivial compact-closed structure cannot have uniform copying — the
  contrapositive of the firewall collapse.
- **Concrete** ([`Scratch/NoCloning.lean`](../../formal/Scratch/NoCloning.lean),
  `no_linear_clone`): the linear-algebra heart — cloning `ψ ↦ ψ ⊗ ψ` is, on the
  one-dimensional space, `x ↦ x²`, which is **not linear**; so no linear (unitary,
  physical) process clones. The obstruction is precisely that copying is quadratic while
  quantum evolution is linear.

So the physics/cartesian seam (no-cloning vs free copying) — the doctrine's [§0.6
seam](00-doctrine.md) and the firewall — is now a theorem on both sides.

## 4.6 What remains: the literal functor and the traced SMC

Two pieces are deliberately *not* claimed done, and named here for honesty:

1. **A literal `Functor` out of a reconstructed `Cl(𝕋)`.** Functors above are exhibited
   at the level of the *structure the theory exports* (the eigenform/`gfp` and
   compact-closed/Lawvere content), not as `CategoryTheory.Functor`s out of the free
   traced SMC as a Lean category. Building `Cl(𝕋)` as that category is research-grade.
2. **The traced symmetric monoidal typeclass.** mathlib lacks it; defining it with the
   full JSV coherence and instantiating it (e.g. proving `FGModuleCat` traced) is the
   remaining infrastructure. The collapse (§4.4) sidesteps it via the minimal
   axiomatization, which is why it lands cleanly now.

## 4.7 What this layer shows

- The **expressivity/triviality dial** in action: the chemistry functor *exists* and is
  near-literal (the theory says something real about autocatalysis); the social-domain
  entanglement functor *does not typecheck* (the theory refuses an overclaim by
  construction). The firewall is enforced by the type system, not by willpower.
- It also confirms the **residues** sit outside the language: a functor preserves only
  structure, and valence / the hard problem / freedom are precisely the non-structural
  remainder — so no functor reaches them, exactly as [A6](02-axioms.md) predicts of the
  σ-move that formalizing itself is.
