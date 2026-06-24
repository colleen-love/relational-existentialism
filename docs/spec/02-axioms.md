# 02 — The Axioms

> *The basis: the axioms and the definition.* This file holds only what the theory
> **assumes** — the three axioms **A1–A3** and the definition **D1** — each stated formally,
> tagged `[fragment; status]`, and glossed against the plain-language view. What the theory
> **proves** lives elsewhere: the theorems **T1–T3** and the structural results in
> [theorems.md](theorems.md), the quantitative theorem in [03](03-sparsity-conjecture.md).
>
> The typed labels separate assumed from proved: **A1–A3** are **axioms** (taken), **D1** is
> a **definition** (notation, no logical content), **T1–T3** are **theorems**. For the
> checked dependency map — per-item independence evidence and verified `#print axioms`
> footprints — see the [Axiom Dependency Audit](axiom-audit.md). (Summary: the basis is four
> items; only **A3** is a load-bearing wager, and its independence is mechanized — drop it and
> the theory collapses to the universal solvent.)

Throughout, `𝒞 = Cl(𝕋)`, `σ = Tr` is the self-relation operator (D1), `γ` is the
symmetry, `Δ` the diagonal (cartesian fragment only), and `(R, ·, 1, ≤, β, c, ε)`
the attention data of [§1.3](01-signature.md).

---

# The axioms

## A1 — The ambient structure `[structural; both]`

**Statement.** The doctrine works in a **traced symmetric monoidal category** `𝒞 = Cl(𝕋)`
with a distinguished **cartesian fragment** `𝒞_×` and a **ν-modality** (greatest fixed
points / final coalgebras), as set out in [00 — The Doctrine](00-doctrine.md).

**Axiom.** This structure is *assumed*, not derived — it is the language in which every
other commitment is stated. In Lean it appears as a hypothesis (the `TracedSMC` typeclass
and the complete-lattice / `OrderHom.gfp` machinery), so results proved over it report "no
logical axioms"; but the structure's operations and laws are themselves commitments, and
honesty names them here as the first axiom rather than hiding them as a relocated hypothesis.

**Gloss.** Before any claim about selves or relations, you must fix *what kind of thing a
relating is*: composable, tensorable, traceable, with a cartesian corner where copying is
allowed. A1 is that choice of arena.

**Role.** The precondition for everything: A2, A3, D1, and the theorems T1–T3 cannot even be
stated without it. The [Axiom Dependency Audit](axiom-audit.md) records why A1 is independent
(removing it removes the language).

---

## A2 — Relation primacy `[structural; both]`

**Statement.** A state's identity is exhausted by its behavior under all
process-contexts. Writing a *context* as a unary morphism-with-a-hole
`C[-] : 𝒞(I, D) → 𝒞(I, X)` built from the generators, define for states `s, t : I → D`:

$$
s \;\equiv\; t
\quad:\Longleftrightarrow\quad
\forall\, C[-].\ C[s] = C[t].
$$

**Axiom.** `≡` is the finest congruence the theory distinguishes; there is **no**
state-distinguishing data beyond contextual behavior. Equivalently: the only points
of `D` are those forced by the morphisms (no "bare carrier" under the relatings).

**Gloss.** *Take away every relation and there is no bare self left underneath.* The
knot is a shape the rope holds; pull the rope straight and nothing remains. This is
Yoneda made into a commitment: an object is its relatings.

**Role.** Structural premise. It is what licenses defining identity *coinductively*
in **T2** — `≡` will be exhibited as the bisimilarity `≈`, so that "same behavior in
all contexts" and "greatest bisimulation" coincide.

---

## A3 — Recursion constitutes the self `[posit; both, with cartesian existence]`

**The discriminating axiom.** A **self / eigenform** is a state that is a fixed point
of **co-directed attention-feedback** — equivalently, that is sustained by the
relations it keeps looping. In the structural form ([§1.3](01-signature.md),
[`Scratch/Attention.lean`](../../formal/Scratch/Attention.lean)): a self is an
eigenform of the co-directed attention operator `Φ_c` induced by the coupling, the
carrier of selves being its greatest sustainable field,

$$
\text{self} \;=\; \nu\Phi_c, \qquad \Phi_c(\nu\Phi_c) = \nu\Phi_c .
$$

Finiteness here is *constitutive* (the bounded capacity `α`), not an external budget,
so the selection is built into the structure rather than bolted on. In the **uniform,
depleting special case** ([§1.3.4](01-signature.md),
[`RelExist/Loop.lean`](../../formal/RelExist/Loop.lean)) this reduces to the threshold
form: with `loop_R` and budget `β`,

$$
e \ \text{is a self}
\quad:\Longleftrightarrow\quad
\mathrm{loop}_R(e) = e \ \ \wedge\ \ d(e) \ge 2 \ \ \wedge\ \ d(e)\cdot\lambda(e) \le \beta,
$$

with carrier `Stab_R := { e : loop_R(e) = e, d(e) ≥ 2, d·λ ≤ β }`. Here `e` is
unchanged by budgeted return, it required genuine recursion (`d ≥ 2`, not a one-off),
and the cost of reaching the eigenform is affordable. (The bridge proving these two
coincide — `loop_R(e)=e ⟺ d·λ ≤ β` — is [Step 3](03-sparsity-conjecture.md).)

**Status: posit.** The philosophy's central wager, *asserted*. The existence of fixed
points is underwritten by T1 and by Knaster–Tarski (`νΦ_c`); the *selection* — that
co-directed recursion under constitutive finiteness is what promotes a fixed point to
a self — is the new content. It is what stops the theory from being a universal
solvent.

**Gloss.** A relation builds a persisting self only when it loops — returned to,
re-entered, lived again until it holds. The decades-long friendship, the formative
parent, the work you keep choosing: built from relations *iterated*, not merely had.
Attention, co-directed and finite, is what shapes which loops close — and being
attended-to *raises* the attention one can give, so the self is sustained generatively,
not spent down.

**Role.** Everything discriminating about the theory routes through here. Drop A3
and the resource bound and *nearly everything* models `𝕋` (the triviality pole);
keep them and models thin out to the systems that actually stabilize selves. The
candidate theorem of [03](03-sparsity-conjecture.md) — **`Stab_R` is sparse under
finite `β`** — is the formal cash value of "a self is an achievement of recursion."

**Mechanized.** The defining condition `loop_R(e) = e` is now tied to the resource
threshold in Lean — [`formal/RelExist/Loop.lean`](../../formal/RelExist/Loop.lean)
proves `loop_R(e) = e ⟺ N(e) ≥ d(e) ⟺ d·λ ≤ β` (`loopR_isEigen_iff`), so A3's
fixed-point self and the counted threshold are provably the same condition.

---

# The definition

## D1 — Self-relation is feedback `[definitional; both]`

**Statement.**

$$
\sigma(P) \;:=\; \mathrm{Tr}(P).
$$

**Definition.** The self-relating of a system *is* the trace of a relating on it — output
returned to input — and nothing more is meant by "the mind aware of the mind."

**Gloss.** The simplest relation is the self relating to itself: attention turned
inward, modeled as feedback. Because `Tr` needs no copying, this definition is
**fragment-neutral** and survives into the quantum fragment as the partial trace —
even though its *mirror* reading (T3) does not.

**Co-directed form.** Self-relation is the unary case (`Tr` over a private wire). When
the looped wire is *shared* between two systems, the same feedback is **co-directed** —
neither end closes the loop alone — and this is the engine of attention in
[§1.3](01-signature.md): the attention operator `Φ_c` is feedback through the coupling,
so co-direction is a consequence of the relating, not added to it.

**Role.** Pure definition; fixes the referent of `σ` used by T1, A3, T3, and the
co-directed `Φ_c` of A3.

---

# The theorems

The theorems that follow from this basis — **T1** (to relate is to create), **T2**
(observational identity and the "we"), **T3** (knowing vs feeling) — together with the
structural results about relating (self, part, other, collection; routing vs directing;
what knowing does to a relation) live in their own file, with honest status tags and Lean
names: **[theorems.md](theorems.md)**. The quantitative theorem (sparsity) is
[03](03-sparsity-conjecture.md). Derived notions (self, distributed self, birth/death) are
collected in [theorems.md](theorems.md) too.

---

## The residue — typed out, on the doctrine's own reading

Valence, the hard problem, and freedom are not unstated axioms. On the doctrine's own
reading they fall **outside what a structure-preserving functor expresses** — the language
speaks only of structure functors preserve, and these three are the non-structural
remainder. By T3, formalizing is itself the σ-move (the objectifying look that leaves a
remainder), so the language captures the *structure* of feeling (`≈`) and, on this reading,
not feeling-as-lived.

This is a **stance the doctrine takes, not a proved theorem**: there is no formal result that
these three are non-functorial (one cannot even state "valence" to prove it). Held as a
stance it is the program naming its own boundary; stated as a theorem it would overreach.

→ Continue to [03 — The Sparsity Conjecture](03-sparsity-conjecture.md), the one
place the spec reaches for a genuine **theorem** rather than a redescription.
