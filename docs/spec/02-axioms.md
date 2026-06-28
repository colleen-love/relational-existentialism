# 02 — The Axioms

> *The basis: the axioms and the definition.* This file holds only what the theory
> **assumes** — the three axioms **A1–A3** and the definition **D1** — each stated formally,
> tagged `[fragment; status]`, and glossed against the plain-language view. What the theory
> **proves** lives elsewhere: the theorems **3.1–3.3** and the structural results in
> [paper one](paper-one.md), the quantitative theorem in [03.7](../archive/03.7-sparsity.md).
>
> The typed labels separate assumed from proved: **A1–A3** are **axioms** (taken), **D1** is
> a **definition** (notation, no logical content), **3.1–3.3** are **theorems**. The doctrinal basis is
> four items; only **A3** is a load-bearing wager — drop it and the theory collapses to the universal
> solvent. The concrete *matrix model* adds one further standing assumption, **B1** (a preferred /
> "classical" basis), named below — below the headline, but load-bearing for the model's knowing/feeling
> readings and so disclosed rather than left implicit. (Each theorem's `#print axioms` footprint is
> recorded with its Lean name in [paper one](paper-one.md).)

Throughout, `𝒞 = Cl(𝕋)`, `σ = Tr` is the self-relation operator (D1), `γ` is the
symmetry, `Δ` the diagonal (cartesian fragment only), and `(R, ·, 1, ≤, β, c, ε)`
the attention data of [§1.3](01-signature.md).

> **Paper-one scope.** Paper one (see [`paper-one.md`](paper-one.md)) consumes A1–A3 **abstractly** — as
> the baseline of its energy theorem (`Scratch/BandFromAxioms`: the channel is contractive and
> nondegenerate, A3 read as the decoherence-free subalgebra). The *gfp mechanization* of A3 below
> (`Attention.lean`, `Loop.lean`) and the sparsity that is its quantitative cash value are **archived** as
> the foundation of papers two and three; they are linked here for completeness, not as load-bearing
> citations for paper one.

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

**Role.** The precondition for everything: A2, A3, D1, and the theorems 3.1–3.3 cannot even be
stated without it. A1 is independent in the strongest sense — removing it removes the language.

---

## A2 — Relation primacy `[structural; both]`

**Statement.** A state's identity **is** its first-person relational unfolding — the way it relates,
lived forward — formalized as the greatest bisimulation `≈` (3.2, `νΘ`). Behavior under external
contexts is a *function* of that identity, not its definition. Writing a *context* as a unary
morphism-with-a-hole `C[-] : 𝒞(I, D) → 𝒞(I, X)` built from the generators, the third-person
**observational identity** is

$$
s \;\cong\; t
\quad:\Longleftrightarrow\quad
\forall\, C[-].\ C[s] = C[t],
$$

and the commitment is that `≈` is the real identity, of which `≅` is a **strictly lossy
projection**: `≈ ⊊ ≅`. (The mechanization realizes `≅` concretely as *trace* equivalence — one
particular observational equivalence; whether it coincides with the full *contextual* `≅` defined
above is the open context-lemma question, deliberately left open, since proving it would be the full
abstraction the inversion denies.)

**Axiom.** There is **no bare carrier** *below* the relational unfolding `≈`: the only individuation
a state has is how it relates, lived out. But identity is **not** exhausted by *external* observation
— the inside is strictly finer than any outside can read (`≈ ⊊ ≅`). Soundness holds (lived sameness
⇒ observed sameness, `≈ ⊆ ≅`); completeness is **denied**: contextual equivalence does not recover
bisimilarity. This is not a failure to prove full abstraction — proving `≈ = ≅` would *contradict*
the theory's own limitative core (3.3, the seam: you cannot completely view from outside what you
relate to), so the equality is the one thing the theory must *not* assert.

**Gloss.** *You are your lived relating, which exceeds how you appear.* Take away every relation and
no bare self remains underneath (no carrier below `≈`) — Yoneda made into a commitment, an object is
its relatings. But two selves can be observationally identical to every outside probe and still be
different selves inside: the first-person surplus, the part of who you are that no external view can
read off. Behavior is a function of self, not a definition of it.

**Role.** Structural premise. It is what licenses defining identity *coinductively* in **3.2** as the
bisimilarity `≈` — and it fixes, against the third-person `≅`, that the lived identity is the real
one. The proved soundness `≈ ⊆ ≅`, the proved strictness `≈ ⊊ ≅`, and the resulting non-injective
*forgetting from inside to outside* `D/≈ ↠ D/≅` (the decoherence of identity) are mechanized in
[`Scratch/Identity.lean`](../../formal/Archive/Scratch/Identity.lean); see
[03.5](03.5-decoherence.md#the-identity-residue-you-are-your-lived-relating).

---

## A3 — Recursion constitutes the self `[posit; both, with cartesian existence]`

**The discriminating axiom.** A **self / eigenform** is a state that is a fixed point
of **co-directed attention-feedback** — equivalently, that is sustained by the
relations it keeps looping. In the structural form ([§1.3](01-signature.md),
[`Scratch/Attention.lean`](../../formal/Archive/Scratch/Attention.lean)): a self is an
eigenform of the co-directed attention operator `Φ_c` induced by the coupling, the
carrier of selves being its greatest sustainable field,

$$
\text{self} \;=\; \nu\Phi_c, \qquad \Phi_c(\nu\Phi_c) = \nu\Phi_c .
$$

Finiteness here is *constitutive* (the bounded capacity `α`), not an external budget,
so the selection is built into the structure rather than bolted on.

**The Heisenberg commitment.** A3 fixes the *level* at which the self lives. Attention `Φ_c` is
an **operator on the algebra of relations**, not a state over it; the self is the **fixed-point
subalgebra** of `Φ_c` — the relations attention returns unchanged, in QI terms the
*decoherence-free subalgebra* — not a stationary *state* of a channel. This is what makes "self
is a collection of relations" literally true: a structured, plural sub-object closed under the
dynamics, not a point. The channel-on-states (Schrödinger) reading, which would put the self at
the level of a state, is the **road not taken** — and it is taken nowhere in the development:
every self here is the eigenform `νΦ_c`, never an invariant density matrix.

*Note (the gloss vs. the formalization).* "Decoherence-free subalgebra" / "greatest sustainable field" and
the formalized strict `νΦ_c` are **not** the same object: `νΦ_c` is the *strict* fixed point (the `μ = 1`,
fixed/known band), while the sustainable field is the larger **peripheral** block
`Peri(Φ_c) = { X : ‖Φ_c X‖ = ‖X‖ }`, which also carries the rotating (`‖μ‖ = 1, μ ≠ 1`, *energy*) band.
This is now **mechanized**: `Scratch/BandFromAxioms.lean` defines `Peri` (entrywise) and proves
`peri_iff_mem_conservedBand` — A3's sustainable field *is* exactly the conserved (modulus-one) band — with
the seam its off-diagonal part (`decoherenceFreeSeam_iff_offdiag_conserved`) and `νΦ_c` its `μ = 1`
sub-band (`fixedBand_le_conservedBand`). Reading A3's gloss literally — the self **is** `Peri(Φ_c)` — is
what closes the band-coincidence bet `H_align` of
[03.9](03.9-band-coincidence.md#postscript--is-h_align-a-fourth-axiom-scratchbandfromaxiomslean)
*without a fourth axiom* (`band_coincidence_from_axioms`): the coincidence is A3 read at the strength of
its own text, merely written in full — **not** a derivation of something beyond the three axioms.

In the **uniform, depleting special case** ([§1.3.4](01-signature.md),
[`RelExist/Loop.lean`](../../formal/Archive/RelExist/Loop.lean)) this reduces to the threshold
form: with `loop_R` and budget `β`,

$$
e \ \text{is a self}
\quad:\Longleftrightarrow\quad
\mathrm{loop}_R(e) = e \ \ \wedge\ \ d(e) \ge 2 \ \ \wedge\ \ d(e)\cdot\lambda(e) \le \beta,
$$

with carrier `Stab_R := { e : loop_R(e) = e, d(e) ≥ 2, d·λ ≤ β }`. Here `e` is
unchanged by budgeted return, it required genuine recursion (`d ≥ 2`, not a one-off),
and the cost of reaching the eigenform is affordable. (The bridge proving these two
coincide — `loop_R(e)=e ⟺ d·λ ≤ β` — is [Step 3](../archive/03.7-sparsity.md).)

**Status: posit.** The philosophy's central wager, *asserted*. The existence of fixed
points is underwritten by 3.1 and by Knaster–Tarski (`νΦ_c`); the *selection* — that
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
candidate theorem of [03.7](../archive/03.7-sparsity.md) — **`Stab_R` is sparse under
finite `β`** — is the formal cash value of "a self is an achievement of recursion."

**Mechanized — and its limits.** [`formal/Archive/RelExist/Loop.lean`](../../formal/Archive/RelExist/Loop.lean)
proves `loop_R(e) = e ⟺ N(e) ≥ d(e) ⟺ d·λ ≤ β` (`loopR_isEigen_iff`) — but for an **abstract**
self-relation endomap `σ`, *not* the relational `Φ_c`; the first `⟺` is just `StabilizesAt` unfolded
(definitional), the second one arithmetic lemma. So it ties an abstract fixed point to a threshold.
It does **not** force the depth floor `d ≥ 2` (the posit that makes selfhood rare — it is a
hypothesis, and even the witness builds `d` in by construction), and it does not connect the
trace/`νΦ_c` structure to the cost. The structural rarity is carried by the Agda nowhere-dense
result ([03.7](../archive/03.7-sparsity.md)), not the counting bound.

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
even though its *mirror* reading (3.3) does not.

**Co-directed form.** Self-relation is the unary case (`Tr` over a private wire). When
the looped wire is *shared* between two systems, the same feedback is **co-directed** —
neither end closes the loop alone — and this is the engine of attention in
[§1.3](01-signature.md): the attention operator `Φ_c` is feedback through the coupling,
so co-direction is a consequence of the relating, not added to it.

**Role.** Pure definition; fixes the referent of `σ` used by 3.1, A3, 3.3, and the
co-directed `Φ_c` of A3.

---

# The standing assumption of the matrix model

## B1 — The classical structure / preferred basis `[posit; matrix model only]`

**Statement.** The concrete mechanization (the matrix model of `Scratch/Decoherence.lean` onward) fixes a
**distinguished basis** — the "classical structure" — relative to which *knowing* is the projection onto
the **diagonal** (`dephase`), *feeling* is the off-diagonal **copy-defect** (`defectSq`), and the spectral
**bands** (fixed / rotating / transient) are read edge by edge. Concretely: `IsClassical M :⇔ M` is
diagonal *in this basis*, and `dephase` keeps that diagonal and kills the rest.

**Assumption.** *Which* basis counts as classical is **posited**, not derived. The arrow of §3–4, the
knowing/feeling split of §2, and the energy band of §5 are all stated **relative to** this basis; a change
of basis changes what is "known" and what is "felt." In physical decoherence the preferred (pointer) basis
is *selected* by the system–environment interaction (**einselection**); the model takes it as given.

**Gloss.** Before the σ-move can "objectify onto the classical fragment," there must be a fragment that
counts as classical. B1 is that choice. It is below the headline — none of A1–A3 mention a basis — but it
is genuinely load-bearing for the matrix-model readings, so it is named here rather than left implicit in
the definitions.

**Status.** `[posit; matrix model]`, and **`[open]`** as future work: *deriving* the preferred basis
(einselection — the pointer basis as the one the interaction leaves un-decohered) rather than positing it.
The development does **not** claim this derivation; it discloses the basis as an input.

**Role.** Fixes the referent of "diagonal / known" vs "off-diagonal / felt" throughout
[03.5](03.5-decoherence.md)–[03.9](03.9-band-coincidence.md). Strictly weaker than an axiom about selves:
it is a coordinate choice the model makes explicit.

---

# The theorems

The theorems that follow from this basis — **3.1** (to relate is to create), **3.2**
(lived identity and the "we"), **3.3** (knowing vs feeling) — together with the
structural results about relating (self, part, other, collection; routing vs directing;
what knowing does to a relation) live in their own file, with honest status tags and Lean
names: **[paper one](paper-one.md)**. The quantitative theorem (sparsity) is
[03.7](../archive/03.7-sparsity.md). Derived notions (self, distributed self, birth/death) are
collected in [paper one](paper-one.md) too.

---

## The residue — typed out, on the doctrine's own reading

Valence, the hard problem, and freedom are not unstated axioms. On the doctrine's own
reading they fall **outside what a structure-preserving functor expresses** — the language
speaks only of structure functors preserve, and these three are the non-structural
remainder. By 3.3, formalizing is itself the σ-move (the objectifying look that leaves a
remainder), so the language captures the *structure* of feeling (`≈`) and, on this reading,
not feeling-as-lived.

This is a **stance the doctrine takes, not a proved theorem**: there is no formal result that
these three are non-functorial (one cannot even state "valence" to prove it). Held as a
stance it is the program naming its own boundary; stated as a theorem it would overreach.

→ Continue to [paper one](paper-one.md): what follows from the basis (3.1–3.3 and the
structural results), including [03.7 — The Sparsity Conjecture](../archive/03.7-sparsity.md), the one
place the spec reaches for a genuine **theorem** rather than a redescription.
