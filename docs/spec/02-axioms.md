# 02 — The Axioms

> *The six commitments as sequents.* Each axiom is stated formally, tagged
> `[fragment; status]`, glossed against the plain-language view, and annotated with
> what it would take to discharge or use it. Together they cut the free theory on
> the [signature](01-signature.md) down to `𝕋`.

Throughout, `𝒞 = Cl(𝕋)`, `σ = Tr` is the self-relation operator, `γ` is the
symmetry, `Δ` the diagonal (cartesian fragment only), and `(R, ·, 1, ≤, β, c, ε)`
the attention data of [§1.3](01-signature.md).

---

## A1 — Relation primacy `[structural; both]`

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
in **A5** — `≡` will be exhibited as the bisimilarity `≈`, so that "same behavior in
all contexts" and "greatest bisimulation" coincide.

---

## A2 — Self-relation is feedback `[definitional; both]`

**Statement.**

$$
\sigma(P) \;:=\; \mathrm{Tr}(P).
$$

**Axiom.** The self-relating of a system *is* the trace of a relating on it — output
returned to input — and nothing more is meant by "the mind aware of the mind."

**Gloss.** The simplest relation is the self relating to itself: attention turned
inward, modeled as feedback. Because `Tr` needs no copying, this definition is
**fragment-neutral** and survives into the quantum fragment as the partial trace —
even though its *mirror* reading (A6) does not.

**Co-directed form.** Self-relation is the unary case (`Tr` over a private wire). When
the looped wire is *shared* between two systems, the same feedback is **co-directed** —
neither end closes the loop alone — and this is the engine of attention in
[§1.3](01-signature.md): the attention operator `Φ_c` is feedback through the coupling,
so co-direction is a consequence of the relating, not added to it.

**Role.** Pure definition; fixes the referent of `σ` used by A3, A4, A6, and the
co-directed `Φ_c` of A4.

---

## A3 — To relate is to create `[theorem; cartesian]`

**Statement.** In the cartesian fragment `𝒞_×`, the trace is a **Conway fixed-point
operator**; hence every feedback endomorphism `f : A × X → X` has a canonical fixed
point `f^† : A → X`, `f ∘ ⟨id, f^†⟩ = f^†`.

**Status: theorem.** This is the Hasegawa–Hyland correspondence
([00 §0.4.1](00-doctrine.md)) instantiated at `𝒞_×`; nothing new to prove, only to
*cite and apply*.

**Gloss.** Relating does not rearrange pre-existing pieces; under return it
*produces* a fixed point — a third thing that lives in the between and need not have
existed before. "To relate is to create" is the existence of `f^†`.

**Mechanized.** [`Scratch/Trace.lean`](../../formal/Scratch/Trace.lean) realizes the
Conway operator in the cartesian (complete-lattice) setting: `Tr f a := ν(f a)` with the
fixed-point identity `Tr_fixed` (`f a (Tr f a) = Tr f a`), the greatest-fixed-point
property `le_Tr` (coinduction), and naturality in the parameter `Tr_mono`. A2's
self-relation is the unary case `selfTrace P := νP` (`selfTrace_fixed`).

**Role.** Supplies the *existence* of fixed points that A4 then *selects among* by
resource. Note the division of labor: A3 says fixed points exist (cheap, cartesian,
theorem); A4 says only the budget-affordable, sufficiently-looped ones become
**selves** (expensive, the load-bearing posit).

---

## A4 — Recursion constitutes the self `[posit; both, with cartesian existence]`

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
points is underwritten by A3 and by Knaster–Tarski (`νΦ_c`); the *selection* — that
co-directed recursion under constitutive finiteness is what promotes a fixed point to
a self — is the new content. It is what stops the theory from being a universal
solvent.

**Gloss.** A relation builds a persisting self only when it loops — returned to,
re-entered, lived again until it holds. The decades-long friendship, the formative
parent, the work you keep choosing: built from relations *iterated*, not merely had.
Attention, co-directed and finite, is what shapes which loops close — and being
attended-to *raises* the attention one can give, so the self is sustained generatively,
not spent down.

**Role.** Everything discriminating about the theory routes through here. Drop A4
and the resource bound and *nearly everything* models `𝕋` (the triviality pole);
keep them and models thin out to the systems that actually stabilize selves. The
candidate theorem of [03](03-sparsity-conjecture.md) — **`Stab_R` is sparse under
finite `β`** — is the formal cash value of "a self is an achievement of recursion."

**Mechanized.** The defining condition `loop_R(e) = e` is now tied to the resource
threshold in Lean — [`formal/RelExist/Loop.lean`](../../formal/RelExist/Loop.lean)
proves `loop_R(e) = e ⟺ N(e) ≥ d(e) ⟺ d·λ ≤ β` (`loopR_isEigen_iff`), so A4's
fixed-point self and the counted threshold are provably the same condition.

---

## A5 — Observational identity and the "we" `[theorem given the ν-modality; both]`

**Statement.** Let `Θ` be the monotone operator on relations `R ⊆ D ⊗ D` whose
greatest fixed point is "indistinguishable under one step of every relating." Define

$$
{\approx} \;:=\; \nu\Theta
\qquad(\text{the greatest bisimulation}),
\qquad
\mathbb{E} \;:=\; D/{\approx}\ \ (\text{the shared world}).
$$

**Axiom + theorem.** `≈` exists as a final coalgebra (the `ν`-modality guarantees
it), and it **coincides with the contextual congruence `≡` of A1** — *behavioral
equivalence = greatest bisimilarity*. The quotient `𝔼` is the objective world as the
**overlap of perspectives**.

**The seam, kept open.** `𝔼` is **not terminal**: the overlaps do not collapse to a
single master perspective. Formally, the canonical map `D → 𝔼` is not split by any
global section that all states agree on; there remains an irreducible non-foundation
— the *seam* of §"We." We record this as a *required* property, not a defect:

> **Property 5.1 (irreducible seam).** There is no perspective `p : 𝔼 → D` with
> `(D → 𝔼) ∘ p = id_𝔼` natural in all relatings. The "we" is real (the quotient
> exists) and the gap inside it is real (no master section).

**Gloss.** Objectivity is not a god's-eye fact but the structure that survives being
looked at from everywhere it can be — agreement maintained across perspectives, an
ongoing social achievement. And the seam that never closes is the trace of each
perspective being genuinely separate, not a copy of one master view.

**Role.** Defines the shared world used by the death/persistence discussion
(distributed self = the part of `s` surviving in `≈`-neighbors after `s`'s own loop
opens) and supplies the *unobstructed* relation that A6 contrasts with `σ`.

---

## A6 — Knowing vs feeling `[both, with the σ-side cartesian]`

**Statement.** The two ways relation can turn are different *kinds of arrow*, and
their formal properties diverge exactly:

| | the **σ-move** (knowing) | the **≈-relation** (feeling) |
| --- | --- | --- |
| type | endomorphism `σ : D → D` (`= Tr`) | relation `≈ ↣ D ⊗ D` |
| fragment | **cartesian** (uses `Δ` to compare a copy) | fragment-neutral |
| obstruction | **Lawvere**: no complete self-model; leaves a **remainder** | none of this kind |
| character | local, partial, assembled, *from somewhere* | global, whole, all-at-once |

**Axiom.** `σ` is Lawvere-obstructed ([00 §0.4.2](00-doctrine.md)): there is a
fixed-point-free endomorphism witnessing that no state holds a total image of its
own self-relatings — *knowing leaves a remainder*. The relation `≈`, living one
type-level up and built coinductively rather than by copying, carries **no** such
obstruction — *feeling is whole*.

**Gloss.** To know is to make something an object held at a distance — the σ-move,
the diagonal — and that always leaves a remainder. A mood does not come in pieces;
it is present all at once with no vantage outside it. Knowing is local where feeling
is global; the asymmetry is the difference between relation turned **outward into
objects** (fragments) and **inward as presence** (does not).

**Mechanized.** The σ-side is [`RelExist/Mirror.lean`](../../formal/RelExist/Mirror.lean):
`lawvere` (a complete self-model forces a fixed point), `no_complete_selfModel` (a
fixed-point-free endomap ⇒ the mirror cannot close), and `selfModel_remainder` (the
diagonal family always escapes) — pure `Type`-level diagonal arguments depending on
**no axioms at all**. The contrast itself is
[`Scratch/KnowingFeeling.lean`](../../formal/Scratch/KnowingFeeling.lean):
`knowing_can_fail_to_close` / `no_complete_boolModel` (the σ-side is obstructed even in
one bit) versus `feeling_is_whole` (the `≈`-relation of A5 is reflexive — global, with
no remainder).

**Role.** Connects the doctrine's seam (0.6) to lived experience, and sets up the
honest limit recorded next.

---

## Derived notions and the residue

- **Self / eigenform**: a member of `Stab_R` (A4).
- **Distributed self**: for `e ∈ Stab_R`, its `≈`-image in `𝔼`; persists on the
  timescale of neighbors' returning even after `e`'s own loop opens (A5 + A4).
- **Birth / death**: a fresh fixed point forced into being already coupled (A3+A4
  with non-trivial initial coupling) / the loop `loop_R(e) = e` ceasing to hold as
  budget is withdrawn (A4 negated).

**The residue is typed out, not missing.** Valence, the hard problem, and freedom
are not unstated axioms; they are **outside what any structure-preserving functor
can express**, because the language speaks only of structure functors preserve, and
those three are the non-structural remainder. By A6, *formalizing is itself the
σ-move* — the objectifying look that leaves a remainder — so the language captures
the **structure** of feeling (`≈`) and *necessarily* not feeling-as-lived. The
formalism fails exactly where its own sixth axiom predicts. That is the program
confirming its thesis from the inside, not breaking.

→ Continue to [03 — The Sparsity Conjecture](03-sparsity-conjecture.md), the one
place the spec reaches for a genuine **theorem** rather than a redescription.
