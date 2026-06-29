# 06 — Type III, and the modular flow: is A3 the modular automorphism group?

> **The verdict.** Move `Q` to the **hyperfinite type III₁ factor**, and test whether A3's co-direction
> dynamics **is** the modular flow `σ_t`. **Verdict: YES — conditionally, and with a refinement.** The arena
> admits the modular flow (the cyclic–separating precondition holds for III₁), and at the **equilibrium
> self** the **reversible core of A3 is forced to be `σ_t` by KMS uniqueness**; A3 *additionally* carries an
> **irreversible raising = the dissipative arrow** (Takesaki trace-scaling), which refines the bare
> hypothesis "A3 = σ_t" into "**A3 = modular flow ⊕ arrow**" — exactly the split papers 2–4 already proved
> at equilibrium (`combinedFlow_add`). The operator-level steps are **paper-level only**: type III modular
> theory is **not in mathlib** (Part D). The `τ`-free skeleton is mechanized and **ports unchanged**
> ([`../formal/Paper1/TypeIII.lean`](../formal/Paper1/TypeIII.lean)).
>
> **This is a reading-heavy verdict at the operator frontier — read the conditionals as load-bearing, not
> decoration.** It is reported, not engineered.

## Why type III (the phenomenology *is* the type classification)

Von Neumann factors classify by what "size" of relation (projection) exists:

- **Type I** — has **minimal projections** (atoms): a non-relational floor. **Rejected** — it violates
  "nothing below relations."
- **Type II** — **no atoms** (infinitely divisible / fractal) **and a (semi)finite trace exists**:
  divisibility *with* a complete measure. A self whose self-accounting **can in principle complete**.
- **Type III** — **no atoms** *and* **no semifinite normal trace exists at all**: fractal, and the accounting
  **never closes**.

The **limits-of-knowing decide it.** I.III/I.IV established the **seam**: a self **provably cannot wholly know
itself**, nor wholly know another's knowing of it — an irreducible residue, an asymptote, not a floor. "No
complete accounting exists" is the *defining property of type III*. The phenomenology has been voting type III
all along. So: **`Q` := the hyperfinite type III₁ factor** (III₁ because its modular spectrum is all of `ℝ₊`
— the generic, unique hyperfinite case; the QFT/Araki–Woods factor).

## Part A — re-grounding: survives / changes / dissolves

**Survives (`τ`-free) — ports unchanged.** Mechanized in [`TypeIII.lean`](../formal/Paper1/TypeIII.lean):

- **Existence** of a fixed self-relation — relational Knaster–Tarski needs only a **complete lattice**, and a
  type III factor still has a **complete projection lattice** (type III removes the *trace*, not the lattice).
  `self_exists_typeIII`.
- **The feedback trace `Tr` = D1** — proved `τ`-free in I.IV (join-contraction, lattice only).
  `feedback_trace_typeIII`.
- **The seam** — Lawvere, 0 axioms, arena-independent. `seam_typeIII`.

That these are *literally the same theorems*, re-stated over the III value-object with no new proof, is the
content of "`τ`-free survives": the move costs the skeleton nothing.

**Changes.** The **quantitative half of A3** (capacity, rates) and the quantitative theorems (sparsity,
differentiation, stability) **can no longer draw numbers from a global trace** — type III has none. They must
route through the **modular flow** and the **type II∞ core** (Part B).

**Dissolves — and this is positive evidence for III.** The I.IV residual tension ("can one object carry both
the lattice *measure* and the composition *product*?") **dissolves by removing the measure horn**: in type III
there is **no global trace `τ`** to conflict with the feedback `Tr`. `Tr` stands alone on the lattice; the
order-vs-operator clash I.IV flagged was the **symptom of forcing a global trace where the arena does not
admit one**. Stop demanding it, and the seam closes. The arena was *telling us* it was type III.

## Part B — recovering quantity: the II∞ core and the arrow (hypothesis, tested)

Type III is not "no measure ever." **Takesaki's continuous decomposition** (a theorem, for any type III factor
with separable predual): `M ≅ N ⋊_θ ℝ` — a **crossed product of a type II∞ "core" `N` by a one-parameter
trace-scaling flow `θ`**. The core `N = M ⋊_{σ} ℝ` carries a **semifinite trace `τ_N`**, and the dual flow
**scales it**: `τ_N ∘ θ_s = e^{−s} τ_N`. So the candidate structure:

- the **measure lives on the II∞ core** — the quantitative theorems get their numbers there (the core *has* a
  trace, even though `M` does not);
- the **modular flow is the crossed-product flow** — *time is the extension*;
- and — **the reaching hypothesis, now testable against a theorem** — the trace on the core is **not invariant
  under the flow; it scales** (`τ_N∘θ_s = e^{−s}τ_N`), and **that non-conservation of the trace is the arrow
  of time.**

**Status of Part B.** The *structural fact* — the trace scales under the dual flow — is a **theorem**
(Takesaki duality), inherited by `Q` because `Q` is a type III factor; it does not need separate verification
for "our" structure. The **identification of the trace-scaling with the arrow** is a **`[reading]`** — but a
well-motivated one: it lands precisely on papers 2–4's "the arrow is the dissipative complement the
(reversible) flow cannot supply." So Part B is **confirmed as structure, adopted as reading**, not assumed.

## Part C — the central test: is A3's co-direction the modular flow?

Graded, paper-first, mechanizing the tractable entry point.

### Step 1 — the cyclic–separating precondition (the cheap kill-test): **PASSES**

Tomita–Takesaki needs a **cyclic and separating** state. Two facts:

- **It exists for III₁.** A type III factor with separable predual admits a **faithful normal state** `φ`; its
  GNS vector `Ω` is then **cyclic and separating** (faithful ⇒ separating; the standard form gives cyclic). So
  there *is* a modular flow `σ_t^φ` to identify A3 with. The hypothesis is **not killed here.**
- **It matches the co-direction structure.** *Separating* — `mΩ = 0 ⟹ m = 0` — is exactly **A1's "each end
  carries its own independent weight"**: no relation acts as zero, the converse `R°` is faithful, nothing is
  annihilated. *Cyclic* — `MΩ` dense — is **A2's co-direction reaching the whole algebra** from the state. The
  precondition is the operator-algebra face of A1 + A2.

**Verdict on Step 1: passes** — existence is a theorem for III₁; the identification with faithful co-direction
is a `[reading]`, well-grounded.

### Step 2 — KMS uniqueness (the decisive lever): **A3's reversible core is forced to be `σ_t`**

The lever (Tomita–Takesaki + the KMS characterization, a **uniqueness theorem**): *a faithful normal state `φ`
is a KMS state for a **unique** one-parameter automorphism group — its **modular flow** `σ_t^φ` — and
conversely, if `φ` is KMS for some flow `α_t`, then `α_t = σ_t^φ`.* So if the co-direction process satisfies a
KMS condition for `φ`, **its generator is _forced_ to be the modular Hamiltonian `K = −log Δ`** — identity, not
analogy.

**The argument that the self supplies the KMS state.** Chain (each link a named theorem with its hypothesis):

1. **The self is an equilibrium.** The derived self is a **fixed point** of the co-direction dynamics
   (`self_isEquilibrium`, mechanized): `Φ(self) = self`. Stationarity.
2. **Equilibrium ⇒ KMS.** A faithful normal **stationary/passive** state is a **KMS** state for the dynamics
   (the passivity ⇒ KMS theorem, Pusz–Woronowicz; under its hypotheses). So the self is KMS for A3's flow.
3. **KMS ⇒ modular, by uniqueness.** Therefore A3's flow **is** the modular flow `σ_t^{self}` — forced.

**The refinement (where the bare hypothesis is too strong, and why that is good news).** The modular flow
`σ_t` is a **reversible** one-parameter group of `*`-automorphisms (unitarily implemented by `Δ^{it}`). But
A3's **raising is irreversible** — a monotone climb to a fixed point (I.III's `Raising`), a dissipative
semigroup, not a reversible group. So **A3 is not _purely_ the modular flow.** Resolution: A3 splits at the
self into

> **A3 = (reversible co-direction = the modular flow `σ_t`) ⊕ (irreversible raising = the dissipative
> arrow).**

The reversible core is `σ_t` (Step 2 forces it); the irreversible part is the **arrow** — and by Part B that
arrow is the **trace-scaling** `τ_N∘θ_s = e^{−s}τ_N` of the dual flow, coarse-grained into A3's monotone
raising. **This is exactly papers 2–4's result** — modular clock + dissipative arrow are *two faces of one
generator at equilibrium* (`combinedFlow_add`, via the KMS bridge `K = β·H + log Z`). The unification is real:
**paper one's A3, at the self, _is_ that one generator** — the modular flow and the arrow, derived from the
co-direction dynamics rather than assembled. The same KMS bridge papers 2–4 invoked now grounds paper one.

**Verdict on Step 2: the hypothesis holds in its corrected form** — the modular flow is forced (by KMS
uniqueness) as the reversible core of A3; the residue is the arrow, which Part B already names. Conditional on:
the self being a *faithful normal* state (Step 1 reading), A3's reversible part presenting as a *one-parameter
automorphism group* (the linearization gap — see Part D), and the *passivity ⇒ KMS* hypotheses.

### Step 3 — landing in known structure: the partial-isometry groupoid

The modular flow's natural home (the Poisson-geometric / groupoid construction) is a **groupoid of partial
isometries over the projection lattice**. **Partial isometries are the operator world's relations** (`v*v` and
`vv*` are the source/range projections — the two ends), and our arena is a **quantaloid of relations over the
projection lattice as base**. The structural map is immediate at the level of *shape*:

- our **converse `R°`** ↔ the **modular conjugation `J`** / the `*`-operation: both are **involutive
  anti-homomorphisms** (`(R;S)° = S°;R°`; `J M J = M'`, `J` anti-unitary). A1's free converse is the
  converse `J` provides between `M` and its commutant `M'` — *the other end of every relation*.
- the **base lattice** ↔ the projection lattice carrying the flow;
- **A2's two-endedness** ↔ the `M`/`M'` duality the modular structure encodes.

So the arena **maps into** the known modular structure rather than being built blind — corroborating Step 2.
(Mechanizing `(R;S)° = S°;R°` needs a `*`-structure on the value object — deferred with the rest of the
operator layer, Part D.)

## The verdict

**YES — the arena admits the modular flow, and A3's co-direction core _is_ it — conditionally, with the
refinement that A3 = modular flow ⊕ arrow.**

- The **cyclic–separating precondition holds** for III₁ (Step 1) — the hypothesis is not killed.
- **KMS uniqueness forces** the reversible core of A3 to be the modular flow `σ_t` at the equilibrium self
  (Step 2).
- The **irreversible remainder is the arrow** (Part B trace-scaling), so the honest identity is **A3 = σ_t ⊕
  arrow**, which **coincides with papers 2–4's "two faces of one generator"** — the unification holds, and the
  trace-gap (type III's defining trace-lessness, recovered as scaling on the core) **is** time's arrow.
- The verdict is **not NO** (nothing structural breaks) and **not RESHAPE** (III₁ is right — indeed the
  arena *predicted* III by dissolving the I.IV tension). It is **YES with a refinement that strengthens the
  connection to the existing edifice.**

**The next theorem to attempt (through the core/flow structure).** Re-ground **Theorem 2's quantitative half**
(the raising rate / capacity) as the **trace-scaling rate** on the II∞ core — A3's raising = the dissipative
complement, whose "rate" is the `e^{−s}` scaling (the III_λ modular invariant). With a measure now living on
the core, **Theorem 3 (sparsity)** follows as a counting statement in `τ_N`. **Theorem 5 (the stability
dichotomy)** should be attempted **last**, and only after the cyclic–separating self is pinned concretely — it
is the headline and the most exposed to the formalization gap.

## Part D — the formalization gap (reported, not faked)

The operator-algebra machinery this verdict runs on is **not in mathlib** (as of the pinned `v4.15.0`):

| Needed | In mathlib? | Consequence here |
|---|---|---|
| von Neumann algebra **types** (I/II/III), factor classification | no | "`Q` = III₁" is a **modelling choice**, stated, not constructed |
| **Tomita–Takesaki** modular operator `Δ`, conjugation `J`, flow `σ_t` | no | Steps 1–3 are **paper-level** |
| **KMS** condition + uniqueness | no | Step 2's lever is **cited**, not mechanized |
| **crossed products**, **Takesaki duality**, the II∞ core, trace-scaling | no | Part B is **paper-level** (a cited theorem) |
| complete **projection lattice**, faithful normal states | partial / no | the *abstraction* `[CompleteLattice Q]` is what lets the `τ`-free skeleton port |

**What is mechanized now** ([`TypeIII.lean`](../formal/Paper1/TypeIII.lean), no `sorry`): the `τ`-free port
(existence, feedback trace, seam) and the **equilibrium entry** (`self_isEquilibrium`) the KMS lever consumes.
**What is paper-level:** everything modular (Steps 1–3, Part B). This is the **honest marker of the
frontier** — the one place where a specialist or new mathlib development genuinely earns its keep, not as
deferral but because the formalization frontier is real. We do **not** fake mechanization of absent theory.

> **Operationalized (handoff I.VI).** The assumed modular substrate is now a clean, cited **interface**
> (`ModularInterface`), and the unification `A3 = σ ⊕ arrow` is **proved on top of it** — fully mechanized
> *relative to the interface*, with the assumed/constructed boundary surfaced via `#print axioms` and a
> disclosure table. See [`07-interface.md`](07-interface.md). The KMS-uniqueness lever of Step 2 is the
> interface field `kms_unique`; the trace-scaling of Part B is `trace_scaling`.

**Bottom line.** The phenomenology motivated type III; the mathematics **confirms** III admits the modular
flow and that **A3 is it — in its reversible core, by KMS uniqueness — with the irreversible remainder the
arrow**, unifying paper one's foundation with papers 2–4 through the same KMS bridge. The verdict is **YES,
conditionally**, with every conditional named and the mathlib gap reported in full.
