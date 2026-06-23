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

The full traced-symmetric-monoidal `Cl(𝕋)` is now a genuine Lean object — the free traced
SMC on a signature, with its universal functor (§4.6). The domain functors below are also
exhibited directly at the level of **operative content** — the eigenform/`gfp` structure
(A2–A5) and the cartesian copy/Lawvere structure (A6) — which is what makes each one a
*one-line* theorem (§4.3, §4.8, §4.9).

## 4.2 The domains, with verdicts

| Domain | Target | Verdict | Status |
| --- | --- | --- | --- |
| **Physics (quantum)** | `FGModuleCat`/`FdHilb`; `Tr` = partial trace, co-determination = entanglement | **literal traced-SMC functor** (`matTracedSMC`) — redescriptive, not predictive; the distinctive fact is **no-cloning** | ✅ **literal instance + no-cloning** (§4.5–4.6) |
| **Chemistry** | reaction networks (Baez–Pollard); autocatalytic sets = looped eigenforms | **strong, near-literal** — best non-quantum fit | ✅ **mechanized** (§4.3) |
| **Biology** | Rosen relational biology / (M,R)-systems | **strong, with an ancestor** — closure to efficient causation = a looped eigenform | ✅ **mechanized** (§4.9) |
| **AI** | semantics of recurrence; Geometry of Interaction *is* traced categories | design-principle functor — feedback **is** the trace | ✅ **mechanized** (§4.8) |
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

This axiomatizes compact closure minimally (the dual adjunction) rather than routing through
the full traced SMC; mathlib has symmetric/braided/**rigid** monoidal categories and
`ChosenFiniteProducts`, but no traced-monoidal or compact-closed typeclass — so the traced
SMC structure, the concrete models, and the free traced SMC `Cl(𝕋)` are all built from
scratch here (§4.6).

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
- **The partial trace** ([`Scratch/PartialTrace.lean`](../../formal/Scratch/PartialTrace.lean)):
  the doctrine's `Tr` *is* the QM partial trace `ptrace M i j := ∑ k, M (i,k) (j,k)`, and
  it is proved to satisfy **all three JSV wire axioms** — **naturality** (`ptrace_nat_left`,
  `ptrace_nat_right`), **sliding** (`ptrace_slide`), **yanking** (`ptrace_swap`: `Tr(σ) =
  id`) — plus linearity, **vanishing-II** (`ptrace_prod`), and full-trace compatibility
  (`trace_ptrace`). These assemble into a literal `FdHilb`/`FGModuleCat`-style `TracedSMC`
  instance — **`matTracedSMC`** (§4.6) — with the associator-as-reindexing coherence for the
  retensoring axioms supplied by permutation matrices. **The physics functor is now literal.**

So the physics/cartesian seam (no-cloning vs free copying) — the doctrine's [§0.6
seam](00-doctrine.md) and the firewall — is now a theorem on both sides.

## 4.6 The traced SMC typeclass, the free category `Cl(𝕋)`, and literal functors

What were once the two research-grade frontier pieces — a real traced-SMC typeclass and a
literal functor out of the free traced SMC — are now **fully built** in
[`formal/RelExist/Traced.lean`](../../formal/RelExist/Traced.lean) and
[`formal/RelExist/Free.lean`](../../formal/RelExist/Free.lean) (axiom-free / `Quot.sound`-only,
fully constructive), together with the monoidal-coherence refinement and a concrete matrix
model. The progression, in order of strength:

**Done:**

- **A traced symmetric monoidal category typeclass** — `TracedSMC`, with associator and
  unitor isomorphisms (morphism data) and the **full Joyal–Street–Verity axiom set**:
  naturality (left/right), sliding (dinaturality), yanking, **vanishing-I** (trace over
  the unit), **vanishing-II** (trace over `U ⊗ V` = nested traces), and **superposing**
  (trace commutes with `W ◁ -`). Adding the structural isos as morphisms is what makes the
  retensoring axioms statable transport-free. mathlib has no such typeclass.
- **It is non-vacuous and the axioms are validated** at three strengths: the trivial
  one-object model (`trivialTracedSMC`, consistency by `rfl`); a commutative monoid
  (`scalarTracedSMC`) in which **sliding holds *exactly because* `·` is commutative**; and
  — fittingly for *relational* existentialism — **`Rel`, the category of sets and
  relations** ([`Scratch/Rel.lean`](../../formal/Scratch/Rel.lean), `relTracedSMC`), a
  genuine **multi-object** model with `⊗ = ×` and the relational trace
  `(trace R) x y := ∃ u, R (x,u) (y,u)`, which validates the **full** axiom set —
  including the retensoring axioms — *non-trivially*.
- **Literal functors** — `TracedFunctor` is a real structure-preserving map (a *model* in
  the Layer-4 sense), with `TracedFunctor.id`, `TracedFunctor.toTrivial`, and
  `TracedFunctor.comp`. The last makes functorial semantics genuinely *functorial*:
  models compose.
- **A literal functor out of a free object** (`TracedFunctor.fromFreeScalar`). The scalar
  fragment of the free traced SMC on one object — `End(I)`, the endomorphisms of the unit —
  is the **free commutative monoid on one generator**, i.e. `(ℕ, +)`. This *is* buildable
  concretely, with its **universal property**: `natCMon.lift B b` is the unique monoid
  homomorphism sending the generator `1` to a chosen `b : B`, and `natCMon.lift_unique`
  proves uniqueness (every hom out of `ℕ` is such a lift — *axiom-free*, not even
  `propext`). Packaged through `TracedFunctor.ofCMonHom` (a traced functor from any monoid
  homomorphism, since a commutative monoid is a one-object `TracedSMC` via
  `scalarTracedSMC`), this yields a genuine **literal functor out of a free object**,
  determined precisely by *where the generator (the loop/dimension `δ`) is sent*. That is
  the functorial-semantics ideal — a model is fixed by the image of the generators — in
  its smallest honest instance.
- **The multi-color form** (`TracedFunctor.fromFreeCMon`). The one-generator result extends
  to `k` generators: `ℕᵏ` is the **free commutative monoid on `k` generators** (the scalar
  fragment of the free traced SMC on `k` objects/colors), built by prepending one free
  generator at a time (`freeCMon`). Its full universal property is mechanized — existence
  (`freeCMon.lift`: a tuple `(n₀,…,n_{k-1})` is sent to `g₀^{n₀}·…·g_{k-1}^{n_{k-1}}`) and
  **uniqueness** (`freeCMon.lift_unique`: every homomorphism out of `ℕᵏ` is the lift of the
  images it assigns to the generators) — both **fully axiom-free** (not even `propext`). The
  step that makes a *tuple* of independent generators combine coherently is the middle-four
  interchange `(ab)(cd) = (ac)(bd)`, which holds *exactly because* the monoid is commutative
  — the same commutativity that drives sliding. So a model out of the free scalar object on
  any finite number of colors is determined, constructively, by where its generators go.

**Now also done — the literal matrix instance.** `matTracedSMC`
([`Scratch/MatrixModel.lean`](../../formal/Scratch/MatrixModel.lean)) is a genuine
`TracedSMC` whose **objects are finite types, morphisms are matrices, `⊗` is the Kronecker
product, and the trace *is* the quantum partial trace** `ptrace`. Five of the seven JSV trace
axioms are exactly the `PartialTrace` lemmas (naturality, sliding, yanking); the two
**retensoring** axioms (vanishing-II, superposing) are discharged by realising the
associators as honest **permutation matrices** (`permMat` of `Equiv.prodAssoc`) and proving
the reindexing lemmas `permMat_mul` / `mul_permMat`. This makes the **physics functor
literal**, not content-level — the doctrine's `Tr` is, on the nose, the partial trace of
categorical quantum mechanics. (Axioms: the standard mathlib three; `sorry`-free.)

**Now also done — the full free traced SMC `Cl(𝕋)` and its universal functor.**
[`RelExist/Free.lean`](../../formal/RelExist/Free.lean) builds the **free traced SMC on a
signature** `(C, G)` (colors and generating morphisms) as a genuine Lean category and the
**literal universal functor** out of it:

- `Obj C` — objects freely generated from colors by `⊗`/unit; `Term` — morphism syntax
  freely generated by `id, comp, ⊗, braid, trace` and the structural isos; `Rel` — the
  congruence generated by **exactly the `TracedSMC` equations** (category laws, iso
  round-trips, the seven JSV trace laws — *and no more*: pentagon/triangle/hexagon are not
  imposed, just as the typeclass omits them);
- `clTracedSMC : TracedSMC` — **`Cl 𝕋 := Quot Rel` is itself a traced SMC**: every operation
  descends to the quotient and every axiom holds because its `Rel` generator equates the two
  sides;
- `functor : TracedFunctor (Cl 𝕋) 𝒟` — **the universal (literal) functor**: a model of the
  signature in any `𝒟` (a reading `ιC` of colors, `ιG` of generators) extends to a genuine
  traced functor out of `Cl 𝕋`, with objects and all structure preserved and the morphism map
  the interpretation descended through the quotient;
- `functor_unique` — **uniqueness**: any structure-preserving map agreeing with `ιG` on the
  generators *equals* `functor`'s map. So `Cl 𝕋` is genuinely **free** — `(ιC, ιG)`
  determines the traced functor uniquely.

The whole construction's only axiom is **`Quot.sound`** (the defining law of quotients —
not `propext`, not choice); `interp_respects` (that the interpretation respects every
equation) is **fully axiom-free**.

**Now also done — the monoidal-coherence layer.** The coherence equations the bare
`TracedSMC` deliberately omits are layered back on as a refinement
`CoherentTracedSMC extends TracedSMC` ([`RelExist/Coherence.lean`](../../formal/RelExist/Coherence.lean)),
carrying the eight standard symmetric-monoidal laws — naturality of the associator and both
unitors, the **pentagon** and **triangle**, naturality of the braiding, its **symmetry**
(`σ∘σ = id`), and the **hexagon**. It is non-vacuous and validated at three strengths: the
trivial model (axiom-free), the **scalar** model (each law reduces to a commutative-monoid
identity — associativity for the associator laws, commutativity for the braiding laws), and —
the real check — **`Rel`** ([`Scratch/RelCoherence.lean`](../../formal/Scratch/RelCoherence.lean),
`relCoherentTracedSMC`) and the **literal matrix model**
([`Scratch/MatrixCoherence.lean`](../../formal/Scratch/MatrixCoherence.lean),
`matCoherentTracedSMC`), both genuine **multi-object** models in which all eight coherence
laws hold. For the matrix model the engine is the *functoriality of permutation matrices*
(`permMat (e ∘ e') = permMat e · permMat e'`, `permMat e ⊗ₖ permMat e' = permMat (e ×' e')`),
which turns the pure-permutation laws (pentagon, triangle, symmetry, hexagon) into equalities
of `Equiv`s that hold by computation. So coherence is a first-class, validated refinement; it
sits *above* the trace, exactly as the doctrine claims (the JSV axioms never reference it).

**And the free coherent object.** [`RelExist/FreeCoherent.lean`](../../formal/RelExist/FreeCoherent.lean)
builds `Cl_coh 𝕋`, the **free `CoherentTracedSMC`** on the signature: the syntax quotiented by
`CohRel` — the bare congruence `Rel` (embedded via `ofRel`) *plus* the eight coherence
equations — is a coherent traced SMC (`clCoherentTracedSMC`), with the universal functor
`functorC` into any coherent model (the bare `interp_respects` discharges the embedded steps,
`𝒟`'s coherence fields the rest). So **both** free objects now exist: the bare `Cl 𝕋`
(doctrine-faithful — the trace needs no coherence) and the coherent `Cl_coh 𝕋`. Both are
`Quot.sound`-only.

## 4.7 What this layer shows

- The **expressivity/triviality dial** in action: the chemistry functor *exists* and is
  near-literal (the theory says something real about autocatalysis); the social-domain
  entanglement functor *does not typecheck* (the theory refuses an overclaim by
  construction). The firewall is enforced by the type system, not by willpower.
- It also confirms the **residues** sit outside the language: a functor preserves only
  structure, and valence / the hard problem / freedom are precisely the non-structural
  remainder — so no functor reaches them, exactly as [A6](02-axioms.md) predicts of the
  σ-move that formalizing itself is.

## 4.8 AI — recurrence is the trace (mechanized)

The AI verdict is a **design-principle functor**: the *Geometry of Interaction* is the
mathematics of traced categories, and the semantics of recurrence **is** feedback through a
hidden wire. In [`formal/Scratch/Recurrence.lean`](../../formal/Scratch/Recurrence.lean) this
is made literal by *reusing the doctrine's own structure*, not re-deriving it:

- **Feedback = the trace.** A recurrent system `step : (input × state) → (output × state)`
  loops its hidden `state` back. Its observable behaviour is `feedback step := rtrace step`,
  and `feedback_eq_trace` proves this **is** the trace of `Rel` (§4.4/[`Rel.lean`](../../formal/Scratch/Rel.lean))
  *definitionally*. The GoI "execution formula" — input `i` produces output `o` exactly when
  some hidden state is **self-consistent** (`step (i,s) (o,s)`, the wire fed back unchanged)
  — is `feedback_iff`, true by `rfl`.
- **Sustained recurrence = the eigenform `ν`.** State dynamics `next : state → state` induce
  a monotone "can-keep-going" operator `recurOp`; its **greatest fixed point**
  `sustained := ν(recurOp)` is the set of states on an unbounded orbit — the net's persistent
  activity. This is the *same* `OrderHom.gfp` ν-modality as `≈` (We) and attention, with
  coinduction (`sustained_greatest`) and `selfLoop_sustained` (a fixed point of the dynamics
  recurs forever).
- **The bridge.** `selfConsistent_sustained`: a self-consistent hidden state realising the
  feedback is a *sustained* state of the induced dynamics — so the **looped self of the
  theory (a self-trace fixed point) maps to persistent recurrence in the AI domain**, and
  `feedback_witnessed_by_sustained` packages it: observable feedback is witnessed by a
  sustained eigenform. Trace ⟶ feedback and `ν` ⟶ sustained activity, both *received with
  nothing bolted on* — which is exactly what "design-principle functor" means.

## 4.9 Biology — Rosen's (M,R)-systems and closure to efficient causation (mechanized)

The biology verdict is "**strong, with an ancestor**": Robert Rosen's *metabolism–repair
(M,R) systems* anticipate the doctrine's looped self. An organism is **closed to efficient
causation** — it fabricates all its own parts, *including its own maintainers* — an
impredicative self-closure that is precisely a greatest fixed point. In
[`formal/Scratch/Biology.lean`](../../formal/Scratch/Biology.lean):

- Unlike chemistry's single production operator, an `MRSystem` **couples two** monotone
  operators — `metabolize` (what present components make) and `repair` (what regenerates the
  makers) — and `fabricate := repair ∘ metabolize` is their composite.
- `organism := ν(fabricate)` is the maximal self-fabricating whole, with `organism_closed`
  (fixed point) and `organism_greatest` (coinduction). `mr_cycle_closes` is the two-operator
  heart: the organism is **repaired from its own metabolites**.
- `closed_to_efficient_causation` — a component the system fabricates *from itself alone* lies
  in the organism: the efficient cause of its own maintenance is **internal**, Rosen's
  defining property, as a one-line consequence of coinduction.
- `selfTrace_eq_organism` — **the functor, witnessed**: the theory's self-trace (`νP`, A2) of
  the fabrication operator *is* the organism, definitionally — a looped self maps to a
  self-fabricating organism.

The impredicative "the repairer is itself repaired" is the same self-reference the
[mirror](../../formal/RelExist/Mirror.lean) makes precise on the σ-side — biology as the
**ancestor** of the doctrine's self-modelling. With this, **all five domains** of the plan
(physics, chemistry, biology, AI, and the social/mental-health firewall) are mechanized.

## 4.10 Decoherence — the quantum→classical retraction (mechanized, concrete)

The firewall (§4.4) is a *binary*: a domain is cartesian (copyable) or compact (entangleable),
never both. But the **passage** between them — how the classical fragment arises *inside* the
relational whole — is not binary, it is graded, and it has a name: **decoherence**. This is
mechanized concretely inside the literal matrix model
([`Scratch/Decoherence.lean`](../../formal/Scratch/Decoherence.lean)), with the standard
basis as the **classical structure**.

| Result | Lean name | Meaning | State |
| --- | --- | --- | --- |
| **decoherence** — kill the coherences | `RelExist.Decoherence.dephase` | keep the diagonal, zero the off-diagonal (the basis-induced retraction) | ✅ defined |
| the **classical fragment** = diagonal states | `IsClassical` / `isClassical_iff_diagonal` | the copyable, broadcastable states are exactly the diagonal ones | ✅ proved |
| decoherence is a **retraction** | `dephase_eq_self_iff` / `dephase_idem` / `trace_dephase` | idempotent, trace-preserving, fixes exactly the classical fragment | ✅ proved |
| **copyability ⟺ commutativity** | `isClassical_mul` / `classical_comm` | the classical fragment is closed under composition *and commuting* — the no-broadcasting fault line, concretely | ✅ proved |
| **copy-defect** — the continuous knob | `copyDefect` / `copyDefect_eq_zero_iff` | the off-diagonal mass; `= 0` ⟺ classical (the dial from feeling to knowing) | ✅ proved |
| a **numeric magnitude** | `defectSq` / `defectSq_eq_zero_iff` / `defectSq_nonneg` | squared off-diagonal mass: `0` exactly on the classical fragment, positive otherwise | ✅ proved |
| the fragment is **proper** | `plus_not_classical` / `dephase_plus_ne` / `defectSq_plus_pos` | a witnessed superposition (`|+⟩⟨+|`) has positive defect; decoherence loses information — the concrete face of `no_cloning` | ✅ proved |

So the cartesian/compact binary of `Compact.collapse` is refined, *inside* a genuine traced
SMC, into a **graded retraction**: decoherence `dephase` projects the relational whole onto a
proper classical fragment, the **copy-defect** measures continuously how far a state is from
being copyable (zero iff classical, positive on a superposition), and "copyable ⟺ commuting"
makes the no-broadcasting fault line literal. This is the structural shadow of the
quantum→classical passage — `sorry`-free, axiom footprint `propext`/`Classical.choice`/`Quot.sound`.
(The abstract form — a `ClassicalStructure` on a dagger-SMC, with decoherence a functor onto
the cartesian sub-fragment — is the typeclass-level companion to this concrete instance.)
