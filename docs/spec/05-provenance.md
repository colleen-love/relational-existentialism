# 05 — Provenance Ledger

> Part of the [Formalization Spec](README.md). *The honest accounting a referee reads first.* Every
> other page argues the theory; this one states, per result, **what is rederived, what is synthesis,
> and what (if anything) is novel** — and names the genuinely open bridges so they are found here, by
> us, rather than on page one of a review.

---

## 0. The one-sentence claim

> The **mathematical content** of this development is, almost entirely, **rederivation** of established
> results (bisimulation, Lawvere, traced monoidal categories, the graph model, the partial trace,
> Rosen, Banach/Neumann series). The **contribution** is a **synthesis** — a single typed identification
> across decoherence, fixed-point logic, and relational dynamics — together with a set of philosophical
> **readings** mounted on theorems, and the **mechanization artifact** itself (a sorry-free, axiom-audited
> Lean+Agda corpus). The one place a *candidate-novel mathematical theorem* lived — whether the seam
> bites the **quantum partial trace specifically** — is now **resolved** (Bridge B, §4): the seam bites
> the genuine `ptrace` on the **compact/no-broadcasting face**, and the cartesian/Lawvere face (route 1)
> is shown *firewall-obstructed*, not merely unbuilt. The resolution is a synthesis on standard pieces
> (non-injectivity of `ptrace`, no-broadcasting, the firewall), not new mathematics.

This is deliberately the *deflationary* reading. We would rather under-claim here and have the synthesis
and the artifact carry the weight than overclaim a theorem and have a reviewer find the seam unmarked.

---

## 1. The three tiers

| Tier | Meaning | What it would take to be more |
| --- | --- | --- |
| **R — Rederivation** | The theorem is established mathematics; we re-prove it (often in a proof assistant, sometimes in a lighter special case) to have it *inside* the corpus with an audited axiom footprint. Novelty: ~0; value: the machine-checked artifact and the uniform setting. | A new theorem, not a re-proof. |
| **S — Synthesis** | No single new theorem, but a non-obvious **identification** or **transport**: the same structure recognized across two domains the literature keeps apart, so that a known fact in one becomes a statement in the other. Novelty: the bridge, not the endpoints. | Showing the identification is *forced* (an equivalence/obstruction), not merely *available*. |
| **N? — Novel-candidate** | A statement that, if it holds at the claimed generality, is not a re-proof of anything we can cite. In this corpus these are now **only** philosophical readings (explicitly lenses, not proofs of the world); the one *mathematical* candidate — the quantum-seam question (Bridge B) — has been **resolved** (§4) as a firewall dichotomy, i.e. as synthesis, not a new theorem. | Nothing further (the readings are honest as readings; Bridge B is settled). |

A result can be **R in content, S in framing**: the theorem is old, the recognition that it *is* this
phenomenon is the contribution. Most of the corpus is exactly this. We mark such rows `R / S`.

---

## 2. The ledger

Grouped by area. "Prior art" cites the result being rederived or transported; it is representative, not
exhaustive. Lean/Agda names are the audited artifacts (see [`formal/README.md`](../../formal/README.md)).

### 2.1 Identity, bisimulation, the first-person surplus

| Result | Prior art | Tier | Note |
| --- | --- | --- | --- |
| `≈ := νΘ`, coinduction, `≈` an equivalence, shared world `D/≈` | Park, Milner (bisimulation); Aczel (non-well-founded sets); Rutten (universal coalgebra) | **R** | Lean via `OrderHom.gfp` (Knaster–Tarski); Agda via native final-coalgebra copatterns — two independent mechanizations agreeing. |
| `≈ ⊊ ≅` (lived exceeds observed); `≅` observational/trace equivalence | van Glabbeek (linear-time/branching-time spectrum); Hennessy–Milner | **R / S** | The theorem is the spectrum's standard strict inclusion. *Synthesis:* reading the surplus as the **first-person remainder**. |
| `Deterministic ⟹ (≈ ⟺ ≅)` — the surplus *is* branching | Folklore of the spectrum (determinism collapses the hierarchy); Hennessy–Milner under determinism | **R / S** | Mechanized both assistants. *Synthesis:* "you exceed how you appear" is, exactly, a fact about systems that *could have done otherwise*. |
| Relational appearance `≅ₒ` (an other's marginal of you); `≈ ⊆ ≅ ⊆ ≅ₒ`; deterministic *relational* surplus | Coarser-than-observation equivalences are standard; the marginal/quotient is elementary | **S** | The move that corrects the "view from nowhere": the operative outside is a *coupled other*, and a **deterministic** system still has surplus against it (feeling from finite access, not from branching). |

### 2.2 Knowing, the mirror, the seam (Lawvere)

| Result | Prior art | Tier | Note |
| --- | --- | --- | --- |
| Lawvere diagonal; no complete self-model; remainder | Lawvere (1969); Yanofsky (survey) | **R** | Core, **0 axioms** — fitting, since incompleteness is the contrapositive of a one-line diagonal. |
| No reflexive object in Set/finite (Cantor); the obstruction for `Bool` | Cantor; Lawvere | **R** | `no_reflexive_object_for_Bool`, **0 axioms**. |
| The seam: `self_cannot_trace_relation` — the one trace a self can't take on itself | Lawvere, specialized | **R / S** | The *theorem* is Lawvere at `Env = Self`. *Synthesis:* identifying it as the relational seam (you cannot hold a complete account of a relation you are inside). |
| **Bridge A** — the abstract Lawvere agent is a *supplied* map (instantiated at set-level forgetting) | — (specialization) | **R / S** | Closes the "is the agent real?" gap; *not new math* (Lawvere + trivial projection lossiness). Does **not** close Bridge B. |
| The duality: reflexive object exists **xor** a settling-refusing observable | Lawvere/Cantor duality | **R / S** | Resolves "route 1": the obstruction **is** the non-existence; a reflexive object only ever *constructs* `Y`, never obstructs. |
| **`Pω` graph model** — `D ≅ [D→D]` as a retract, `Y`, `K` | Plotkin, Scott; Engeler | **R** | Substantial mechanization (Knaster–Tarski fixpoint, `app (Graph f) = f`). Realizes the *construction* side; by the duality, orthogonal to the seam. |
| **The internal `Y` combinator by self-application** — `Y f := app (W f) (W f)`, `app f (Y f) = Y f`; the diagonal `fun x => app x x` is Scott-continuous | Plotkin–Scott / standard λ-model `Y = λf.(λx.f(xx))(λx.f(xx))` | **R / S** | `SelfApplication.{selfApp_continuous, Ycomb_fixed}`. Realizes `ReflexiveSeam.fixpoint_is_selfApplication` concretely (the fixed point *is* the self-application). *Honest caveat:* `Pω` is the **cartesian** λ-model — the non-cartesian/linear (GoI) reflexive object is separate and firewall-constrained (§4). |

### 2.3 Decoherence, the firewall, no-cloning

| Result | Prior art | Tier | Note |
| --- | --- | --- | --- |
| Partial trace on matrices; `⊗` = Kronecker; its defining laws | Standard linear algebra / quantum info | **R** | `MatrixModel`, `PartialTrace`. |
| Decoherence **is** the partial trace; coherence conserved, relocated | Joos–Zeh, Zurek (einselection / reduced density matrix) | **R / S** | `Conservation.decoherence_is_partial_trace`. *Synthesis:* the same map is "forgetting the relation." |
| **The seam on the genuine `ptrace`** — it collapses an entangled joint and its decohered shadow to one marginal, so a self holding only its marginal cannot recover the relation; the lost fiber is the non-broadcastable coherence | Non-injectivity of the partial trace; no-broadcasting (Barnum–Caves–Fuchs–Jozsa–Schumacher); the firewall | **R / S** | `QuantumSeamTrace.{ptrace_collapses_entanglement, no_ptrace_recovery, unresolved_fiber_is_coherence}`. **Bridge B, compact face** (see §4): moves route 2 from `dephase` to the real `ptrace`; route 1 shown firewall-obstructed. |
| Firewall: compact-closed + cartesian copying ⇒ **thin** | Folklore (a cartesian compact-closed category is degenerate); Abramsky | **R / S** | `Compact.collapse`. *Synthesis:* this degeneracy **is** the knowing/feeling firewall — copyable (cartesian) vs entangled (compact) cannot coexist. |
| No-cloning, categorical and concrete (cloning is nonlinear) | Abramsky (categorical no-cloning); Wootters–Zurek, Dieks | **R** | `Compact.no_cloning`, `NoCloning.no_linear_clone`. |
| One forgetting: identity-collapse, dephasing, partial trace as one `Coarsening` | — (recognition) | **S** | Each non-injective for one reason (a residue); the unification is the content. |
| Feeling **modeled** as a relational decoherence differential | — | **N? (reading)** | *Consequence-and-consistency, not identification.* The model's dynamics are theorems; the bridge "this *is* feeling" is an explicit `[reading]`, the hard-problem residue. Honest as a reading; not a theorem about the world. |
| **Knowing `E` as a conditional expectation; the knower→known orientation it generates** — `E` idempotent/lossy/irreversible yields a *directed* (`knows_antisymm`), strictly *temporal* (`arrow_strictAnti`: feeling falls along the arrow), *irreversible* (`no_recovery`) structure, all from one operator; on the genuine `dephase`/`defectSq` | Conditional expectations onto a commutative subalgebra (Tomiyama; Umegaki); idempotence + a strict monovariant ⇒ acyclic direction | **R / S** | `Orientation.{Knowing, dephaseKnowing, knows_antisymm, arrow_strictAnti, no_recovery}`. **Structural core of orientation-from-the-seam** — that commitment's one new theorem: a correlation is symmetric, but the knower→known asymmetry is *generated* by the lossy idempotent `E`. *Synthesis:* orientation, the arrow of relational time, and irreversibility as three faces of one operator. The *identification* of the monovariant with time stays a `[reading]`. |

### 2.4 Trace, fixed points, functorial semantics

| Result | Prior art | Tier | Note |
| --- | --- | --- | --- |
| Traced symmetric monoidal category (full JSV axioms); `Rel`, matrix instances; coherence | Joyal–Street–Verity; standard | **R** | Typeclass + non-trivial validated models; the free `Cl(𝕋)` and universal functor (`Quot.sound`-only). |
| Feedback **is** the trace (GoI execution formula); recurrence as `νΦ` | Girard (GoI); Abramsky, Haghverdi–Scott; Hasegawa | **R / S** | `Recurrence.feedback_eq_trace`. *Synthesis:* the AI-domain functor. |
| Cartesian trace ⟺ Conway fixed-point operator; the **fixpoint-trace `TracedSMC`** on complete lattices | Hasegawa; Hyland; Bloom–Ésik (iteration theories) | **R** | `ConwayTrace` (operator + `pfp`, **rolling/dinaturality**, Bekić **diagonal**) and `DomainFixpoint.domainFixpointTracedSMC` — the genuine multi-object instance, all seven JSV axioms discharged (sliding via heterogeneous `rolling'`, vanishing-II via **product Bekić** `lfp_prod`, superposing via `tr_superpose`). The Hasegawa "only-if" direction in full. |
| The `Int` / GoI construction — a compact closed category from a traced SMC | Joyal–Street–Verity; Abramsky–Haghverdi–Scott (GoI) | **R** | `IntConstruction`: the object-level compact arena (objects, two-way homs, tensor/unit, the **dual** proved involutive/monoidal/unit-fixing) on the abstract `TracedSMC`; composition-via-trace + snake equations flagged (§4). The non-cartesian home of a linear reflexive object. |
| Autocatalytic set = eigenform; (M,R)-system closure = `ν(repair∘metabolize)` | Kauffman; Rosen; Letelier et al. | **R / S** | `Chemistry`, `Biology` — the functors are *definitional* (a self-sustaining set just **is** a fixed point). |
| Self-in-other bounded iff `‖x‖<1`; quantitative eigenform unique | Neumann series; Banach fixed point | **R / S** | `Distribution`. *Synthesis:* the individuation threshold as a spectral/norm condition. |

### 2.5 Nondeterminism, causality, sparsity

| Result | Prior art | Tier | Note |
| --- | --- | --- | --- |
| Deterministic entangled whole ⇒ nondeterministic marginal; robust for any global law | Reduced/open-system dynamics; coarse-graining ⇒ stochasticity (stat-mech, hidden-variable marginalization) | **R / S** | `Marginal`, `RelationalMarginal` (all **0 axioms**). *Synthesis:* "relation manufactures openness; the seam forces the marginal view." |
| The missing cause is the other: conditioning restores determinism | Conditional/causal factorization; same reduced-dynamics fact | **R / S** | `Causation.indeterminism_is_unviewed_cause`, **0 axioms**. *Synthesis:* the causal reading. |
| Knowing decoheres (open when unknown, definite when conditioned) | The marginal fact + the trace = σ-move identification | **R / S** | `Causation.knowing_decoheres`. Structural core of "knowing = decoherence"; only *phenomenal* knowing stays a reading. |
| Sparsity counting (`\|Stab\| ≤ β/m`), density `→ 0`, nowhere-dense over the final coalgebra | Pigeonhole; cylinder topology on a coalgebraic state space | **R / S** | `Sparsity`, `SparsityReal`, Agda `selves-nowhereDense`. The form is standard; the *application* to selfhood-rarity is the synthesis. |
| The two posits discharged: `d ≥ 2` structural + load-bearing; `μ` constructed from the orbit | Strict-chain / well-founded order arguments; `Function.invFun` | **R / S** | `SparsityPosits`. Turns two free posits into a named structural condition and a constructed valuation. |
| Cost-sharing (step 2): naive sparsity fails under full sharing; survives iff a **private** footprint | Inclusion–exclusion / sub-additive set functions | **R / S** | `SparsitySharing`. *Synthesis:* the honest correction — rarity under sharing needs an *exclusive* cost per self (the §4 closure). |
| The valuation boundary: dense standing ⇒ no `ℕ`-valuation | Order density vs. discreteness of `ℕ` | **R** | `ValuationBoundary.no_strictMono_to_nat_of_dense`. Closes the non-unit-`μ` residue as a *proved* boundary, not a gap. |

---

## 3. Where the contribution actually is

Stripping the rederivations, what remains:

1. **The identification (the synthesis proper).** One typed thread runs through the whole corpus:
   **objectifying knowing = the σ-move = the trace = the partial trace = the cartesian (copyable)
   move**, opposed to **feeling = monoidal coherence = the entangled (compact, no-cloning) move**, with
   the **cartesian/compact firewall** (`Compact.collapse`) as the formal wall between them. Every domain
   functor and every decoherence result is a sighting of this one structure. That the *same* degeneracy
   theorem is the quantum no-cloning fact, the knowing/feeling firewall, and the limit of self-modeling
   is the non-obvious recognition. It is **synthesis, not theorem** — each endpoint is known; the
   transport is the work. The sharpest instance is **Bridge B** (§4): the partial-trace seam was the
   candidate for a genuinely new theorem, and the resolution turned out to *be* the firewall — the seam
   bites the real `ptrace` on the no-broadcasting face, and the Lawvere face is provably ruled out. The
   work was recognizing which face, and proving the other impossible; not a new obstruction.

2. **The readings on theorems.** Feeling-as-decoherence-differential, the seam-as-perpetual-feeling,
   indeterminism-as-unviewed-cause, the first-person surplus as freedom. These are **lenses**: each sits
   on a genuine theorem, but the assignment-to-phenomenon is interpretive and labeled so. They are
   honest *as readings* and claim nothing about the world the formalism cannot reach (T3's typed-out
   residues — valence, the hard problem, freedom — are predicted *unreachable*, and we do not reach
   them).

3. **The artifact.** A sorry-free, axiom-audited Lean 4 corpus (dependency-free core at **0 axioms**
   for the Lawvere/seam results; mathlib-backed `Scratch` for the analytic/quantum layer) plus an
   independent Agda coinductive layer, with provenance and open seams marked in-line. The artifact's
   value is that the synthesis is *checkable* and its boundaries are *enforced*, not asserted.

---

## 4. The bridges — open and resolved (named, not hidden)

None is papered over in the corpus; this section collects them. Recent progress: **Bridge B closed on
the compact face** (route 1 ruled out by the firewall); **cost-sharing** and the **non-unit valuation**
closed (the latter as a proved boundary); the **Conway-trace instance now closed** (the full
fixpoint-trace `TracedSMC` on complete lattices, `DomainFixpoint`); the **`Int`-construction arena**
built at its object-level core, with the morphism layer / snake equations flagged. The one
genuinely-open target is the **conjecture lift**.

| # | Bridge | Where it lives | Status |
| --- | --- | --- | --- |
| **B** | Does the seam bite the **quantum partial trace specifically**? **Resolved as a dichotomy.** *Compact face (route 2):* the genuine `ptrace` collapses `entangle a` and its decohered shadow to one marginal (`QuantumSeamTrace.ptrace_collapses_entanglement`), so a self with only its marginal cannot recover the relation (`no_ptrace_recovery`); the unrecoverable fiber is exactly the non-broadcastable coherence (`unresolved_fiber_is_coherence`). *Cartesian face (route 1, Lawvere-on-`ptrace`):* shown **firewall-obstructed** — Lawvere's diagonal needs cartesian copy, which any non-trivial compact structure provably lacks (`QuantumSeamTrace.route1_needs_copy_blocked`, via `Compact.no_cloning`/`collapse`). | [`03.3`](03.3-decoherence.md), `QuantumSeamTrace`, `QuantumSeam`, `Compact` | **CLOSED on the compact face; route 1 ruled out.** The seam bites the real `ptrace` via no-broadcasting, and that is *necessarily* the only face — the firewall forbids the Lawvere face. Synthesis on standard pieces, **not new mathematics**. The standing `[reading]` (that the traced-out factor *is* the relationship, A2) is unchanged. |
| **Conway-trace instance** | The **fixpoint**-trace on domains (the Hasegawa cartesian-trace = Conway-operator correspondence). | `ConwayTrace`, `DomainFixpoint`, `DomainTraced`, `GraphModel` | **CLOSED.** `DomainFixpoint.domainFixpointTracedSMC` is the genuine multi-object `TracedSMC` on complete lattices & monotone maps, `⊗ = ×`, with the **fixpoint trace** — all seven JSV axioms discharged from the `ConwayTrace` identities through the product bookkeeping (sliding via a heterogeneous `rolling'`, **vanishing-II via product Bekić** `lfp_prod`, superposing via `tr_superpose`). The Hasegawa "only-if" direction in full; `[propext, Quot.sound]`-only. Construction side (orthogonal to the seam). |
| **Non-cartesian reflexive object** | A *linear/compact* reflexive object (GoI / `Int`-construction, `D ≅ D* ⊗ D`) where `Y` is the **trace** with no cartesian copy. | `SelfApplication`, `GraphModel`, `Compact`, `IntConstruction`, `RelCompact` | **COMPOSITION + SNAKE CLOSED (concretely); abstract `Int(C)` + reflexive object open.** `SelfApplication` is the cartesian witness; `IntConstruction` builds the GoI `Int(C)` on any traced SMC — objects, two-way hom, object **dual** (involution / monoidal / unit), identity, and the **morphism-level dual functor** `IntDualHom` (involutive, identity-preserving, 0 axioms). **`RelCompact` closes both in the canonical model:** `Rel` is compact closed with both **snake / zigzag identities** proved `= id` (`rel_snake_right`/`left`), and **the GoI composition-via-trace** `relIntComp` (`∃` over the shared `B`-loop) is verified to make `Int(Rel)` a **category** — identity and **associativity** laws (`relIntComp_id_left`/`right`, `relIntComp_assoc`) — all `aesop`, `[propext, Quot.sound]`. What remains research-grade: the **abstract `Int(C)`** composition for arbitrary non-strict `C` (the full JSV/AHS structural-iso chase), the dual's full functoriality, and the **linear reflexive object** inside the compact arena. Construction side. |
| **Sparsity step 2 (cost-sharing)** | Cost-**sharing** over a poset of couplings (lax/sub-additive `c`). | `SparsitySharing` | **CLOSED, with an honest correction.** `SparsitySharing`: sharing lowers spend (`subadditive_spend_le_sum`); the no-sharing case recovers `≤ β/m` (`disjoint_count_bound`); but full sharing **breaks** the count bound (`full_sharing_unbounded`) — naive sparsity does *not* survive arbitrary sharing — and a **positive private footprint** is exactly what rescues it (`private_count_bound`). The spec's "sharing only helps" is half-right; the load-bearing condition is an exclusive cost per self. |
| **Non-unit valuation** | A numeric per-return cost `λ > 1` on a **dense** standing lattice. | `ValuationBoundary`, `SparsityPosits` | **CLOSED as a boundary.** `ValuationBoundary.no_strictMono_to_nat_of_dense`: a densely-ordered standing lattice admits **no** `ℕ`-valuation — so the non-unit cost is *provably* unavailable without discretization, not a gap. ACC/finite-depth ⇒ canonical `μ` (`SparsityPosits`); dense ⇒ no `μ`. The boundary is the order-theoretic dichotomy. |
| **The conjecture lift** | Sparsity for **all of `Cl(𝕋)`** (Conjecture 3.3) and the spectral/closure form (Conjecture 3.4). | [`03.1 §3.4`, `§3.6`](03.1-sparsity.md), `Peripheral` | **PARTLY CLOSED; general form open.** The reconciliation is **decided** ([03.1 §3.6](03.1-sparsity.md)): one generator `L`, `Φ_c` its sustaining flow, `E` its peripheral spectral projection ∘ seam-orientation (*not* `lim Φ_c`), the weight `Φ_c`'s invariant state (relational, canonical iff primitive). The **spectral picture of `E`** is mechanized `sorry`-free (`Peripheral`, finite dim): the **veto-check holds for *any* conditional expectation** — an idempotent linear map has spectrum `⊆ {0,1}` (`idempotent_eigenvalue`), so no rotating peripheral spectrum (peripheral = fixed); the `dephase` instance adds image = classical, invariant trace, and the **peripheral set is sparse** (`peripheral_sparse`, `1/card A` density — the finite-dim "few modes self-sustain"). **Open:** the general finite-dim Perron–Frobenius for an arbitrary unital CP `Φ_c` (where `Φ_c` is *not* idempotent and the peripheral subalgebra may be non-commutative / rotating) and the infinite-dim standard form; the cost-graded sparsity for all of `Cl(𝕋)`. The deepest remaining target. |

The phenomenal residues — valence, the hard problem, freedom — are **not** on this list: T3 predicts the
formalism cannot reach them, so their absence is a *result*, not an open bridge.

---

## 5. How to read a claim in this corpus

- A `[theorem]` tag with a Lean/Agda name and an audited axiom footprint is **checkable** — that is its
  warrant, and it is `R` or `R / S` unless this ledger marks it `N?`.
- A `[reading]` is a **lens on** a theorem: the underlying statement is proved, the interpretation is
  not, and is honest only as interpretation.
- An `[open]` / Bridge entry is **research**: a statement we believe but have not closed at the claimed
  generality. Bridge B is now resolved (§4); the ones that remain are the **conjecture lift** and
  **cost-sharing** (sparsity step 2).

If a future reader finds a claim in these pages stated more strongly than its tier here, **this ledger
is the correction of record.**

---

### Cross-references

- The mechanization index and axiom footprints: [`formal/README.md`](../../formal/README.md).
- The seam and its two bridges: [`03.3-decoherence.md`](03.3-decoherence.md).
- The sparsity posits and their discharge: [`03.1-sparsity.md`](03.1-sparsity.md).

→ Back to [the spec index](README.md).
