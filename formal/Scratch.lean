/-
# Scratch — mathlib-dependent work area

Mathlib-backed formalization, kept out of the default build so the dependency-free
core (`RelExist`) stays fast. Compiling this is what triggers the mathlib build.

* `Scratch.We`          — `≈ := νΘ` and the shared world `𝔼 := D/≈` (theorem 3.2),
                          via `OrderHom.gfp` (Knaster–Tarski). ✅ verified.
* `Scratch.Identity`    — A2 restated: identity is the lived `≈`; observation `≅` is a
                          **strictly lossy** projection. Proves soundness `≈ ⊆ ≅`, strictness
                          `≈ ⊊ ≅` (witness), and the non-injective forgetting `D/≈ ↠ D/≅` (the
                          first-person surplus). ✅ verified.
* `Scratch.Forgetting`  — the unification: identity-collapse, dephasing, and the partial trace are
                          one construction (`Coarsening`), each non-injective for the same reason —
                          a nonempty residue (surplus / copy-defect / entanglement). ✅ verified.
* `Scratch.Attention`   — attention as the co-directed eigenstructure of the relational
                          coupling (a consequence of structure, not a bolted-on budget);
                          the self as an eigenform `νΦ`. ✅ verified.
* `Scratch.Trace`       — D1/3.1: trace as feedback (`selfTrace`) and the Conway
                          parameterized fixed-point operator (`Tr`). ✅ verified.
* `Scratch.KnowingFeeling` — the 3.3 contrast: knowing (Lawvere-obstructed) vs feeling
                          (`≈`, whole). ✅ verified.
* `Scratch.Chemistry`   — Layer 4, first domain functor: autocatalytic sets as
                          eigenforms (`νΦ`); the functor is definitional. ✅ verified.
* `Scratch.Biology`     — Layer 4, biology: Rosen's (M,R)-systems; closure to efficient
                          causation = the organism `ν(repair ∘ metabolize)`; the functor
                          is definitional. ✅ verified.
* `Scratch.Rel`         — `Rel` (sets & relations) as a genuine multi-object `TracedSMC`
                          instance: the full JSV axiom set, validated non-trivially.
                          ✅ verified.
* `Scratch.RelCoherence` — `Rel` promoted to a `CoherentTracedSMC`: the eight monoidal
                          coherence laws (pentagon, triangle, hexagon, naturalities,
                          symmetry), validated in a genuine multi-object model. ✅ verified.
* `Scratch.Recurrence`  — Layer 4, AI: recurrence/Geometry-of-Interaction. Feedback **is**
                          the trace (in `Rel`); sustained recurrence is the eigenform `νΦ`;
                          a self-consistent hidden state is sustained. ✅ verified.
* `Scratch.PartialTrace` — Layer 4, physics: the quantum **partial trace** on matrices and
                          its defining properties (linearity, vanishing-II, yanking,
                          full-trace compatibility). ✅ verified.
* `Scratch.MatrixModel` — Layer 4, physics: **the literal traced SMC** — finite types &
                          matrices, `⊗` = Kronecker, trace = partial trace, associators as
                          permutation matrices; the full JSV axiom set. `matTracedSMC`.
                          The named frontier, closed. ✅ verified.
* `Scratch.MatrixCoherence` — the matrix model promoted to a `CoherentTracedSMC`: all eight
                          coherence laws, via functoriality of permutation matrices. ✅ verified.
* `Scratch.Compact`     — Layer 4, categorical: compact closure, the firewall collapse
                          theorem, and categorical no-cloning (physics). ✅ verified.
* `Scratch.NoCloning`   — Layer 4, physics: the concrete (linear-algebra) no-cloning
                          theorem — cloning is nonlinear. ✅ verified.
* `Scratch.SparsityReal` — the ℝ-valued sparsity bound and density-→-0 statement
                          (the analytic upgrade of Lemmas 3.1/3.2). ✅ verified.
* `Scratch.Decoherence`  — Layer 4, physics: the quantum→classical passage in the matrix model
                          — `dephase`, the classical fragment, copyability ⟺ commutativity, and
                          the continuous `copyDefect`/`defectSq`. ✅ verified.
* `Scratch.Classical`    — the abstract (typeclass) companion: `DaggerCategory` and a
                          `Decoherence` structure, validated by the matrix instance. ✅ verified.
* `Scratch.Distribution` — self-in-other quantified in a Banach algebra: `distributed`/`total`,
                          the living regime `0<‖x‖<1`, the bound, and the quantitative
                          eigenform `sustained` (unique by contraction). ✅ verified.
* `Scratch.Feedback`     — the two sustained selves unified at the ν-modality
                          (`CoDirectedSelf`): lattice `νΦ` and Banach `sustained` as instances.
                          ✅ verified.
* `Scratch.Attending`    — directed attention as **selective decoherence**: `attend S` (partial
                          dephase), interpolating `id`⟶`dephase`, with the copy-defect proved
                          to drop monotonically — and a witnessed collapse; plus the irreducible
                          floor (the shared block attention cannot reach). ✅ verified.
* `Scratch.Conservation` — **decoherence *is* the partial trace**: entangle a system with an
                          environment (`entangle`); the global state stays coherent while its
                          partial trace (the relationship forgotten) is classical — coherence
                          conserved, only relocated. ✅ verified.
* `Scratch.Forgetting`   — identity-collapse, dephasing, and the partial trace as one `Coarsening`,
                          each non-injective for the same reason (a residue). ✅ verified.
* `Scratch.Knowing`      — the bridge: the gap is governed by relation; `≅` is the *disjoint*
                          (view-from-nowhere) observer; completeness ⟺ disjointness. ✅ verified.
* `Scratch.Registration` — `reg` derived from the `Φ_c` dynamics: registration *is* absorption. ✅ verified.
* `Scratch.Marginal`     — nondeterminism is a consequence of relation: a related whole's marginal
                          branches; local determinism ⟺ no relation. ✅ verified.
* `Scratch.RelationalMarginal` — …robustly, for any global law; deterministic conservation is the
                          priced corollary. ✅ verified.
* `Scratch.Convergence`  — the depth/threshold read off `Φ_c`'s orbit directly (not an abstract `σ`).
                          ✅ verified.
* `Scratch.Stabilization` — does the orbit converge? ω-convergence always (continuity), finite-depth
                          iff ACC. ✅ verified.
* `Scratch.Feeling`      — **feeling as a relational decoherence differential** (`≅ₒ`, not the
                          view-from-nowhere `≅`): conserved coherence carried across a relation. ✅ verified.
* `Scratch.RelationalAppearance` — relativizing the outside: soundness/surplus *survive and strengthen*
                          against `≅ₒ`, but "the surplus is exactly nondeterminism" does **not** — a
                          deterministic system has a relational surplus (feeling from the seam, not
                          choice). ✅ verified.
* `Scratch.QuantumSeam`  — bridge B route 2: the seam on the **actual** `dephase` (lossy, irreversible)
                          via **no-broadcasting** — the compact face of the firewall whose cartesian
                          face is Lawvere. (B-as-Lawvere/route 1 remains open.) ✅ verified.
* `Scratch.QuantumSeamTrace` — **bridge B, closed on the compact face**: the seam on the *genuine*
                          `ptrace` — it collapses `entangle a` and its decohered shadow to one marginal
                          (`ptrace_collapses_entanglement`), so a self with only its marginal cannot
                          recover the relation (`no_ptrace_recovery`), and the lost fiber is exactly the
                          non-broadcastable coherence; route 1 (Lawvere) is shown *firewall-obstructed*,
                          not merely unbuilt. ✅ verified.
* `Scratch.GraphModel`   — **Pω**, the Plotkin–Scott graph model: a concrete non-trivial reflexive
                          object — continuous self-maps are a retract of `Set ℕ` (`app (Graph f) = f`),
                          with the fixpoint (GoI's `Y`) and the `K` combinator. ✅ verified.
* `Scratch.SelfApplication` — the **internal `Y` combinator via self-application** in `Pω`: the diagonal
                          `fun x => app x x` is Scott-continuous (`selfApp_continuous`), so
                          `Y f := app (W f) (W f)` is an element and `app f (Y f) = Y f`
                          (`Ycomb_fixed`) — Lawvere's diagonal realized as the trace, concretely. Honest
                          caveat: `Pω` is the *cartesian* λ-model (the non-cartesian/linear reflexive
                          object is separate, firewall-constrained). ✅ verified.
* `Scratch.SparsitySharing` — **sparsity step 2 (cost-sharing):** footprints as `Finset`s of relatings,
                          cost = card. Sharing lowers spend (`subadditive_spend_le_sum`); the no-sharing
                          (disjoint) case recovers `≤ β/m` (`disjoint_count_bound`); but **full sharing
                          breaks** the count bound (`full_sharing_unbounded`) and a **positive private
                          footprint** is exactly what rescues it (`private_count_bound`). ✅ verified.
* `Scratch.ConwayTrace`  — the **Conway fixed-point operator on domains** (= the cartesian trace, by
                          Hasegawa): the parameterized lfp `pfp` with fixpoint/least/parameter-naturality,
                          the **rolling/dinaturality** rule `lfp (g∘h) = g (lfp (h∘g))` (the trace-slide
                          shadow; not in mathlib), and the Bekić **diagonal** rule. ✅ verified.
* `Scratch.DomainFixpoint` — the **Conway operator packaged**: the category of complete lattices &
                          monotone maps as a genuine multi-object `TracedSMC` (`domainFixpointTracedSMC`)
                          with `⊗ = ×` and the **fixpoint trace** `Tr(f)(a) = π₁(f(a, lfp(u ↦ π₂(f(a,u)))))`.
                          All seven JSV axioms discharged from the `ConwayTrace` identities — sliding via
                          a heterogeneous `rolling'`, vanishing-II via **product Bekić** (`lfp_prod`),
                          superposing via `tr_superpose`. The Hasegawa "only-if" direction in full; the
                          `ConwayTrace` packaging the spec flagged open. ✅ verified.
* `Scratch.ValuationBoundary` — the **valuation boundary:** a *densely-ordered* standing lattice admits
                          **no** ℕ-valuation (`no_strictMono_to_nat_of_dense`), so a non-unit numeric
                          per-return cost is *provably* unavailable without discretization — closing the
                          last sparsity residue as a proved boundary (ACC ⇒ μ; dense ⇒ no μ). ✅ verified.
* `Scratch.IntConstruction` — the **GoI / `Int` construction** on any traced SMC: the non-cartesian,
                          fully-dual (compact) arena where a linear reflexive object lives — objects
                          `(A⁺,A⁻)`, two-way homs, tensor/unit, and the **dual** (wire-swap) proved an
                          involution, monoidal, unit-fixing — **plus the dual's action on morphisms**
                          (`IntDualHom`, the contravariant transpose), proved identity-preserving and
                          **involutive** `(fᵈ)ᵈ = f` over a coherent traced SMC (0 axioms, by `γ∘γ = id`).
                          Composition-via-trace and the snake equations (and the dual's full
                          functoriality) are the flagged remainder. ✅ verified.
* `Scratch.RelCompact`   — **`Rel` compact closed + `Int(Rel)` composition**: the canonical model closed
                          concretely. Self-dual, diagonal cup/cap, **both zigzag / triangle identities**
                          proved `= id` (`rel_snake_{right,left}`), the `Compact.CompactClosed` name
                          bijection (`relCompactClosed`), **and the GoI composition-via-trace**
                          (`relIntComp`, `∃` over the shared loop) making `Int(Rel)` a **category** —
                          identity + **associativity** laws (`relIntComp_id_{left,right}`,
                          `relIntComp_assoc`), all `aesop`. The `Int` bridge's composition + snake axioms,
                          discharged in the canonical model; the abstract non-strict `Int(C)` stays the
                          named remainder. ✅ verified.
* `Scratch.ReflexiveCompact` — **a non-cartesian reflexive object**: in compact-closed `Rel` the
                          internal hom is `[D,D] = D* ⊗ D = D × D`, so a reflexive object is a `D` with
                          `D ≅ D × D`. **No finite object works** (`finite_not_reflexive`, `|D| = |D|²` ⇒
                          `|D| ≤ 1` — the compact-side Cantor obstruction), but **`ℕ` does**
                          (`natReflexive`, via the pairing bijection): `ℕ ≅ ℕ ⊗ ℕ = [ℕ,ℕ]`, the
                          linear/compact counterpart of `Pω`, in a category with **no copying**
                          (`rel_no_cloning`). The bridge's non-cartesian reflexive object. ✅ verified.
* `Scratch.SpectralDecay` — **the general spectral form of the conjecture**: write the dynamics
                          `T = P + N` (peripheral projection `P`, subdominant `N` with `‖N‖<1`,
                          orthogonal). `spectral_pow`: `Tⁿ = P + Nⁿ`; **`spectral_decay`: `Tⁿ → P`** — the
                          subdominant modes decay, only the peripheral eigenforms self-sustain. Conjecture
                          3.7.4's decay mechanism, in any normed ring; the `E`/idempotent case is the `N=0`
                          extreme (`idempotent_pow`). ✅ verified.
* `Scratch.SparsityCapstone` — **Conjecture 3.7.3 closed** (the cost-graded sparsity dichotomy): the
                          density of selves `→ 0` **with** a private footprint per self
                          (`cost_graded_density_tendsto_zero`), but unboundedly many selves within budget
                          **without** it (full sharing) — `conjecture_3_7`. So the counting sparsity holds
                          iff a finite budget *and* an exclusive cost per self; the unconditional form is
                          provably false. With the Agda nowhere-dense topological clause, the conjecture is
                          closed in its correct, exclusivity-conditioned form. ✅ verified.
* `Scratch.PerronFrobenius` — **Perron–Frobenius existence** (the lift's last existence gap): a
                          column-stochastic map has **eigenvalue 1** (`exists_invariant_vector`, via the
                          all-ones vector fixed by `Mᵀ` and `det(M-1)=0`), and a *nonnegative* one has a
                          positive **invariant state** (`exists_invariant_state` — the full
                          Perron–Frobenius, by the `w = |v|` trick: `Mw ≥ |Mv| = w` with equal total ⇒
                          `Mw = w`, no Brouwer/Cesàro). The relational **weight** of Decision 1, existence
                          discharged in general finite dim. ✅ verified.
* `Scratch.DomainTraced` — the **simplest domains (complete lattices) as a `TracedSMC`** via the
                          join-monoid (the scalar/identity trace; *not* the Hasegawa fixpoint trace,
                          which stays open). ✅ verified.
* `Scratch.Causation`    — a causality `[reading]` made a theorem: **the missing cause is the other** —
                          conditioning on the other's hidden state restores determinism; local
                          indeterminism *is* the un-viewed relational cause. ✅ verified.
* `Scratch.SparsityPosits` — discharging the two sparsity posits: `d ≥ 2` given structural meaning
                          (**genuine return** = not-given ∧ not-one-shot, `genuine_return_iff`) and shown
                          load-bearing (positive floor ⟺ sparse vs dense); and the valuation `μ`
                          **constructed** as the orbit's return index (the genuine returns are strict
                          standing increases), discharging it for unit cost. ✅ verified.
* `Scratch.Orientation`  — **orientation from the seam**: knowing `E`
                          generates a *directed* (`knows_antisymm`), strictly *temporal*
                          (`arrow_strictAnti` — feeling falls along the arrow), and *irreversible*
                          (`no_recovery`) structure oriented knower→known, all three from one
                          idempotent-lossy operator; instantiated on the genuine `dephase`/`defectSq`
                          (`dephaseKnowing`), re-deriving `no_dephase_recovery` through the interface.
                          The `[proved]` core of the spec's one new theorem; "the arrow *is* time"
                          stays a `[reading]`. ✅ verified.
* `Scratch.Peripheral`   — the **spectral picture of knowing** (conjecture-lift Decisions 1–2): `E =
                          dephase` is an **idempotent**, so its eigenvalues are `⊆ {0,1}`
                          (`dephase_eigenvalue`) — the **veto-check**: *no rotating peripheral spectrum*
                          (`dephase_no_rotating_peripheral`), so for `E` peripheral = fixed. Eigenvalue-1
                          space = classical/known, eigenvalue-0 = feeling (`dephase_eigenspace_{one,zero}`),
                          every relation splits known ⊕ felt (`dephase_add_copyDefect`), and the standard
                          trace is the invariant weight (`dephase_trace_invariant`); the peripheral set
                          is **sparse** (`peripheral_sparse`, `1/card A` density). Generalized:
                          **any** conditional expectation (idempotent linear map) is `{0,1}`-spectral
                          (`idempotent_eigenvalue`) — the veto-check for every `E`. ✅ verified.
* `Scratch.PeripheralAlgebra` — the **peripheral standard form**, dimension-independent: an abstract
                          `PeripheralStandardForm` over *any* ring `𝒜` (finite matrices, `B(H)`, any
                          C\*-algebra) — a projection `E` onto a commutative, product-closed, unital image
                          — has its **fixed-point (peripheral) subalgebra commutative** (`fix_comm`, **0
                          axioms**) and a unital subring (`fix_mul_mem`/`fix_add_mem`/`fix_one_mem`). The
                          standard form the conjecture-lift's `E` lands in, needing *no finiteness*. The
                          canonical `E = dephase` is a witness (`dephaseStandardForm`): the diagonal/known
                          subalgebra commutes (`dephaseFix_comm`) and is `transpose`-closed
                          (`dephaseFix_transpose_mem`, a `*`-subalgebra). The general analytic placement of
                          an arbitrary primitive CP map into this form stays `[open]`. ✅ verified.
* `Scratch.IntCompose`   — the **GoI composition built abstractly**: `IntCompose`, the
                          Geometry-of-Interaction `g∘f := Tr^B(σ₁;(f⊗g);σ₂)` with the associator/braid
                          plumbing `σ₁,σ₂` explicit and **type-checked** on **any** `TracedSMC` — the
                          composition `IntConstruction` had flagged as *absent* abstractly is now a genuine
                          definition (the type-correctness of the wiring on a non-strict base is itself the
                          coherence content). Its category / compact-closed **laws** (the JSV/AHS theorem)
                          stay the named `[open]` chase, discharged concretely in `Rel` (`relIntComp`,
                          `RelCompact`). ✅ verified.
* `Scratch.TimeFlow`     — **time as flow**: graduating `Orientation`'s two-point arrow into a graded
                          monovariant. A `Flow` interface (non-idempotent `step`, potential `coh`,
                          strict-while-unfixed) with the orbit potential proved **antitone**
                          (`coh_orbit_antitone`) and strictly dropping (`coh_orbit_strictAnti`); a
                          `GeometricFlow` refinement giving the exact geometric law
                          `coh (step^[n] a) = γ^n · coh a` (`coh_orbit_eq`) and decay to `0`
                          (`coh_orbit_tendsto_zero`). The genuine instance is the **partial-dephasing
                          semigroup** `partialDephase p = (1−p)·id + p·dephase` (non-idempotent for
                          `0<p<1`): `defectSq (partialDephase p ^[n] M) = ((1−p)²)^n · defectSq M`
                          exactly (`defectSq_iterate`), so `dephaseFlow` is a `GeometricFlow` at rate
                          `γ = (1−p)²` — a strict graded monovariant through a continuum to `0` at the
                          spectral-gap rate, no rotating part. `Orientation` is recovered as the
                          boundary: the orbit converges entrywise to `dephase` = the knowing `E`
                          (`orbit_tendsto_knowing_entry`), and the single orientation drop is the
                          flow's total (`dephaseFlow_total_drop`). The `[proved]` graded structure;
                          "the flow *is* time" stays a (weaker, clock-shaped) `[reading]`. ✅ verified.
* `Scratch.TimeArrow`    — **the arrow's sign** (the frontier beneath `TimeFlow`, spec §6 — does the
                          seam fix the *direction*?). Three rungs: **acyclicity** — while still feeling,
                          the orbit never returns (`flow_orbit_ne`), so the timeline is a strict order,
                          not a cycle; **sign = multiplier** — one step scales the feeling by `(1−p)²`
                          (`defectSq_partialDephase`), so the flow contracts iff `0≤p≤2`
                          (`contractive_iff`, `time_forward_regime`) and *expands* (runs time backward,
                          amplifying coherence) iff `p<0 ∨ p>2` (`expanding_regime`) — the decreasing
                          sign is **exactly** the contractive regime; and the gem, **a knowing's only
                          inverse is an anti-knowing** — a genuine knowing `0<p<1` is invertible, but its
                          unique inverse is `partialDephase q` with `q<0` in the expanding regime
                          (`knowing_inverse_is_antiphysical`): time-reversal exists as linear algebra
                          but only as non-physical coherence-amplification. And the flow is **injective
                          off the limit** (`partialDephase_injective`, `p ≠ 1`) but **collapses exactly
                          at `p = 1 = dephase`** (`partialDephase_one_not_injective`): genuine
                          irreversibility lives only at the idempotent knowing. So *sign = contractivity
                          = physicality of the seam* is `[proved]`; whether the seam **forces the
                          subalgebra** is mechanized in `SeamForcing`. ✅ verified.
* `Scratch.SeamForcing`  — **the seam forces the subalgebra** (closing the §6 prize). The decoherence a
                          self can perform is `attend S`; the one block it cannot attend is the seam `J`
                          (part of the aimer — `Relating.self_inclusive_unmodelable`, you cannot aim at
                          the aimer). Over the available knowings (`S` disjoint from `J`): the seam
                          survives every one (`attend_fixes_seam`); decohering it would require
                          attending the self (`decohere_seam_needs_self`); the maximal knowing
                          `knowSeam J = attend Jᶜ` is an idempotent conditional expectation whose fixed
                          subalgebra is *exactly* the seam algebra (`knowSeam_eq_self_iff`) — a function
                          of `J` alone, so the subalgebra `E` projects onto is **fixed by the seam**
                          (`seam_forces_subalgebra`). The seamless `J=∅` case is `Orientation`'s
                          `dephase` (`knowSeam_empty`); a real self keeps strictly more. Hence the self
                          can never fully decohere itself (`self_cannot_fully_decohere`) — the seam is
                          permanent feeling, forced. **Aim vs orientation**: the contraction is uniform
                          in the seam (`direction_uniform_in_seam` — every `knowSeam J` lowers feeling)
                          while the target varies with it (`target_depends_on_seam`), so *knowing's
                          contractive nature orients the arrow; the seam aims it* — two distinct
                          obstructions. `[proved]` modulo the standing `J`↔genuine-seam `[reading]`.
                          ✅ verified.
* `Scratch.KnowingFromArrow` — **the converse**: from the arrow back to the knowing. Dual of
                          `TimeFlow`/`Orientation` — the `Arrow` interface carries `Flow`'s fields read
                          `V ⊢ E`, and on the genuine instance `partialDephase p` the orbit converges
                          entrywise to `dephase`, the knowing map `E` of `Orientation.dephaseKnowing`
                          (`arrow_limit_is_knowing`), which is idempotent (`limit_idempotent`), is the
                          seam-forced conditional expectation `knowSeam ∅` (`limit_is_seam_CE`), and
                          annihilates the very monovariant `defectSq` that defined the arrow
                          (`limit_annihilates_potential`) — *an arrow's limit is a knowing*, by
                          re-export. The general lift (every contractive arrow with trivial peripheral
                          spectrum) is `Scratch.MeanErgodic` (Conjecture R, `[open]`, gated out of this
                          build). `[proved]` instance. ✅ verified.
* `Scratch.Space`       — Part 1 of the space/energy spec: **space as the geometry of the coupling**.
                          From a coupling `len : A → A → ℝ≥0∞` (edge `= −log` coupling strength) the
                          path metric `dist i j = ⨅ walks` is a **quasi-pseudometric** (`dist_self`,
                          `dist_le_len`, `dist_triangle`; asymmetry a *theorem*, `dist_asymmetric`);
                          **separability ⟺ `d = ∞`** (`dist_eq_top_iff`, witness `couplingSep_dist` —
                          "space = coexistence minus connection"); and the **influence bound**
                          (`influence_bound`): reusing the `TimeFlow` decay engine on a weighted
                          dephasing flow, coherence between `i,j` after `n` closures is
                          `≤ exp(−n·d(i,j))·|Mᵢⱼ|` — influence propagates no faster than the coupling
                          distance permits. A weighted quasi-metric pre-geometry, not a manifold; the
                          "lightcone" is a propagation bound only. `[proved]` core, `[reading]` that it
                          *is* space. ✅ verified.
* `Scratch.RotatingSpectrum` — Parts 2–3 (the keystone): the **rotating peripheral spectrum** and
                          **energy**, on one concrete `ℂ` instance. `schur μ` is the phase-damping
                          channel (the `ℂ`-lift of `Space.wDephase`); `schur_iterate` gives the
                          per-edge geometric law, and the band of an edge is read off `‖μ i j‖`:
                          conserved (`schur_sustained`, `=1`) vs decaying (`schur_transient_tendsto`,
                          `<1`). The witness `quarterMul` on `Matrix (Fin 3) ℂ` carries all three bands
                          at once — fixed (diagonal), **rotating** (`μ₀₁ = i = e^{iπ/2}`, a genuine
                          rotating eigen-operator `Φ U = i·U`, `phaseChannel_eigen`, sustained
                          `rotating_sustained`), and transient (`transient_decays`). Part 3 (`[reading]`):
                          the modulus-one band is **energy** (conserved, `energy_conserved`), the
                          modulus-`<1` band is the **arrow** (`arrow_dissipates`); `energy_arrow_split`
                          shows both in one generator's spectrum. `[proved]` witness; the general CPTP
                          peripheral structure theorem stays the narrated `[open]`. ✅ verified.
* `Scratch.SpectralMultiplicity` — **Conjecture 3.7.4's new mathematics, closed**: the reconciliation of
                          *sparse* and *multiple*. Standard nonlinear Perron–Frobenius forces **uniqueness**
                          (`unique_fixed_of_global_contraction` — global contraction ⇒ one self, the
                          primitive/subhomogeneous regime); the doctrine's **contingency** needs *more than
                          one*. The bridge reads the abstract `‖x‖<1` of `Distribution` as the **linearization**
                          `x = DΦ_c`: `feedbackMap_contract` makes the living regime a contraction with rate
                          `‖x‖`, and `living_self_unique_attractor` exhibits `sustained x b` as the unique,
                          geometrically-reached attractor (piece 1). The **counting bound** (piece 3, the gem):
                          a locally attracting self is **isolated** (`attracting_isolated`), so distinct selves
                          are **`r`-separated** (`attractors_separated` — exclusivity *derived* from the gap,
                          not posited), and an `r`-separated set inside a capacity-`m` cover has `≤ m` points
                          (`separated_card_le_cover`), so the density of selves `→ 0`
                          (`selves_density_tendsto_zero`) — **independent of `N`**. Yet multiplicity is real: an
                          explicit two-basin map carries **two** genuine attractors (`two_attracting_selves`),
                          non-globally-contracting exactly as uniqueness requires. So selves are `>1`
                          (contingency) and `o(N)` (sparse): controlled multiplicity, bounded by structure.
                          **The reading is closed too:** the basin `r` is built from the *literal* Fréchet
                          derivative `A = DΦ_c` with `‖A‖<1` (`attractingFixed_of_hasFDerivAt`, any real Banach
                          space, rate `(1+‖A‖)/2` set by the gap `1-‖A‖`), and the capacity is the **explicit**
                          `⌊(b-a)/r⌋+1` (`separated_card_le_of_Icc`), so the self-count is bounded entirely by
                          the gap (`selves_card_le_gap_capacity`) — only the note that operator norm dominates
                          the cone spectral radius is a definitional `[reading]`. ✅ verified.
* `Scratch.SeamComonoid` — **the seam is the non-comonoidal residue** (concrete layer; abstract layer
                          [`RelExist.Fox`](../RelExist/Fox.lean)). Fox's hallmark: *classical / copyable /
                          cartesian* is one notion — carrying a copy comonoid — and in the matrix model that
                          is `IsClassical` (`cartesian_iff_copyDefectFree`: copyable ⟺ `copyDefect = 0`). The
                          central theorem `seam_is_noncomonoidal_residue`: a seam state with a **live**
                          coherence carries **no** copy, and **no available knowing** (`attend S`, `S` disjoint
                          from the seam, via `attend_fixes_seam`) can move it into the copyable fragment. A
                          **self-inclusive** seam (a genuine between) forces such a state to exist
                          (`self_inclusion_forces_residue`), so the headline `seam_is_the_common_obstruction`:
                          every seam state carries a copy **iff** the seam has no between — the self, being
                          self-inclusive, is at once uncopyable, non-broadcastable, and incompletely
                          self-knowable, **three names for one missing comonoid**. `seam_two_faces` packages
                          the unification: one copy failure, the monoidal (no-broadcast, survives every
                          knowing) and cartesian (`dephase` cannot fix it) faces at once. ✅ verified.
* `Scratch.FoxTheorem` — **Fox's hallmark, mechanized** (milestone 6; abstract `Type`-level layer
                          [`RelExist.Fox`](../RelExist/Fox.lean)). The categorical §0.4 hallmark — *the
                          cartesian fragment is exactly the presence of a uniform, natural `Δ`* — discharged
                          over a genuine cartesian monoidal category by standing on mathlib's
                          `CategoryTheory.Monoidal.Cartesian.Comon_`: `cartesianComonoid` (every object a
                          comonoid, functorially — cartesian ⇒ natural copy), `comonoid_forced` (the
                          **uniqueness**: any comonoid's comul is THE diagonal, counit THE terminal map — the
                          copy is forced, not chosen), and `foxEquivalence` (`Comon_ C ≌ C` — comonoids ARE
                          the objects). Instantiated at `Type` (`foxEquivalenceType`, `comonoid_forced_type`)
                          and bridged to the doctrine's copy (`doctrine_copy_is_diagonal`: `Fox.cartesian`'s
                          `(x,x)` is mathlib's diagonal). So §3.2's forward hallmark + uniqueness + the sharp
                          equivalence are **mechanized, not cited**; the reverse direction (comonoid ⇒
                          cartesian, Fox's classical hard half) is not in mathlib and stays the one cited
                          result. ✅ verified.
-/
import Scratch.We
import Scratch.Identity
import Scratch.Attention
import Scratch.Trace
import Scratch.KnowingFeeling
import Scratch.Chemistry
import Scratch.Biology
import Scratch.Rel
import Scratch.RelCoherence
import Scratch.Recurrence
import Scratch.PartialTrace
import Scratch.MatrixModel
import Scratch.MatrixCoherence
import Scratch.Compact
import Scratch.NoCloning
import Scratch.SparsityReal
import Scratch.Decoherence
import Scratch.Classical
import Scratch.Distribution
import Scratch.Feedback
import Scratch.Attending
import Scratch.Conservation
import Scratch.Forgetting
import Scratch.Knowing
import Scratch.Registration
import Scratch.Marginal
import Scratch.RelationalMarginal
import Scratch.Convergence
import Scratch.Stabilization
import Scratch.Feeling
import Scratch.RelationalAppearance
import Scratch.QuantumSeam
import Scratch.GraphModel
import Scratch.DomainTraced
import Scratch.DomainFixpoint
import Scratch.Causation
import Scratch.SparsityPosits
import Scratch.Orientation
import Scratch.Peripheral
import Scratch.PeripheralAlgebra
import Scratch.IntCompose
import Scratch.QuantumSeamTrace
import Scratch.SelfApplication
import Scratch.SparsitySharing
import Scratch.SparsityCapstone
import Scratch.ConwayTrace
import Scratch.ValuationBoundary
import Scratch.IntConstruction
import Scratch.RelCompact
import Scratch.ReflexiveCompact
import Scratch.SpectralDecay
import Scratch.PerronFrobenius
import Scratch.TimeFlow
import Scratch.TimeArrow
import Scratch.SeamForcing
import Scratch.KnowingFromArrow
import Scratch.Space
import Scratch.RotatingSpectrum
import Scratch.SpectralMultiplicity
import Scratch.SeamComonoid
import Scratch.FoxTheorem
