# WS5 — Finite Attention and Incompleteness of Self-Representation: Obligation Analysis

## What is at stake

WS5 concerns a coalgebra `(U, ξ)` — the terminal `P_κ`-coalgebra `νP_κ` from WS1/WS2, whose points are relation-first objects — equipped with a second structure: a **finite-support weighting** over each object's relations, evolving under feed/starve dynamics. Two mathematically distinct claims live here, and their statuses diverge sharply.

**Claim 1 (incompleteness).** No object can carry a complete, faithful self-model. Formally: there is no point-surjection from an object onto its own space of self-descriptions. This is a Lawvere fixed-point / diagonal obstruction — the same engine behind Cantor, Tarski, Gödel. It is `(F,κ)`-robust: it depends only on the cardinality/surjectivity structure, not on the choice of observation functor. This is the clean win; a negative result the program *wants*.

**Claim 2 (dynamics).** The attention weights evolve on a simplex under replicator-with-mutation `ẋᵢ = xᵢ(fᵢ − f̄) + μ(uᵢ − xᵢ)`, and this dynamics (a) has a fixed point, (b) converges to it, and (c) never reaches a simplex vertex (no delta-collapse — the anti-collapse floor). Convergence is **conditional**: Banach contraction needs a genuinely contractive operator on a complete metric realization of `νP_κ`, and contractivity of the replicator-mutator is a hypothesis, not a theorem.

The non-triviality: the two claims must be reported at **different confidence levels**, and the formalization must not let the solid incompleteness theorem launder the conditional convergence claim into looking equally settled. The obligation is genuinely *split*.

**Ambient theory (shared across all candidates below).** ZFC with AFA modeled *coalgebraically* (no set-theoretic AFA axiom imported): the carrier is `Cofix (PkObj κ)` as established in WS1/WS2, `F = P_κ` (bounded powerset, `< κ` support), bisimulation = identity by terminality. No monad `T` or distributive law `λ` is required for Claims 1 or the metric structure; WS5 imports WS3's `alg`/`pkJoin` only if attention is defined to interact with composition. Target: Lean 4 / Mathlib, axiom budget `[propext, Classical.choice, Quot.sound]`.

---

## Candidate 1 — Incompleteness via Lawvere's fixed-point theorem (abstract form)

**Framing.** Cash out "no object fully knows itself" as: a self-model would be a surjection `e : A → (A → B)` in a cartesian-closed setting; Lawvere says if such a point-surjection exists then every `f : B → B` has a fixed point. Contrapositive: exhibit a `B` with a fixed-point-free endomap (`B = Prop` / `Bool` with negation) to kill the surjection.

**Signature.**
```lean
theorem ws5_no_complete_self_model {A B : Type u}
    (neg : B → B) (hneg : ∀ b, neg b ≠ b) :
    ¬ ∃ e : A → (A → B), Function.Surjective e
```

**Strategy.** Direct diagonalization: given surjective `e`, the map `d : A → B := fun a => neg (e a a)` is hit by some `a₀`, so `e a₀ = d`, giving `e a₀ a₀ = neg (e a₀ a₀)` — contradicts `hneg`. Two lines. Mathlib may already have this as `Function.cantor_surjective` / `Cardinal` machinery; port or inline.

**Success condition.** Theorem compiles axiom-free; `B := Bool`, `neg := not` instantiates `hneg`.

**Failure mode.** Not failure of the theorem (it's elementary) but of *adequacy*: if `A → B` is the wrong model of "space of self-descriptions" for the relational carrier, the theorem proves something true but off-target.

**Trade-off.** Maximally robust and cheap, but maximally *disconnected* from `νP_κ`. It proves incompleteness for an abstract `A`, not for the actual groundless object. Strongest as a lemma, weakest as a WS5 deliverable on its own.

---

## Candidate 2 — Incompleteness instantiated on the carrier `νP_κ`

**Framing.** Bind Candidate 1 to the real object: a self-model of `u : (νP_κ).X` is a surjection from (the relations of) `u` onto the descriptions of `u`. Take "descriptions" as `(νP_κ).X → Bool` (predicates on states) and show no state's relation-set surjects onto it — using that `(νP_κ).str u` is a `< κ`-sized set while `(νP_κ).X → Bool` is `≥ 2^κ`-sized.

**Signature.**
```lean
theorem ws5_carrier_incomplete (hinf : ℵ₀ ≤ κ) (u : (νPk κ).X) :
    ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop), Function.Surjective e
```

**Strategy.** Two independent routes. (a) *Cardinality:* `mk ↥((νPk κ).str u).1 < κ ≤ mk (νPk κ).X ≤ mk ((νPk κ).X → Prop)`, and `Cardinal.cantor` blocks surjection onto a strictly larger type. (b) *Diagonal:* Candidate 1 with `A := ↥((νPk κ).str u).1`, `B := Prop`, `neg := Not` (needs `Classical` for `Not b ≠ b`). Route (a) is cleaner and reuses the `< κ` support bound that is the load-bearing WS1 fact.

**Success condition.** Compiles; the `< κ` bound is genuinely consumed (mirrors how WS1/WS3 consume regularity/infiniteness), tying incompleteness to *finite (bounded) attention* rather than a generic diagonal.

**Failure mode.** If one instead chose "descriptions" = `(νP_κ).str u` itself (same `< κ` bound both sides), the surjection is *not* blocked — a state can enumerate its own immediate relations. This is the real content: incompleteness bites only when the description space out-sizes the attention support. If the modeling collapses the two, the obligation *vanishes* (falsely trivializes).

**Trade-off.** On-target and still robust to `(F,κ)`. Slightly heavier (cardinal arithmetic on the carrier). This is the recommended *primary* incompleteness deliverable.

---

## Candidate 3 — Finite attention as an explicit structure + starvation dynamics (discrete)

**Framing.** Cash out "finite attention" concretely: an attention state on `u` is a finitely-supported weight `α : ↥((νP_κ).str u).1 → Q` (reuse WS4's `WQObj`-style bounded support, or `Finsupp`). Model one feed/starve step as a map `step : Attn → Attn` and prove the **plurality floor**: if a mutation parameter `μ > 0` is present, no reachable state is a Dirac delta (support stays ≥ 2).

**Signature.**
```lean
structure Attn (κ : Cardinal.{u}) (u : (νPk κ).X) where
  w    : ↥((νPk κ).str u).1 → ℝ
  supp_lt : Cardinal.mk (↥{r | w r ≠ 0}) < κ
  nonneg  : ∀ r, 0 ≤ w r
  sums_one : ∑' r, w r = 1        -- simplex constraint

theorem ws5_plurality_floor (μ : ℝ) (hμ : 0 < μ)
    (step : Attn κ u → Attn κ u)
    (hstep : ∀ a r, μ * (uniform r) ≤ (step a).w r)   -- mutation injects a floor
    (a : Attn κ u) (r : _) : (step a).w r > 0
```

**Strategy.** Pure inequality bookkeeping: the mutation term `μ(uᵢ − xᵢ)` adds a strictly positive lower bound `μ·uᵢ` to every coordinate after a step, so no coordinate hits `0`; hence support never shrinks to a singleton — no delta-collapse. No fixed-point theory needed.

**Success condition.** The floor is `> 0` unconditionally given `μ > 0`; delta-collapse (dynamical singularity) is provably excluded.

**Failure mode.** *Dynamical collapse* = some reachable `step^n a` is a vertex (single nonzero coordinate). If `μ = 0` the floor is `0` and collapse is *possible* — this is exactly why `μ > 0` is load-bearing and must appear as a hypothesis, not be assumed away.

**Trade-off.** Captures the anti-collapse commitment crisply and cheaply, but the `sums_one` over a `< κ`-support (`tsum`) and the real-analytic simplex are fiddly in Lean. Discretizing (one `step`) sidesteps ODE formalization entirely — recommended over any continuous-time attempt.

---

## Candidate 4 — Convergence via Banach fixed point (conditional, honest)

**Framing.** Cash out "attention settles into a stable partial self-image" as: on a complete metric realization `(M, d)` of `νP_κ` (America–Rutten / Turi–Rutten), a contractive attention operator `T_att` has a unique fixed point. State it **with contractivity as an explicit hypothesis** — do not claim the replicator-mutator *is* a contraction.

**Signature.**
```lean
theorem ws5_attention_converges
    {M : Type u} [MetricSpace M] [CompleteSpace M]
    (Tatt : M → M) (K : ℝ) (hK : K < 1)
    (hcontr : ∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) :
    ∃! p, Tatt p = p
```

**Strategy.** Direct application of Mathlib's `ContractingWith.exists_fixedPoint` / `Banach`. Trivial *given* the hypothesis. The entire scientific weight is in a *separate, unproved* lemma `replicator_mutator_contracts : ∀ …, ∃ K < 1, …` which is **not** discharged and must be flagged as the open obstruction (analogous to WS4's Layer C typed hole).

**Success condition.** The conditional theorem compiles; the contractivity hypothesis is quarantined as a named premise, never silently instantiated.

**Failure mode.** *Non-convergence.* If the replicator-mutator is not a contraction for the relevant `μ` (plausible under ungrounded self-reference — expansive or chaotic regimes), no fixed point is guaranteed and the premise is vacuously carried. Reporting this theorem as if convergence were *established* (rather than *conditional*) is the specific dishonesty the split-status requirement forbids.

**Trade-off.** Cheap and correct as stated, but its usefulness is entirely hostage to the unproved contraction lemma. Must be paired with an explicit `sorry`-free *statement* (typed obligation) of that lemma, left open.

---

## Candidate 5 — Convergence via replicator Lyapunov / KL-divergence (alternative dynamics route)

**Framing.** Instead of Banach, cash out convergence via a Lyapunov function: relative entropy `D(x* ‖ x)` to an interior equilibrium `x*` is non-increasing under the replicator-mutator flow, giving convergence to the interior (and simultaneously the plurality floor, since KL blows up at the boundary).

**Signature.**
```lean
theorem ws5_lyapunov_descent
    (f : Fin m → ℝ → ℝ)   -- fitness
    (μ : ℝ) (hμ : 0 < μ) (xstar : Fin m → ℝ) (hint : ∀ i, 0 < xstar i)
    (V : (Fin m → ℝ) → ℝ) (hV : V = fun x => ∑ i, xstar i * Real.log (xstar i / x i))
    (flow : ℝ → (Fin m → ℝ)) (hflow : IsReplicatorMutator flow f μ) :
    ∀ t, deriv (fun s => V (flow s)) t ≤ 0
```

**Strategy.** Compute `dV/dt` along the flow; for the pure replicator it is `−Var_x(f)` (Fisher's theorem); the mutation term contributes a further non-positive KL term. Requires real analysis + `deriv` of a composite — heavier than Banach but yields interiority *and* descent together.

**Success condition.** `dV/dt ≤ 0` with equality only at `x*`; boundary excluded because `V → ∞` there.

**Failure mode.** Same as Candidate 4 (dynamics need not converge) *plus* the Lyapunov function may fail to be monotone if fitness `f` is state-dependent in a non-gradient way — then no descent, obstruction sharper.

**Trade-off.** Unifies convergence + interiority (subsumes part of Candidate 3), but the ODE/`deriv` formalization cost is high and Mathlib's replicator-dynamics support is thin. Higher payoff, higher risk. Best deferred unless continuous-time is essential.

---

## Candidate 6 — The split-status assembly (meta-deliverable)

**Framing.** The actual WS5 obligation is not one theorem but a *bundle that records two different statuses*. Cash this out as a structure whose incompleteness field is a proved theorem and whose convergence field is explicitly *conditional* (carries its contractivity hypothesis as data), so no importer can read them at equal confidence.

**Signature.**
```lean
structure WS5FiniteAttention (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) where
  -- Discharged (Impossibility-proved, (F,κ)-robust):
  incomplete   : ∀ u : (νPk κ).X,
                   ¬ ∃ e : ↥((νPk κ).str u).1 → ((νPk κ).X → Prop), Function.Surjective e
  -- Discharged (anti-collapse floor, needs μ>0):
  no_delta     : ∀ (μ : ℝ), 0 < μ → PluralityFloor μ
  -- CONDITIONAL (typed open obligation — contractivity NOT proved):
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M]
                   (Tatt : M → M) (K : ℝ), K < 1 →
                   (∀ x y, dist (Tatt x) (Tatt y) ≤ K * dist x y) → ∃! p, Tatt p = p
  -- The obstruction, named and left open (no inhabitant):
  contraction_open : Prop   -- := replicator_mutator_contracts, deliberately unproved
```

**Strategy.** Bundle Candidates 2 + 3 (proved) with Candidate 4 (conditional) and register `contraction_open` as a typed hole — the WS4 `WQPreservesWeakPullback` discipline transplanted. Name the top bundle `ws5_incompleteness_and_conditional_convergence`, *not* `ws5_resolved`, so the proved incompleteness cannot launder the open convergence.

**Success condition.** Bundle compiles; the two proved fields are axiom-free; the conditional field visibly carries its hypothesis; `contraction_open` has no inhabitant.

**Failure mode.** The characteristic WS5 dishonesty: proving incompleteness + plurality and *naming the bundle as if convergence were closed*. Guarded against structurally by the naming and the typed hole.

**Trade-off.** The most faithful rendering of the obligation and the recommended top-level shape. Costs nothing beyond assembling the parts; its only "risk" is that it honestly displays an open problem rather than hiding it.

---

## Cross-cutting trade-off summary

The obligation bifurcates by *robustness to the shared `(F,κ)` parameter*: Candidates 1–3 (incompleteness + plurality floor) are `(F,κ)`-robust and dischargeable now, cheaply, axiom-free — Candidate 2 is the on-target incompleteness win, Candidate 3 the anti-collapse floor. Candidates 4–5 (convergence) are irreducibly *conditional*: they hinge on an unproved contractivity/Lyapunov-descent lemma that ungrounded self-reference may genuinely violate, so the honest deliverable states convergence *with its hypothesis exposed* and routes the contraction lemma to an open obligation. Candidate 6 is the assembly that keeps the two confidence levels separate — the single most important structural requirement, since the failure mode unique to WS5 is not a false theorem but a *true theorem misreported as settling more than it does*. Recommended path: **2 + 3 proved, 4 conditional, 6 as the honest bundle**; treat 1 as a reusable lemma and 5 as optional higher-payoff future work.
