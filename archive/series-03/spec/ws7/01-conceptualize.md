# WS7 — Non-collapse and the Goldilocks band

## What is at stake

WS7 is the collector. Every prior workstream states its theorems "for `κ` infinite regular" and leaves the concrete value of `κ` (and the functor `F`, the mutation floor `μ`, and now the quantale cardinality `#Q`) unfixed. WS7's obligation is to show that a *single* concrete parameter tuple simultaneously satisfies every constraint the other workstreams imposed — or to prove no such tuple exists (which is itself a valid terminal result).

The mathematical object at stake is a **nonempty region in parameter space**: the set of tuples `(F, κ, μ, #Q)` such that all of the following hold at once:

1. **Richness floor (structural non-collapse):** `νF` has ≥2 non-bisimilar states; branching ≥2 survives. Guards against `νF` being a single point.
2. **Boundedness (existence + non-totalization):** `F` is `κ`-bounded so `νF` exists as a set (`Cofix` route) and no maximal/universal element exists (`ws6_no_maximal`).
3. **Weak-pullback preservation:** the WS2/WS4 inherited duty — required for bisimulation = behavioural equivalence, and for the graded weak law's Layer C.
4. **Plurality floor (dynamical non-collapse):** `μ > 0` keeps replicator-with-mutation off the simplex vertices; attention never starves to a delta.
5. **Cardinality side condition:** `#Q ≤ κ` so the QPF shape count is legal.

**Why non-trivial.** The constraints pull against each other. Richness pushes `F` to distinguish more (larger branching, richer observation); boundedness caps it (`< κ` support). The two are plausibly jointly satisfiable for `P_κ`/`P_fin`, but the *dynamical* condition (4) is analytic, not combinatorial, and is not implied by (1)–(2): a floored, non-degenerate carrier can still host a non-contractive attention operator. So the band could be nonempty on the static axes and empty on the dynamic one, or nonempty for `P_κ` but empty once the quantale enrichment forces `κ > #Q`. The honest terminal outcomes are genuinely two-valued: exhibit a witness tuple, or prove the intersection empty.

The imported base (established, axiom-free): `PkObj`, `PkMap(_id/_comp)`, `νPk`, `νPk_terminal`, `ws2_nondegenerate`, `Bisim`, `diagBisim`, `ws2_weak_pullback` (for plain `P_κ`), `ws6_no_maximal`, and from WS5 the `Attn`/floor machinery and `ws5_attention_converges` (Banach step). Ambient theory throughout: AFA modeled coalgebraically (`νP_κ = Cofix (P_κ)`), no set-theoretic AFA axiom; `F = P_κ` unless a candidate explicitly enriches to `W_Q`; no monad/distributive law at the WS7 layer (composition is WS3/WS4's concern — WS7 consumes only their carriers). Axiom budget target `[propext, Classical.choice, Quot.sound]`.

---

## Candidate 1 — Static band as a nonempty existence witness

**Framing.** Cash the band out as: there exists a concrete `κ` (and, at the `P_κ` functor) for which richness, boundedness, and no-maximality hold simultaneously. Ignore the dynamical axis; deliver the combinatorial core as an outright existence theorem.

**Signature.**
```lean
theorem ws7_static_band (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) :
    (∃ a b : (νPk κ).X, a ≠ b)                              -- richness ≥ 2
  ∧ (∀ u : (νPk κ).X, ¬ (∀ v, v ∈ ((νPk κ).str u).1))       -- no maximal
  ∧ PkPreservesWeakPullback κ                               -- weak-pullback
```

**Strategy.** Each conjunct is already available: `ws2_nondegenerate hinf`, `ws6_no_maximal hcard` (unfolding `IsMaximal`), `ws2_weak_pullback`. The theorem is an assembly that certifies they hold *together* under one hypothesis pair, plus a non-vacuity witness that `hcard` is satisfiable (needs `mk (νPk κ).X ≥ κ`, the WS1 carrier lower bound — supply it or carry as hypothesis).

**Success condition.** All three conjuncts inhabited under a jointly-satisfiable hypothesis; the hypothesis pair `(hinf, hcard)` demonstrably non-empty (some `κ` meets both).

**Failure mode.** Would fail if `hcard` and `hinf` cannot cohold (no `κ` with the carrier reaching cardinality `κ`) — i.e. the boundedness/richness axes conflict at the cardinal level. Then the static band is empty: **Impossibility proved** on the static axis.

**Trade-off.** Cheapest and almost certainly provable, but weakest: silent on dynamics (4), so it cannot be reported as full non-collapse. It launders nothing only if named `ws7_static_band`, not `ws7_resolved`.

---

## Candidate 2 — Full band including the dynamical axis, conditional on contraction

**Framing.** Add the plurality/convergence axis but keep the contraction as an exposed hypothesis (the WS5 discipline). The band is the static core ∧ a conditional convergence field.

**Signature.**
```lean
structure GoldilocksBand (κ : Cardinal.{u}) (μ : ℝ) where
  hinf         : ℵ₀ ≤ κ
  hcard        : κ ≤ Cardinal.mk (νPk κ).X
  richness     : ∃ a b : (νPk κ).X, a ≠ b
  no_maximal   : ∀ u : (νPk κ).X, ¬ (∀ v, v ∈ ((νPk κ).str u).1)
  weak_pb      : PkPreservesWeakPullback κ
  plurality    : 0 < μ
  converges_if : ∀ {M : Type u} [MetricSpace M] [CompleteSpace M] [Nonempty M]
                   (T : M → M) (K : ℝ≥0), K < 1 →
                   (∀ x y, dist (T x) (T y) ≤ K * dist x y) → ∃! p, T p = p

theorem ws7_band_conditional (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X)
    (hμ : 0 < μ) : Nonempty (GoldilocksBand κ μ)
```

**Strategy.** Static fields as in Candidate 1; `converges_if := ws5_attention_converges`; `plurality := hμ`. The contraction premise is never discharged — it stays inside `converges_if`'s hypotheses, character-for-character the WS5 conditional.

**Success condition.** Bundle inhabited; `converges_if` provably the WS5 Banach conclusion with contraction still hypothetical.

**Failure mode.** Same static failure as C1. The dynamical axis cannot *fail* here because it is never asserted unconditionally — which is exactly the honesty cost.

**Trade-off.** Reports the full band shape while being truthful that dynamics is conditional. Named `ws7_band_conditional`, not `ws7_resolved`. Strictly stronger packaging than C1, strictly weaker than proving contraction.

---

## Candidate 3 — Discharge the dynamical axis by *constructing* a contraction

**Framing.** Cash out the hardest axis: exhibit a concrete replicator-with-mutation operator on a complete metric realization of the floored attention simplex and *prove* it contracts for `μ` in a stated range, closing the WS5 open obligation `replicator_mutator_contracts`.

**Signature.**
```lean
theorem ws7_mutation_contracts (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {M : Type u} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    (T : M → M) (hRM : IsReplicatorMutator T μ) :
    ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (T x) (T y) ≤ K * dist x y
```

**Strategy.** Model `M` as the finite-support probability simplex under total-variation (or an `ℓ¹`) metric. Decompose `T = (1−μ)·R + μ·U` where `R` is the replicator selection map and `U` the uniform-mutation pull. Bound the Lipschitz constant of the mutation term by `(1−μ)` on the affine combination (uniform pull is a strict convex contraction toward the barycenter), and control `R`'s expansion on the μ-floored interior (weights bounded below by `μ·min unif`, so the selection map's derivative is bounded). Take `K = 1 − cμ` for a geometric constant `c`. This is the "one genuinely new proof" of the dynamical axis.

**Success condition.** A specific `K < 1` exhibited with the Lipschitz bound proved for all `μ ∈ (0,1]`.

**Failure mode.** If `R`'s expansion on the floored interior can exceed the mutation contraction for every `μ` — i.e. selection outruns mutation regardless of floor — no such `K` exists and the operator is non-contractive: **the "attention need not converge" risk realized**, an Impossibility on the dynamical axis (report as such, do not weaken to C2).

**Trade-off.** The only candidate that would move convergence from Partial to Discharged. Highest risk — the contraction may simply be false for the honest operator, or hold only on a sub-range of `μ` that must then be stated. Attack this first; it decides whether the whole band is Discharged or Partial.

---

## Candidate 4 — Emptiness result (the negative terminal outcome)

**Framing.** Instead of a witness, prove the intersection empty on some axis — a sharp negative counts as success. The cleanest target: prove the cardinality side condition and richness *conflict* for a specified enriched functor, so no legal `(κ, #Q)` exists.

**Signature.**
```lean
theorem ws7_band_empty_for (F_spec : FunctorSpec) :
    IsEmpty { p : Cardinal.{u} × Cardinal.{u} //
      p.2 ≤ p.1                                    -- #Q ≤ κ
    ∧ RichnessFloor F_spec p.1                       -- ≥2 branching survives
    ∧ Boundedness F_spec p.1 }                       -- νF exists as a set
```
(with `FunctorSpec`, `RichnessFloor`, `Boundedness` the WS7-local predicates typing the axes).

**Strategy.** Pick the adversarial enrichment (`#Q = 𝔠` unbounded quantitative quantale). Show boundedness forces `κ > 𝔠` while some other consumed constraint (e.g. a WS4 shape-count truncation) caps `κ ≤ 𝔠`, contradiction. A cardinal-arithmetic squeeze.

**Success condition.** `IsEmpty` inhabited for the adversarial `F_spec`.

**Failure mode.** Fails to be *interesting* if the emptiness holds only for a functor no workstream actually adopts; then it is a true theorem about the wrong object. The obligation is to prove emptiness for a functor genuinely on the table.

**Trade-off.** Turns a would-be failure into a §5 success, and sharply delimits which enrichments are admissible. Only worth pursuing if C1–C3 suggest the band really is empty on the cardinality axis; otherwise it proves a vacuous negative.

---

## Candidate 5 — Retro-validation as a universally-quantified survival theorem

**Framing.** WS7's distinctive collector duty: prove that fixing *one* concrete `κ₀` does not break any upstream "for `κ` regular" theorem. Cash out as a single theorem instantiating every consumed result at `κ₀`.

**Signature.**
```lean
theorem ws7_retro_validate (κ₀ : Cardinal.{u}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X) :
    Nonempty (WS2.WS2Characterization κ₀)
  ∧ (∀ u : (νPk κ₀).X, ¬ (∀ v, v ∈ ((νPk κ₀).str u).1))
  ∧ Nonempty (WS6.WS6NoPoles κ₀)
  ∧ (2 ≤ n → Nonempty (WS4.GradedWeakLawCoherence (Luk n) κ₀ hreg))
```

**Strategy.** Direct instantiation: `ws2_characterization hinf hreg`, `ws6_split_and_no_maximal hinf hcard`, `ws4_graded_law_coherence`. The content is *not* a new proof but a certificate that the conjunction survives one `κ₀` — the thing §6.1's management rule requires before anyone reports "done."

**Success condition.** All conjuncts inhabited at a single named `κ₀` with `hreg`, `hcard` co-holding.

**Failure mode.** Fails if regularity + the carrier lower bound `hcard` cannot cohold at any `κ₀` — e.g. if the WS1 lower bound is only available for `κ` where regularity fails. Then the workstreams were never jointly valid at one parameter: **the coupling was fatal**, document precisely which two theorems' hypotheses conflict.

**Trade-off.** Indispensable regardless of C1–C4 — it is the actual collector deliverable — but proves *survival at one point*, not that the point is dynamically good. Combine with C3 for a complete result; combine with C1/C2 for a Partial one.

---

## Recommended sequencing

C3 is the decision node: it alone separates a Discharged band from a Partial one, and it is the "one genuinely new proof." Attack it first. If C3 succeeds, assemble C5 (retro-validation) + C3 into a full non-collapse theorem. If C3 resists, fall back to C2 (conditional band) + C5, reporting **Partial** with the contraction obstruction made precise (which `μ`-range, which selection-vs-mutation inequality fails). C1 is the cheap floor everyone can stand on. C4 is held in reserve: pursue only if the arithmetic in C1/C5 exposes a genuine cardinality conflict, converting the failure into an Impossibility-proved success. Throughout, name assemblies to keep the dynamical axis structurally separable (`ws7_band_conditional`, never `ws7_resolved`), so a proved static core cannot launder an open contraction.
