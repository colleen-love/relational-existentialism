# Candidate Framings of the Open Obligations

Each open obligation below is cashed out in **3–7 alternative provable formulations**. Every candidate specifies: the Lean 4 signature to be proved, the ambient theory (functor `F`, monad `T`, distributive law `λ`, quantale/metric structure as relevant), a proof-strategy sketch, the success condition, and the explicit failure mode. All signatures are stated against the existing artifact API (`WQObj`, `WQMap`, `WQRel`, `WQPreservesWeakPullback`, `PkObj`, `PkRel`, `SelectionMap`, `SelectionLipschitz`, `FlooredSimplex`, `mutT`, `Cofix`, QPF machinery). Ambient set theory throughout is ZFC with AFA modeled *coalgebrally* — no set-level AFA axiom is imported; "non-well-founded object" = inhabitant of a terminal coalgebra `Cofix F`, and "bisimilarity = identity" is terminality. The bounded observation functor is `F = P_κ` (`κ`-bounded powerset, `PkObj κ`) or its `Q`-weighted refinement `W_Q` (`WQObj Q κ`, weightings of `< κ` support).

---

## OBLIGATION A — Weighted weak-pullback preservation (Layer C)

The predicate to inhabit or refute:

```lean
def WQPreservesWeakPullback (Q : Type u) [CompleteLattice Q] (κ : Cardinal.{u}) : Prop :=
  ∀ {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : WQObj Q κ X) (u : WQObj Q κ Z),
    WQRel (fun x z => ∃ y, R x y ∧ S y z) s u → ∃ t, WQRel R s t ∧ WQRel S t u
```

where `WQRel R s t := ∃ w : WQObj Q κ {p : X×Y // R p.1 p.2}, WQMap Prod.fst w = s ∧ WQMap Prod.snd w = t`, and `WQObj Q κ X = {ρ : X → Q // #(supp ρ) < κ}`, `WQMap f = pushforward-sup`. The already-proved pointwise fact is `weight_split : w ≤ a * ⊤ → ∃ b, a * b = w` in a `DivisibleQuantale`. The unweighted analogue `PkPreservesWeakPullback` is proved (`ws2_weak_pullback`, via a pullback-of-witnesses `M = {ab // mid ab.1 = mid ab.2}` bounded by `Cardinal.mul_lt_of_lt`). The weighted difficulty is that the naive composite weight `wR(x,y) ⊗ wS(y,z)` fails to sup-project to the correct marginals unless the middle's outgoing mass is `1` (non-normalization).

Ambient: `F = W_Q`, `Q` a `GoodQuantale` (comm. monoid + complete lattice, `1` = `⊗`-unit) or `DivisibleQuantale` (adds `tensor_section`). Witness `Q = Łₙ = Fin (n+1)`, `a ⊗ b = a + b ⊖ n`. No monad/`λ` here — this is a functor-preservation property, prior to the bialgebra.

### A1 — Full weighted preservation over a divisible quantale (the design's literal target)

```lean
theorem wqA1_preserves_weak_pullback (Q : Type u) [DivisibleQuantale Q]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) : WQPreservesWeakPullback Q κ
```

**Strategy.** Mirror `PkRel_comp_le`. Given a joint witness `w` on `graph (R∘S)`, its middle-projection `t := WQMap (mid ∘ γ) w` where `γ` picks a per-pair middle via `Classical.choice`. The pullback carrier `M = {(iR,iS) // mid iR = mid iS}` inherits `< κ` support from `Cardinal.mul_lt_of_lt hκ`. The new content over `Pk`: the *weight* on `M` must satisfy `sup over S-fibre = wS(y,z)` and `sup over R-fibre = wR(x,y)` **simultaneously**. Define `wM(iR,iS) := wR(iR) ⊗ (wS(iS) ⊘ wt) ⊗ ...` using residuation `⊘` from `tensor_section` to renormalize each middle `y` by its total outgoing weight `wt(y) = ⨆_z wS(y,z)`. `weight_split` supplies the factor. Discharge the two marginal equalities by `sSup` distributing over the residuated legs.

**Success.** The `∃ t` is produced with both `WQMap` marginals proved equal by `Subtype.ext` + `le_antisymm`.
**Failure mode.** *Non-existence of a consistent weight assignment*: the two marginal-sup constraints are jointly unsatisfiable because residuation `⊘` is not a section when `wt(y) ≠ 1` and `⊗` is not cancellative (Łₙ is non-idempotent, non-cancellative). Concretely, `wR(x,y) ⊗ b = wR(x,y)` may have no `b` giving the required `wS`-marginal. This is the non-normalization obstruction and it lands here as *no global witness*, not as a false theorem.

### A2 — Preservation restricted to normalized (row-stochastic) weightings

```lean
def Normalized {X : Type u} (s : WQObj Q κ X) : Prop := (⨆ x, s.1 x) = 1

theorem wqA2_preserves_on_normalized (Q : Type u) [DivisibleQuantale Q]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    {X Y Z : Type u} (R : X → Y → Prop) (S : Y → Z → Prop)
    (s : WQObj Q κ X) (u : WQObj Q κ Z)
    (hs : Normalized s) (hu : Normalized u)
    (h : WQRel (fun x z => ∃ y, R x y ∧ S y z) s u) :
    ∃ t, Normalized t ∧ WQRel R s t ∧ WQRel S t u
```

**Strategy.** Under normalization the middle total `wt(y) = 1` for the relevant `y`, so the naive composite `wR ⊗ wS` *does* project (the residuation step of A1 collapses to identity by `tensor_section a 1`). The pullback-carrier bound is unchanged. This is A1 with the obstructing hypothesis assumed away rather than solved.

**Success.** Marginals match on the nose (no residuation needed); `Normalized t` follows from `tensor_sSup`.
**Failure mode.** *Vacuity / scope collapse*: if `Normalized` excludes the objects actually reached by the terminal coalgebra `Cofix (W_Q)` (whose destructor need not be normalized), the theorem is true but does not feed bisimulation = behavioural equivalence on `νW_Q`. Failure = "the normalized subfunctor is not a subcoalgebra," i.e. `wqAlg`/`Cofix.dest` leaves the normalized locus.

### A3 — Lax preservation (composition-reflection up to `≤` in the quantale order)

```lean
def WQRelLE {X Y : Type u} (R : X → Y → Prop) (s : WQObj Q κ X) (t : WQObj Q κ Y) : Prop :=
  ∃ w, WQMap Prod.fst w ≤ s ∧ WQMap Prod.snd w ≤ t   -- pointwise ≤ in Q

theorem wqA3_lax_preservation (Q : Type u) [GoodQuantale Q] (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :
    ∀ {X Y Z} (R : X → Y → Prop) (S : Y → Z → Prop) (s u),
      WQRel (fun x z => ∃ y, R x y ∧ S y z) s u → ∃ t, WQRelLE R s t ∧ WQRelLE S t u
```

**Strategy.** Weaken the marginal-*equality* to marginal-*domination*. Then the naive composite weight always works: `wR ⊗ wS ≤ wR` and `≤ wS` need only monotonicity of `⊗` (`a ⊗ b ≤ a ⊗ ⊤`, and `a ⊗ ⊤ ≤ a` requires `⊤`-unitality — instead use `a ⊗ b ≤ a` iff `b ≤` the residual of `a` into `a`, which holds for `b ≤ 1`). Requires only `GoodQuantale`, not divisibility. No `Classical.choice` beyond the middle selection.

**Success.** Both lax legs discharged by monotonicity lemmas alone.
**Failure mode.** *Insufficiency for identity theory*: lax preservation yields a *lax* relation lifting whose bisimilarity is coarser than behavioural equivalence — so `wq_bisim_behavioural` (criterion ii for the enriched carrier) would *not* upgrade from this. Failure = the lax lifting identifies distinct behaviours (structural collapse of the quotient), detectable as `WQRelLE`-bisimilarity strictly containing the diagonal on a 2-state witness.

### A4 — Preservation for idempotent (frame) quantales, as a negative boundary

```lean
theorem wqA4_preserves_iff_idempotent (Q : Type u) [GoodQuantale Q] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hidem : ∀ a : Q, a * a = a) : WQPreservesWeakPullback Q κ
```

**Strategy.** When `⊗ = ⊓` (idempotent, i.e. `Q` is a frame), `W_Q` is essentially `P_κ` enriched by a frame-valued indicator, and the `Pk` proof ports verbatim: `wM = wR ⊓ wS` on the pullback carrier projects correctly because `⊓` *is* idempotent and commutative, so marginal sups are `⨆ (wR ⊓ wS) = wR ⊓ (⨆ wS)` and the middle-fibre sup is `1`-free. Reuse `PkRel_comp_le`'s carrier `M` with weights.

**Success.** Full `WQPreservesWeakPullback` for idempotent `Q`.
**Failure mode.** This candidate is *designed* to succeed but its role is to sharpen the boundary: paired with `ws4_quantitative_witness` (Łₙ non-idempotent for `n ≥ 2`), it localizes the whole obligation to the non-idempotent gap. "Failing" here would mean even the idempotent case breaks — which would indicate the pullback carrier bound itself (not residuation) is the problem, refuting the `Pk` port.

### A5 — Impossibility: no weighted weak-pullback preservation for any non-idempotent divisible `Q`

```lean
theorem wqA5_no_preservation (Q : Type u) [DivisibleQuantale Q] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hnonidem : ∃ a : Q, a * a ≠ a) : ¬ WQPreservesWeakPullback Q κ
```

**Strategy.** Construct a fixed four-object diagram (the KS-style diamond) `X = {x}`, `Y = {y₁,y₂}`, `Z = {z}`, `R x yᵢ` and `S yᵢ z` both hold, with a joint witness `w` on `graph(R∘S) = {(x,z)}` carrying weight `a` where `a⊗a ≠ a`. Show any `t : WQObj Q κ Y` forces `WQMap`-marginals `wR(x,y₁)⊗wR(x,y₂)`-type sup on the `Y`-fibre that cannot equal both `wR` (into `s`) and `wS` (out to `u`) simultaneously, because reconstructing `a` as a product across the split middle needs `b⊗b = a` with `b` unique, contradicting non-idempotence + the sup-projection. Diagonalize on the two middles.

**Success (as a §5 Impossibility = program success).** `WQPreservesWeakPullback Q κ → False` from the explicit witness.
**Failure mode of the candidate itself.** The diamond *does* admit a `t` after all (residuation rescues it), i.e. A1 is true — in which case A5 is simply false and A1 should be pursued. The two are mutually exclusive; proving either closes Layer C.

**Trade-offs (Obligation A).** A1 is the maximal prize (closes criterion (iv)'s weak-pullback leg outright) but risks being *false* — the non-normalization obstruction may be fatal, in which case effort is wasted unless redirected to A5. A2 and A3 are *safe partials*: A2 buys correctness by shrinking the carrier (risking non-subcoalgebra), A3 buys generality by weakening to lax (risking coarse bisimulation). A4 is cheap, certainly-true, and diagnostically valuable but doesn't touch the witness Łₙ. A5 is the dual gamble to A1: proving it is a *positive* structural finding ("quantitative composition is inherently non-strict, like the strict-`λ` no-go"), but it forecloses the weighted carrier's identity theory and forces WS-downstream onto A2/A3 fallbacks. Rational sequencing: attempt A4 first (cheap sanity + boundary), then fork A1 vs A5 by testing the diamond witness by hand, keeping A2/A3 as the guaranteed-deliverable floor.

---

## OBLIGATION B — Canonicity / uniqueness of the weak distributive law

Informal target: the Egli–Milner weak law `alg` (with `dest (alg t) = ⋃_{x∈t} dest x`) is not merely *a* workable weak law but the canonical/forced one for `F = P_κ` (and persists to `W_Q`). No monad-strict `λ : TF ⇒ FT` exists (`ws3_no_distributive_law : IsEmpty (DistLaw κ)` is proved). `T` = the finite-support (`< κ`) union monad; `F = P_κ`.

Ambient: `T` = `P_κ` as a monad (unit = singleton, join = `⋃`); `F = P_κ` as observation; weak law = EM-lifting. Quantale-graded version replaces both with `W_Q`.

### B1 — Uniqueness among weak laws satisfying the EM unit + multiplication squares

```lean
structure WeakDistLaw (κ : Cardinal.{u}) where
  alg     : PkObj κ (PkObj κ X) → PkObj κ X   -- schematically; realized on νPk
  unit    : ∀ x, alg (singleton x) = x
  mult    : ∀ t, dest (alg t) = pkJoin (PkMap dest t)
  -- (part-reflection etc. as in ws3)

theorem ws3B1_weak_law_unique (κ : Cardinal.{u}) (hκ : κ.IsRegular)
    (L L' : WeakDistLaw κ) : L.alg = L'.alg
```

**Strategy.** Show the multiplication square `dest ∘ alg = pkJoin ∘ PkMap dest` **determines** `alg` on `νPk` because `dest` is injective (Lambek: `dest` is an iso on the terminal coalgebra). Hence `alg = dest⁻¹ ∘ pkJoin ∘ PkMap dest`, a closed form with no freedom. Uniqueness is then `dest`-injectivity applied to the shared `mult` field. `κ.IsRegular` enters via `pkJoin`'s `< κ` bound.

**Success.** Any two weak laws with the EM multiplication square coincide.
**Failure mode.** *`dest` non-injective on the chosen carrier* (would contradict Lambek — so failure here signals a carrier error), **or** the multiplication square admits genuine freedom because `pkJoin` is not the unique join (multiple monad structures on `P_κ`). The latter is real failure: canonicity is false, there is a parametrized family of weak laws.

### B2 — Canonicity via the terminal/final weak-law universal property

```lean
theorem ws3B2_weak_law_terminal (κ : Cardinal.{u}) (hκ : κ.IsRegular) :
    ∃! alg : (PkObj κ (νPk κ).X → (νPk κ).X),
      (∀ x, alg (singleton x) = x) ∧
      (∀ t, (νPk κ).str (alg t) = pkJoin (PkMap (νPk κ).str t))
```

**Strategy.** Recast B1 as `∃!` directly: existence is the constructed `wqAlg`/`alg` from ws3; uniqueness is the B1 argument. Package as a universal property so downstream (`W_Q`) can invoke "the" law. Uses `νPk_terminal` for both halves.

**Success.** `ExistsUnique`, giving a canonical named `alg`.
**Failure mode.** Existence half already discharged in ws3, so failure = uniqueness half only, identical to B1's second failure mode (freedom in the join). If `∃!` fails it degrades gracefully to `∃` (already have it) — B2 cannot *lose* existing ground.

### B3 — Persistence to the graded carrier (canonicity transported along `W_Q → P_κ`)

```lean
theorem ws3B3_weak_law_persists (Q : Type u) [GoodQuantale Q] (κ : Cardinal.{u})
    (hκ : κ.IsRegular)
    (hred : WQObj Q κ = ... /- Bool-reduction wq_reduces_to_pk at Q = {⊥,1} -/) :
    ∃! wqalg : (WQObj Q κ (Cofix (WQObj Q κ)) → Cofix (WQObj Q κ)),
      (∀ x, wqalg (wqSingleton x) = x) ∧
      (∀ t, Cofix.dest (wqalg t) = wqJoin (WQMap Cofix.dest t))
```

**Strategy.** Two-step: (i) prove the graded EM law exists on `W_Q` (mostly done: `wqAlg`, `wqAlg_unit`, `wqAlg_pentagon`); (ii) transport uniqueness from B2 along the functor reduction `wq_reduces_to_pk` (step 16, currently open) which sends `W_Q` at the Boolean quantale back to `P_κ`. Uniqueness upgrades if the reduction is a coalgebra iso.

**Success.** Canonical graded law, closing the WS3→WS4 ratification.
**Failure mode.** The Bool-reduction `wq_reduces_to_pk` is itself unproved (step 16); if it fails to be a coalgebra morphism, the transport breaks and graded canonicity is *independent* of ungraded canonicity — must be proved from scratch at `W_Q`, where `wqJoin`'s `⊗`-scaling may admit a family (non-uniqueness). This is the likeliest failure: grading reintroduces freedom that Boolean `P_κ` did not have.

### B4 — Negative framing: canonicity fails, characterize the family

```lean
def WeakLawFamily (κ : Cardinal.{u}) : Type u := { alg // /- EM unit + mult -/ }

theorem ws3B4_weak_law_not_unique (κ : Cardinal.{u}) (hκ : κ.IsRegular) :
    ∃ L L' : WeakLawFamily κ, L.1 ≠ L'.1
```

**Strategy.** Exhibit two distinct union-like joins on `P_κ` both satisfying the EM squares — e.g. `⋃` versus a `κ`-twisted variant — differing on a non-degenerate witness. If found, canonicity is genuinely false and the honest report is "criterion (iv) delivered by a *choice* of weak law, family characterized."

**Success (as honest partial).** A concrete `L ≠ L'`, both valid — canonicity refuted, family exposed.
**Failure mode.** No two distinct laws can be built (B1 is true) — then B4 is false and B1/B2 should be pursued. Again mutually exclusive with B1.

**Trade-offs (Obligation B).** B1/B2 are the same result at two strengths (`=` vs `∃!`); B2 dominates because it can only improve on the existing `∃`. B3 is what the ratification actually needs (graded persistence) but is *gated on the open Bool-reduction* — so it inherits step-16 risk and may be unprovable until that lands. B4 is the escape hatch: if canonicity is false, proving B4 is still a valid §5 outcome (delivered-by-choice, family known). The dependency `B3 ⊃ B2 ⊃ B1` means effort compounds upward; recommend proving B2 (safe, self-contained), then attempting B3, and pivoting to B4 only if a second law is spotted while trying B3.

---

## OBLIGATION C — Convergence of the attention dynamics (Lemma B)

The open analytic fact: the replicator-with-mutation self-map `mutT` on the floored simplex is a contraction. The Banach step is already discharged conditionally (`ws7_attention_fixed_point` given `(1-μ)·L_R μ < 1`; `ws5_attention_converges` given any `K < 1`). What is missing inhabits:

```lean
structure SelectionLipschitz (S : Type u) [Fintype S] (unif : S → ℝ) (sel : SelectionMap S unif) where
  L_R   : ℝ → ℝ≥0
  bound : ∀ μ, 0 < μ → μ ≤ 1 → ∀ w ∈ floorRegion μ unif, ∀ w' ∈ floorRegion μ unif,
            dist (sel.R w) (sel.R w') ≤ (L_R μ) * dist w w'
```

with the crux `(1 - μ) * (sl.L_R μ) < 1`. Ambient: no functor/monad — this is real analysis on `FlooredSimplex S μ unif ⊆ (S → ℝ)`, `S = SelfSupport` of a state (finite by finite-attention), sup-metric, `MetricSpace`/`CompleteSpace` instances already provided.

### C1 — Replicator selection is globally Lipschitz on the floor; contraction for small μ

```lean
theorem ws7C1_replicator_contracts (S : Type u) [Fintype S] (unif : S → ℝ)
    (hu_pos : ∀ r, 0 < unif r) (hu_sum : ∑ r, unif r = 1)
    (f : S → ℝ) (hf : ∀ r, 0 ≤ f r)   -- fitness field, bounded
    (sel : SelectionMap S unif)
    (hsel : sel.R = replicatorField f) :
    ∃ (sl : SelectionLipschitz S unif sel), ∀ μ, 0 < μ → μ ≤ 1 → (1 - μ) * (sl.L_R μ) < 1
```

**Strategy.** The replicator field `w ↦ (wᵣ·(fᵣ − f̄(w)))` is smooth; on the compact floored simplex its Jacobian has bounded operator norm `L_R` (explicit: `L_R = 2·(max f − min f)` via the mean-field derivative). Then `(1−μ)·L_R < 1` holds for `μ > 1 − 1/L_R`, i.e. a *threshold on the mutation floor*. Provide `L_R μ` constant in `μ` and solve the inequality; if `L_R ≥ 1`, the contraction needs `μ` above threshold, which is a **hypothesis on μ**, not free.

**Success.** `SelectionLipschitz` inhabited *and* the contraction inequality holds for μ in an explicit range.
**Failure mode.** *Non-convergence / no contraction*: if `L_R > 1/(1−μ)` for all admissible μ (fitness spread too large relative to the floor), no contraction constant exists — the dynamics may cycle or be chaotic. This is the charter's "attention need not converge" realized as `∀ sl, (1-μ)·sl.L_R μ ≥ 1`. Detectable: replicator with `≥ 3` strategies and rock–paper–scissors fitness has periodic orbits (no fixed-point contraction).

### C2 — Entropy-regularized (softmax) selection is a contraction unconditionally on the floor

```lean
theorem ws7C2_softmax_contracts (S : Type u) [Fintype S] (unif : S → ℝ)
    (hu_pos : ∀ r, 0 < unif r) (hu_sum : ∑ r, unif r = 1)
    (β : ℝ) (hβ : 0 < β) (f : S → ℝ)
    (sel : SelectionMap S unif) (hsel : sel.R = softmaxField β f) :
    ∃ (sl : SelectionLipschitz S unif sel),
      ∀ μ, 0 < μ → μ ≤ 1 → (1 - μ) * (sl.L_R μ) < 1
```

**Strategy.** Replace the multiplicative replicator with the entropy-regularized update (softmax of `β·f` mixed with current), whose Lipschitz constant is `L_R = β·(max f − min f)/2` (softmax Jacobian bound, `‖∇softmax‖ ≤ β/2·diam`). For small temperature `β` this is `< 1` outright, giving contraction for *all* μ ∈ (0,1]. The charter names "entropy-regularized reinforcement" as equivalent to replicator-with-mutation, so this is a licensed model choice.

**Success.** Contraction with no μ-threshold, for `β < 2/((1−μ)·diam f)`.
**Failure mode.** *Model substitution rejected*: if softmax is deemed not to realize the intended feed/starve semantics (it smooths rather than starves), the theorem is true but off-target — failure = "converges, but not the dynamics the commitment specifies." Also fails if `β` must be large (sharp selection) to avoid dynamical collapse, recreating C1's tension.

### C3 — Contraction on a shrunk (interior) floor via strict positivity margin

```lean
theorem ws7C3_interior_contraction (S : Type u) [Fintype S] (unif : S → ℝ)
    (hu_pos : ∀ r, 0 < unif r) (hu_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ w ∈ floorRegion μ unif, ∀ r, ε ≤ w r) :
    ∃ (sl : SelectionLipschitz S unif sel), (1 - μ) * (sl.L_R μ) < 1
```

**Strategy.** On the ε-interior the replicator field's Jacobian norm is bounded by a *smaller* constant (division by `wᵣ ≥ ε` is controlled), giving `L_R(ε) = C/ε`-type bound but *combined* with the floor guarantee `μ·unif ≥` a positive margin, the product `(1−μ)·L_R` can be pushed below 1 by choosing μ so the floor forces `ε ≥ μ·min unif`. Self-consistent fixed point of the ε–μ relation.

**Success.** Contraction on the μ-floored region using the floor itself as the margin — closes the loop (the floor that prevents *dynamical collapse* is the same floor that gives *contraction*).
**Failure mode.** The ε–μ self-consistency has no solution (the margin needed for contraction exceeds the margin the floor provides): `μ·min unif < required ε` for all μ. Failure = floor strong enough to prevent collapse is too weak to force contraction — the two anti-collapse mechanisms are in tension, not harmony.

### C4 — Weakened target: convergence in Cesàro/time-average rather than pointwise fixed point

```lean
theorem ws7C4_cesaro_converges (S : Type u) [Fintype S] (unif : S → ℝ)
    (sel : SelectionMap S unif) (w₀ : FlooredSimplex S μ unif) :
    ∃ w∞, Filter.Tendsto (fun N => (1/N) • ∑ i in Finset.range N, (mutT^[i] w₀)) Filter.atTop (𝓝 w∞)
```

**Strategy.** Drop the contraction demand. The mutation step maps the compact convex floored simplex to itself continuously (`mutT` total, `mutationStep_maps_into`), so by Krylov–Bogolyubov / Markov–Kakutani there is an invariant measure and the time-averages converge even without a unique fixed point. Uses compactness + convexity, not contraction.

**Success.** Cesàro convergence unconditionally (no Lipschitz premise).
**Failure mode.** This nearly cannot fail (compact convex self-map always has a fixed point by Brouwer/Schauder), but the *result is weaker*: it gives *a* fixed point / average, not a *unique* attracting one, so it does not certify "attention settles into a stable partial self-image" — only "attention does not escape." Failure = weakest acceptable claim, may not meet the commitment's "settles" reading.

### C5 — Impossibility: no contraction exists (dynamical non-collapse fails for the pure replicator)

```lean
theorem ws7C5_no_contraction (S : Type u) [Fintype S] (hS : 3 ≤ Fintype.card S)
    (unif : S → ℝ) :
    ∃ (f : S → ℝ) (sel : SelectionMap S unif) (hsel : sel.R = replicatorField f),
      ∀ (sl : SelectionLipschitz S unif sel) μ, 0 < μ → μ ≤ 1 → 1 ≤ (1 - μ) * (sl.L_R μ)
```

**Strategy.** Take `S = 3` with rock–paper–scissors fitness `f`; the replicator has a center (Hamiltonian-like periodic orbits), so its Jacobian at the interior fixed point has purely imaginary eigenvalues → operator norm ≥ 1, and mutation `(1−μ)` scaling cannot bring the *worst-case* directional Lipschitz constant below 1 for the whole floor. Prove `L_R ≥ 1/(1−μ)` by exhibiting two floor points whose images separate at rate ≥ `1/(1−μ)`.

**Success (as §5 Impossibility / characterization).** Contraction provably impossible for pure replicator at `card ≥ 3` — the honest "dynamics do not converge" finding, itself informative.
**Failure mode.** RPS mutation actually *does* contract for μ above a threshold (the center becomes a sink under mutation) — then C5 is false and C1 with a μ-threshold is the truth. Mutually exclusive with C1's positive range.

**Trade-offs (Obligation C).** C1 is on-target (the literal replicator-with-mutation) but its success is *conditional on μ* and may be outright false at `card ≥ 3` (C5). C2 buys unconditional-in-μ contraction by switching to softmax — cheapest positive result, but risks the "not the specified dynamics" objection. C3 is the most *thematically satisfying* (the anti-collapse floor doubles as the contraction margin) but its self-consistency may have no solution. C4 is the near-certain fallback (compactness) but delivers only Cesàro/existence, not uniqueness/attraction. C5 is the dual to C1. Recommended order: C4 first as a guaranteed floor (some convergence always), C2 for a clean unconditional positive, then fork C1 vs C5 on the μ-threshold analysis, with C3 as the "best story if it works." Note C1/C3/C5 all turn on the same quantity `(1−μ)·L_R μ`; a single Jacobian-norm computation adjudicates all three.

---

## OBLIGATION D — General branching / richness floor (criterion iv-blocking)

The predicate (currently `RichnessGeneralStatus.open_iv_blocking`, never derived from the ≥2-states witness):

```lean
def GeneralBranching (κ : Cardinal.{u}) : Prop :=
  ∀ x : (νPk κ).X, ∃ y z, y ∈ ((νPk κ).str x).1 ∧ z ∈ ((νPk κ).str x).1 ∧ y ≠ z
```

i.e. *every* state has out-degree ≥ 2 (not just: two distinct states exist, which is `ws2_nondegenerate`). WS3's sharp non-triviality of `alg` relies on this. Ambient: `F = P_κ`, `νPk κ = Cofix (PkObj κ)`, terminal so bisimilarity = identity.

### D1 — General branching is FALSE as stated; correct target is a branching *subcarrier*

```lean
theorem ws7D1_general_branching_false (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ¬ GeneralBranching κ
```
then
```lean
def BranchingLocus (κ : Cardinal.{u}) : Set (νPk κ).X := { x | ∃ y z, y ∈ ((νPk κ).str x).1 ∧ z ∈ ... ∧ y ≠ z }

theorem ws7D1_branching_subcoalgebra (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ∃ (C : Coalg κ) (ι : C.X → (νPk κ).X), Function.Injective ι ∧
      (∀ x, x ∈ Set.range ι → x ∈ BranchingLocus κ) ∧ (2 ≤ #C.X)
```

**Strategy.** The empty state `∅` (image of `emptyCoalg`) and the `Ω = {Ω}` state (out-degree 1) are in `νPk` — both violate `GeneralBranching`. So `GeneralBranching` is refuted by `ws2_nondegenerate`'s own witnesses. The correct richness content is that the *branching locus* is non-trivial and forms a subcoalgebra: build `C` as the sub-coalgebra generated by a 2-branching seed (e.g. `{∅, Ω}`-rooted). WS3 non-triviality only needs `alg` to distinguish on *this* locus.

**Success.** `¬ GeneralBranching` + an inhabited branching subcarrier feeding WS3's `alg_nontrivial`.
**Failure mode.** The branching locus is not closed under `str` (a 2-branching state's successors are all single-branching), so no subcoalgebra — then even the restricted richness fails and `alg`'s sharp non-triviality has no carrier. Detectable by chasing successors of `{∅, Ω}`.

### D2 — Restrict the floor to the criterion-(iv)-relevant states only

```lean
def IVRelevantBranching (κ : Cardinal.{u}) (alg : PkObj κ (νPk κ).X → (νPk κ).X) : Prop :=
  ∀ t : PkObj κ (νPk κ).X, 2 ≤ #(t.1) →
    ∃ y z, y ∈ ((νPk κ).str (alg t)).1 ∧ z ∈ ((νPk κ).str (alg t)).1 ∧ y ≠ z

theorem ws7D2_iv_branching (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) (alg : ...)
    (halg : ∀ t, (νPk κ).str (alg t) = pkJoin (PkMap (νPk κ).str t)) :
    IVRelevantBranching κ alg
```

**Strategy.** Don't demand branching everywhere — demand that `alg` *preserves/creates* branching from ≥2-element inputs, which is all WS3 uses. From the multiplication square `str (alg t) = ⋃ str x`, a `t` with two members having distinct successors gives `alg t` out-degree ≥ 2. Direct from `pkJoin` unfolding + `ws2_nondegenerate`.

**Success.** The exact richness WS3 consumes, proved, without the false universal.
**Failure mode.** Two distinct members of `t` can have *identical* successor sets (their union does not increase branching) — then `alg t` may collapse to out-degree 1 and non-triviality fails on that input. Failure = `alg` merges branches, i.e. structural collapse localized to `alg`'s image.

### D3 — Quantitative richness: out-degree bounded below by a cardinal function

```lean
theorem ws7D3_branching_cardinal (κ : Cardinal.{u}) (hκ : κ.IsRegular) :
    ∃ x : (νPk κ).X, 2 ≤ #(((νPk κ).str x).1) ∧
    ∀ n : ℕ, ∃ x : (νPk κ).X, (n : Cardinal) ≤ #(((νPk κ).str x).1)
```

**Strategy.** Exhibit states of every finite out-degree (and up to `< κ`) by `corec` on explicit seed coalgebras (`Fin n` with full successor structure), transported to `νPk` by terminality. Establishes the carrier is "rich" in the strong sense that branching is *unbounded below κ*, dominating the ≥2 floor.

**Success.** Richness as an unbounded family, the strongest positive floor.
**Failure mode.** Terminality collapses distinct-out-degree seeds to the same `νPk` point (bisimilar despite different apparent branching) — would indicate the observation functor under-distinguishes, i.e. structural collapse at the carrier level (contradicting `ws2_bisim_eq`, so failure signals an upstream error).

**Trade-offs (Obligation D).** D1 confronts the likely fact that `GeneralBranching` *as written is false* (empty and `Ω` states refute it) and redirects to a subcarrier — most honest, but risks the locus not being a subcoalgebra. D2 is the *tightest fit to what WS3 actually needs* (branching through `alg`, not everywhere) and is the recommended primary; it fails only if `alg` merges branches. D3 overshoots into a strong quantitative floor that would also settle non-collapse richness (feeds WS7's structural band), at the cost of more `corec` construction. Since the artifact already flags `GeneralBranching` as open-and-`iv`-blocking rather than plausibly-true, D2 (reframe to `alg`-relative) is the lowest-risk closure; D1's negative half should be proved regardless to document that the universal form is unachievable.

---

## OBLIGATION E — Substantive standpoint / criterion (vi)

Current state: `ws6_standpoint_vacuous : ∀ obs, PositionFree obs` is proved (every observation is trivially position-free because `endo_eq_id` forces the only endo-view to be identity), which is *why* (vi) is NOT discharged — vacuity, not substance. The cross-category obligation is stated-not-proved:

```lean
def ws6_no_faithful_zero_host (κ : Cardinal.{u}) : Prop :=
  ∀ (C : Type u) [Category.{u} C] [HasZeroObject C] (D : Type u) [Category.{u} D],
    IsEmpty (FaithfulCarrierEmbedding κ D C)
```

Ambient: `F = P_κ`, `νPk` lives in `Set`/`Type u`; the zero-object facet requires a category `C` with `HasZeroObject`, which `Type u` lacks (`∅ ≠ PUnit`). The tension: the groundless carrier and the pole-coincidence object may inhabit *different categories*.

### E1 — Criterion (vi) via non-terminal spans: substantive standpoints exist as internal sections

```lean
structure Standpoint (κ : Cardinal.{u}) where
  base    : (νPk κ).X
  view    : (νPk κ).X → PkObj κ (νPk κ).X   -- a span, NOT the identity endo-view
  local'  : view base = (νPk κ).str base
  partial : ¬ Function.Surjective view       -- positioned: sees only part

theorem ws6E1_substantive_standpoints (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ∃ sp : Standpoint κ, ∀ sp' : Standpoint κ, sp.base ≠ sp'.base → sp.view ≠ sp'.view
```

**Strategy.** Model a standpoint as a *sheaf-like local section* indexed by its base object, not as a global endo-view. `endo_eq_id` only kills *global terminal* observers; a based, partial `view` is not an endo-map of the terminal object and escapes the vacuity. Distinct bases give distinct positioned views (no view from nowhere = no base-free surjective view). Success realizes (vi)'s "every genuine view is internal, indexed by the object that holds it."

**Success.** A family of genuinely distinct, positioned, non-surjective standpoints — (vi) discharged with content.
**Failure mode.** All based views collapse to identity anyway (terminality is stronger than expected and `view` is forced to `str`), reproducing vacuity at the span level = *standpoint collapse*: no substantive perspective exists, (vi) is trivially-only-true.

### E2 — Criterion (vi) as an impossibility: no substantive TERMINAL standpoint (the intended reading)

```lean
theorem ws6E2_no_terminal_standpoint (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ (obs : (νPk κ).X) (see : ∀ x, x = obs ∨ x ∈ ((νPk κ).str obs).1),
      Function.Surjective (fun x => x ∈ ((νPk κ).str obs).1)
```

**Strategy.** (vi) says there is *no view from nowhere* — reframe as: no single object observes all others (no surjective global observer). This is a Cantor/Lawvere-diagonal argument: a state seeing all states would need out-degree `= #νPk`, exceeding `< κ` support. Direct from the `< κ` bound (mirror `ws6_no_maximal`). This reads (vi) as an *impossibility to be proved*, which the charter counts as success.

**Success (§5 Impossibility).** No terminal/global standpoint exists — the negative content of (vi), fully discharged.
**Failure mode.** A `< κ`-supported state *can* reach every state (if `#νPk < κ`, i.e. the carrier is too small) — then a global observer exists = *standpoint collapse to a God's-eye view*, the exact singularity commitment 6 forbids. Detectable via `κ ≤ #νPk` (already used in `ws6_no_maximal`).

### E3 — Resolve the category split: exhibit ONE ambient category hosting both facets

```lean
theorem ws6E3_common_ambient (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ∃ (C : Type (u+1)) (_ : Category.{u} C) (_ : HasZeroObject C)
      (embed : (νPk κ).X → C),
      Function.Injective embed ∧ (/- P_κ-coalgebra structure transported into C -/)
```

**Strategy.** Take `C = ` pointed sets `Set_*` (or `κ`-ary `Set_*`), which *has* a zero object (the one-point set) and *faithfully hosts* `νPk` (add a disjoint basepoint). Prove the embedding is faithful and carries the coalgebra. This directly *refutes* `ws6_no_faithful_zero_host` (as the artifact predicts it is "almost certainly false as a blanket") — the finding being that pole-coincidence and groundlessness *can* cohabit, so the split is avoidable.

**Success.** `¬ ws6_no_faithful_zero_host` witnessed by pointed sets; both facets in one category.
**Failure mode.** The basepoint breaks either faithfulness (distinct carrier states identified in `C`) or the coalgebra transport (`P_κ` structure not preserved by the pointing) — then the split is *forced*, the pole-coincidence object and groundless carrier are genuinely different objects, and (vi)+pole-coincidence cannot be jointly realized (a real negative for commitment 3's "same refusal" claim).

### E4 — Concede vacuity, relocate (vi) to the dynamical (attention) layer

```lean
theorem ws6E4_perspectival_via_attention (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    ∀ u : (νPk κ).X, ∃ (a : Attn κ u),
      (∀ a' : Attn κ u, a ≠ a' → /- distinct attention = distinct standpoint -/ True) ∧
      ¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e
```

**Strategy.** Grant that the *static* terminal carrier has no substantive standpoint (vacuity is honest), and realize (vi) instead through WS5's finite attention: a standpoint *is* a finite-support attention weighting, and `ws5` already proves no attention surjects onto its own self-descriptions (`incomplete`). Perspective = positioned attention, and "no view from nowhere" = incompleteness of every attention's self-model. Reuses proved WS5 content.

**Success.** (vi) discharged as a *dynamical* rather than *structural* property, leveraging `ws5.incomplete`.
**Failure mode.** This is a *relocation*, not a discharge of the structural (vi) the criterion names — if downstream requires (vi) at the carrier level, this is off-target ("perspective exists dynamically but the static object still has no standpoint"). Categorized as declared substitution, not closure.

**Trade-offs (Obligation E).** E2 is the *cleanest and most likely-provable* (impossibility of a global observer, directly from the `< κ` bound, parallel to `ws6_no_maximal`) — it captures the "no view from nowhere" negative that the charter treats as the real content of (vi). E1 attempts the *positive* (substantive positioned views exist) and is the richest if it works but risks span-level vacuity. E3 tackles the category split head-on and its likely outcome is a *negative* (`ws6_no_faithful_zero_host` false → split avoidable, OR faithfulness fails → split forced); either way it resolves the WS6↔WS1 coupling the audit flags. E4 is the fallback that reuses proved WS5 machinery but relocates the criterion to the dynamical layer (declared substitution). Recommended: E2 as primary (discharges the negative reading cheaply), E3 to settle the structural coupling (its answer is informative in both directions), E1 as the ambitious positive, E4 only if E1 collapses. E2 and E1 together would give both the "no God's-eye view" and "genuine internal views exist" halves that (vi) really wants.

---

## Cross-obligation summary of failure taxonomy

| Obligation | "Collapse" failure | "Non-existence" failure | "No law / no contraction" failure |
|---|---|---|---|
| A (weak-pullback) | lax lifting coarsens bisimulation (A3) | no global weight witness (A1→A5) | — |
| B (canonicity) | — | uniqueness fails, family exists (B4) | multiple valid weak laws (B1) |
| C (convergence) | floor-vs-contraction tension (C3) | only Cesàro, no unique attractor (C4) | no contraction, cycles at card≥3 (C5) |
| D (branching) | `alg` merges branches (D2); terminality merges seeds (D3) | branching locus not a subcoalgebra (D1) | — |
| E (standpoint vi) | global observer exists → God's-eye view (E2); span vacuity (E1) | no common ambient category (E3) | — |

Each obligation admits a matched positive/negative pair (A1↔A5, B2↔B4, C1↔C5, D2↔D1, E1↔E2) such that *whichever holds is a valid terminal outcome*; the negative members are impossibility results that count as success. Recommended global sequencing prioritizes the cheap certain-floor member of each family (A4, B2, C4, D2, E2) to guarantee a deliverable, then forks on the genuine unknowns (A1/A5, C1/C5, E3).
