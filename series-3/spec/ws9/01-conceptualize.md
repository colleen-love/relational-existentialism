# WS9 · 01 — Conceptualize (blind)

*Blind register. Mathematical statement only; downstream phases treat this as the BR.*

## 0. The object and the property at stake

The upstream development (WS5/WS7) fixes a discrete dynamical system on a finite
metric simplex:

- **State space.** `FlooredSimplex S μ unif := { w : S → ℝ // (∀ r, μ·unif r ≤ w r) ∧ ∑ r, w r = 1 }`
  — the probability simplex on a finite type `S`, intersected with a uniform floor
  `w r ≥ μ·unif r`. It is a nonempty (for `μ ≤ 1`) complete metric space in the sup
  (`ℓ∞`) metric.
- **Selection.** `SelectionMap S unif` = a map `R : (S→ℝ) → (S→ℝ)` preserving
  nonnegativity and mass (`∑ w = 1 ⇒ ∑ R w = 1`).
- **Dynamics.** `mutationStep μ unif sel w := (1−μ)·(R w) + μ·unif`, restricted to a
  self-map `mutT : FlooredSimplex → FlooredSimplex`. This is one replicator‑mutator
  ("feed/starve") step: selection `R`, then a `μ`-fraction pull toward `unif`.

Upstream (WS8) proves a **sufficient** convergence result: whenever the step is a
Banach contraction — `(1−μ)·L_R < 1` for a sup‑metric Lipschitz constant `L_R` of the
selection — the iteration has a unique fixed point (`ws8_replicator_converges` for the
linear replicator `R(w)_r = w_r c_r / ∑ w_s c_s`; `ws8_exp_replicator_converges` for the
exponential `R(w)_r = w_r exp(f_r w)/Z(w)`). Both hold on an explicit **band**
`μ > μ⋆(sel)`.

**The property at stake for WS9 is the *converse boundary*: characterizing the region
of parameter space `(S, unif, μ, R)` on which `mutT` actually converges to a unique
fixed point — in particular, whether the mutation floor `μ > 0` alone forces unique
convergence, or whether the contraction band is a genuine (necessary) restriction.**

### Why this is non-trivial

1. **Existence is free but uniqueness is not.** `FlooredSimplex` is compact and convex
   and `mutT` is continuous, so a fixed point exists for *every* `μ ∈ [0,1]` (Brouwer;
   in the 2‑state case, the intermediate value theorem). The content is entirely in
   whether it is **unique** and **globally attracting** — properties Brouwer does not
   give.

2. **The band is not obviously removable.** The Banach route needs `(1−μ)·L_R < 1`. As
   `μ → 0` the factor `(1−μ) → 1`, and a genuinely selective `R` is expansive
   (`L_R > 1`): selection amplifies differences. So the sufficient condition degrades
   precisely where mutation is weak. Whether convergence nonetheless survives there is
   a real dynamical question, not a gap in the proof method.

3. **Frequency dependence permits multistability and cycles.** For frequency‑dependent
   selection (fitness depending on `w`), the replicator can have several coexisting
   attractors (coordination/bistable payoffs) or none in the interior (cyclic payoffs
   → periodic orbits). A blanket "unique fixed point for all `μ > 0`" is therefore in
   tension with standard evolutionary‑dynamics phenomenology — but turning that
   phenomenology into a *machine‑checked* statement, over `FlooredSimplex` with the
   exact `SelectionMap`/`mutT` definitions, requires an explicit, verifiable witness.

The obligation is subtle precisely because the "obvious" strong reading
(convergence everywhere in the plurality regime) is *false*, and the honest task is to
partition the parameter space into where it is **true**, **conditional**, and
**false**, each by a different technique, with the boundaries as sharp as the
mathematics allows.

## 1. Ambient theory (fixed for all candidates)

- **Foundations.** ZFC as encoded by Lean 4 / Mathlib. No AFA/non‑well‑founded set
  theory is used: this is real analysis on a finite‑dimensional simplex.
- **No coalgebraic apparatus.** There is *no* functor `F`, monad `T`, or distributive
  law `λ` in play. The object is a metric self‑map, not a (co)algebra; the "functor"
  language of the carrier construction is upstream and irrelevant here. (This is worth
  stating because it forecloses framings that would try to cash the obligation out as a
  distributive‑law existence/non‑existence claim — that is a category error for a
  dynamical‑systems obligation.)
- **Metric.** `FlooredSimplex S μ unif` with the subtype sup metric inherited from
  `S → ℝ` (`Pi`/`ℓ∞`). `dist`, `CompleteSpace`, and the Banach machinery come from WS5.
- **Imports available.** `FlooredSimplex`, `SelectionMap`, `mutationStep`, `mutT`,
  `SelectionLipschitz`, `mutation_lipschitz`, `ws7_attention_fixed_point`
  (WS7); `ws5_attention_converges` (WS5 Banach step); `ws8_replicator_converges`,
  `ws8_exp_replicator_converges`, `expLipConst`, `exp_band_iff` (WS8 bands).

Throughout, `attnStep` denotes a fully‑applied `mutT` at a concrete `(S, μ, unif, R)`.

## 2. Candidate framings

Seven ways to cash out "characterize where attention converges." Each states the Lean
target, the strategy, the success condition, and — explicitly — **what would count as
this framing failing**.

---

### C1 — Universal unique convergence (the maximal claim)

**Statement.** In the whole plurality regime, every admissible selection converges to a
unique fixed point.

```lean
theorem C1 : ∀ {S : Type u} [Fintype S] [Nonempty S] (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : S → ℝ) (hn : ∀ r, 0 ≤ unif r) (hs : ∑ r, unif r = 1)
    (sel : SelectionMap S unif),
    ∃! p : FlooredSimplex S μ unif, mutT μ hμ0.le hμ1 unif hn hs sel p = p
```

- **Ambient.** As §1; quantified over all `S`, `unif`, `sel`.
- **Strategy.** Would require a *uniform* contraction or Lyapunov argument valid at
  every `μ > 0` and every `sel`. No such argument exists.
- **Success condition.** A proof.
- **Failure (expected).** A single counterexample instance. C1 is included as the
  target to be **refuted**; its negation is C2.

---

### C2 — Necessity of the band via a multistability witness  *(the sharp, decidable core)*

**Statement.** There is a concrete plurality‑regime instance (`μ > 0`) with **at least
two** fixed points; hence no unique attractor, hence the band/structural hypotheses of
WS8 are necessary, not merely sufficient.

```lean
-- coordination replicator R(w)_r = w_r² / Σ_s w_s²  (payoff matrix = identity)
noncomputable def coordSel (unif : S → ℝ) : SelectionMap S unif

-- witness at S = Bool, uniform reference, μ = 3/8
def unifHalf : Bool → ℝ
noncomputable def attnStep : FlooredSimplex Bool (3/8) unifHalf → FlooredSimplex Bool (3/8) unifHalf

theorem ws9_multistable :
    ∃ p q : FlooredSimplex Bool (3/8) unifHalf, p ≠ q ∧ attnStep p = p ∧ attnStep q = q

theorem ws9_no_unique_attention :
    ¬ ∃! p : FlooredSimplex Bool (3/8) unifHalf, attnStep p = p
```

- **Ambient.** As §1. Selection = the coordination‑game replicator
  `R(w)_r = w_r²/∑_s w_s²` (equivalently `w_r·(Aw)_r/(w·Aw)` with `A = I`): a genuine
  `SelectionMap` (nonneg‑ and mass‑preserving), the canonical *bistable* selection.
- **Strategy.** Purely computational / *decidable on paper*: exhibit exact **rational**
  fixed points and verify `mutT p = p` by arithmetic. At `μ = 3/8`, `unif = (½,½)`, the
  fixed‑point equation `(1−μ)·w_r²/(w_0²+w_1²) + μ·½ = w_r` has three exact solutions
  `w_0 ∈ {¼, ½, ¾}`, i.e. the points `(¾,¼)`, `(½,½)`, `(¼,¾)`. Membership in
  `FlooredSimplex` (`w_r ≥ μ·½ = 3/16`) holds for all three. Uniqueness fails from any
  two of them.
- **Success condition.** `norm_num`‑checkable verification of the fixed points +
  distinctness; `¬∃!` follows.
- **Failure of the obligation.** If *no* such witness existed — i.e. if the fixed‑point
  equation had a unique solution for every admissible `(sel, μ>0)` — then C1 would hold
  and this framing would be vacuous. We prove the witness exists, so the failure mode
  here is "the strong claim C1 is false," which is the intended finding.

---

### C3 — Contraction genuinely absent below the band

**Statement.** At the same witness, `mutT` is **not** a Banach contraction for any
constant `< 1` — so the WS8 hypothesis is not an artifact of a loose estimate.

```lean
theorem ws9_no_contraction :
    ¬ ∃ K : ℝ, K < 1 ∧ ∀ p q : FlooredSimplex Bool (3/8) unifHalf,
        dist (attnStep p) (attnStep q) ≤ K * dist p q
```

- **Ambient.** As §1; sup metric on `FlooredSimplex Bool (3/8) unifHalf`.
- **Strategy.** Two distinct fixed points `p ≠ q` give `dist(Tp,Tq)=dist(p,q)>0`; a
  contraction constant `K<1` forces `dist(p,q) ≤ K·dist(p,q)`, contradiction.
- **Success condition.** Direct from C2's two fixed points.
- **Failure.** Would fail only if the witness had `< 2` fixed points (refuting C2).

---

### C4 — Non‑settling via a genuine periodic orbit

**Statement.** There is an instance and a state on a true 2‑cycle: `attnStep²(w) = w`
but `attnStep(w) ≠ w` — attention oscillates forever, never settling.

```lean
theorem C4 : ∃ (…instance…) (w : FlooredSimplex …),
    attnStep (attnStep w) = w ∧ attnStep w ≠ w
```

- **Ambient.** As §1; requires *negative* frequency dependence (anti‑coordination /
  cyclic payoff), realistically on `|S| ≥ 3` (rock–paper–scissors), where discrete
  replicator‑mutator dynamics admit invariant loops.
- **Strategy.** Construct a cyclic payoff and a small `μ`; exhibit an exact period‑2
  point. On `|S| = 2` this is impossible (the 2‑state anti‑coordination replicator
  collapses to the center); on `|S| ≥ 3` an *exact rational* 2‑cycle is delicate.
- **Success condition.** An explicit period‑2 witness.
- **Failure.** No rational cycle is exhibitable; or the constructed map converges.
- **Note.** Strictly stronger than C2 (non‑*convergence*, not just non‑*uniqueness*),
  but far harder to render as an exact machine‑checked witness.

---

### C5 — Existence everywhere (the true‑everywhere floor)

**Statement.** For the 2‑state system, a fixed point exists for **every** `μ ∈ (0,1]`
and every continuous selection — independent of any band.

```lean
theorem C5 : ∀ (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (sel : SelectionMap Bool unifHalf),
    (Continuous sel.R) → ∃ p : FlooredSimplex Bool μ unifHalf,
      mutT μ hμ0.le hμ1 unifHalf (by …) (by …) sel p = p
```

- **Ambient.** As §1. `FlooredSimplex Bool μ unifHalf` is order‑isomorphic to a real
  interval `[μ/2, 1−μ/2]`; `mutT` induces a continuous interval self‑map.
- **Strategy.** Intermediate value theorem on `g(x) = (mutT applied)_0 − x`
  (`intermediate_value_Icc`), giving a zero = fixed point. No contraction needed.
- **Success condition.** IVT closes it.
- **Failure.** Would require the induced map to leave the interval (it cannot: `mutT`
  is a self‑map by WS7's B0 invariance).
- **Role.** Pairs with C2 to bracket the truth: *existence always, uniqueness not
  always.*

---

### C6 — Sharpness of the WS8 band (bifurcation at `μ⋆`)

**Statement.** For a fixed frequency‑dependent selection there is a threshold `μ⋆` with
unique convergence above and multistability below — the band boundary is a genuine
bifurcation.

```lean
theorem C6 : ∃ μ_star ∈ Set.Ioo (0:ℝ) 1,
    (∀ μ, μ_star < μ → μ ≤ 1 → ∃! p : FlooredSimplex Bool μ unifHalf, attnStep' μ p = p) ∧
    (∀ μ, 0 < μ → μ < μ_star → ¬ ∃! p : FlooredSimplex Bool μ unifHalf, attnStep' μ p = p)
```

- **Ambient.** As §1, one selection, `μ` varying.
- **Strategy.** Above: WS8 contraction band. Below: a *parametrized* family of
  multistability witnesses (C2 for a range of `μ`), needing the fixed‑point count as a
  function of `μ` — a continuity/monotonicity argument on the cubic fixed‑point
  relation.
- **Success condition.** Both halves proved with a *matching* `μ⋆`.
- **Failure.** The above‑ and below‑thresholds fail to meet (a gap `μ‑interval` where
  neither is proved), i.e. the exact boundary is not pinned.
- **Note.** Strengthens C2 from a single point to an interval + a sharp boundary; the
  *exact* boundary is generically a Hopf/saddle‑node value with no closed form.

---

### C7 — Conditional convergence under a Lyapunov/potential structure

**Statement.** When the fitness derives from a potential (gradient/potential‑game
structure), convergence holds on *all* `μ > 0`, with no band.

```lean
theorem C7 : ∀ (…potential hypothesis on sel…) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1),
    ∃! p : FlooredSimplex S μ unif, mutT μ hμ0.le hμ1 unif … sel p = p
```

- **Ambient.** As §1 plus a structural hypothesis (fitness `= ∇Φ`, or a monotone /
  Baum–Eagon growth‑transformation structure).
- **Strategy.** A strict Lyapunov function (relative entropy / free energy) decreasing
  along `mutT`, plus a LaSalle‑type "bounded strictly‑decreasing ⇒ converges" step. For
  the *frequency‑independent* linear replicator this plausibly upgrades WS8's band to
  all `μ ∈ (0,1]`.
- **Success condition.** Lyapunov strict‑decrease + convergence, sorry‑free.
- **Failure.** No Lyapunov certificate for `mutT`; or convergence‑to‑set does not
  sharpen to a unique point.
- **Note.** Trades the `μ`‑band for a *structural* hypothesis on the fitness — the
  standard no‑free‑lunch: you do not remove the condition, you move it.

## 3. Trade‑offs between the framings

- **Decidability on paper.** C2 and C3 are *finitely checkable*: exact rational data,
  verification by arithmetic. C5 needs one analytic theorem (IVT) but no witness search.
  C4/C6/C7 require genuinely infinitary arguments (cycle existence, bifurcation
  continuity, Lyapunov/LaSalle) and, for C6/C7, Mathlib machinery that is not present
  (discrete LaSalle, Baum–Eagon).
- **Strength vs. attainability.** C4 (non‑settling) ≻ C2 (non‑uniqueness) in dynamical
  strength but is far harder to witness exactly. C7 (conditional convergence) and C6
  (sharp boundary) are the most informative but the least attainable sorry‑free now.
- **What actually pins the obligation.** The obligation is "characterize where
  convergence holds." The *minimal decisive* content is: (i) it is **not universal**
  (C2/C3 — the band is necessary), and (ii) existence is **always** available (C5 — the
  Brouwer floor). Together these bracket the region and convert WS8's "sufficient band"
  into "sufficient‑and‑necessary‑in‑the‑worst‑case." C4/C6/C7 refine the interior of the
  bracket and are the natural follow‑ons.
- **Risk of over‑claiming.** The *exact* convergence boundary for general
  frequency‑dependent fitness is a bifurcation surface with **no closed form** — a
  genuinely open mathematical object, not a formalization gap. Any framing promising a
  single "converges iff …" law (a naive reading of C6/C7 without hypotheses) would fail
  by over‑reach; the honest target is a stratification with an explicit
  "boundary‑is‑open" stamp.

## 4. Recommended obligation for the formal pass

**C2 + C3 (necessity), with C5 as the existence floor**, are the framings that are
simultaneously *decisive*, *decidable on paper*, and *sorry‑free‑attainable* against the
exact upstream definitions. C1 is their target (refuted). C4, C6, C7 are recorded as the
interior‑refinement program, each gated on infrastructure (exact cycle witnesses;
bifurcation continuity; discrete‑LaSalle / Baum–Eagon Lyapunov theory) that is a
separate, larger undertaking.

**Success for WS9 = a machine‑checked proof that unique attention convergence is *not*
universal in the plurality regime (a concrete multistable replicator‑mutator witness,
non‑contracting), establishing the WS8 band as necessary; with existence available
everywhere.** Failure = the witness cannot be exhibited sorry‑free, or collapses (the
constructed selection turns out to have a unique fixed point after all).
