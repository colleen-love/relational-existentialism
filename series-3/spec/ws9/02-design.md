# WS9 · 02 — Design

*Triage the blind candidates on paper, collapse to a decision, and design the selected
proof.*

## 1. Triage (decidable on paper, per candidate)

Each candidate is scored on axes that can be settled **without** running Lean: whether
its truth value is decidable by hand, whether the required Lean infrastructure exists in
the current build, the witness complexity, and the sorry-free attainability.

| # | Framing | Truth (on paper) | Decidable by hand? | Needs new Mathlib infra? | Witness form | Sorry-free now? |
|---|---|---|---|---|---|---|
| **C1** | universal unique convergence | **false** | yes (refuted by C2) | no | — | n/a (target) |
| **C2** | multistability witness ⇒ `¬∃!` | **true** | **yes** — 3 exact rational fixed points | no | 3 rationals, arithmetic | **yes** |
| **C3** | not a contraction | **true** | **yes** — from C2's two fixed points | no | reuse C2 | **yes** |
| **C4** | genuine 2-cycle (non-settling) | true (∃ instance) | no — needs `|S|≥3`, exact cycle | no, but hard | irrational/delicate | no (not exact) |
| **C5** | existence everywhere (IVT) | **true** | yes — 1-D IVT | no (IVT present) | analytic, no witness | plausible |
| **C6** | sharp band / bifurcation | true (partial) | partly — boundary open | continuity-of-root count | `μ`-family | no |
| **C7** | conditional Lyapunov convergence | true (conditional) | no | **yes** — discrete LaSalle / Baum–Eagon | — | no |

**Reading of the triage.** Exactly two candidates are *both* decidable-by-hand *and*
sorry-free-attainable with zero new infrastructure: **C2** and **C3** (and C3 is a
two-line corollary of C2). **C5** is attainable but needs one analytic theorem (IVT) and
adds the "existence floor" — worthwhile but strictly secondary; it can be deferred
without weakening the headline. **C4/C6/C7** each hit a wall that is *decidable on
paper*: C4 needs an exact cycle on `|S|≥3` (no clean rational witness); C6 needs the
root-count of the fixed-point cubic as a function of `μ` (a genuine bifurcation
argument, boundary with no closed form); C7 needs a discrete LaSalle/Lyapunov theory
(Baum–Eagon) absent from Mathlib. None is a *formalization* obstacle only — each is a
real mathematical/infrastructure cost.

**Decision.** Formalize **C2 (headline) + C3 (corollary)**. This is the minimal decisive
content: it *refutes C1* and establishes the WS8 band as **necessary**, entirely by
exact arithmetic. C5/C4/C6/C7 are logged in `01`'s §4 as the interior-refinement
program. The framing choice (C2) is the *output* of this triage, not a substitute for
it: C2 wins because it is the unique node that is decisive, hand-decidable, and
infra-free.

## 2. The witness (worked on paper)

Fix `S = Bool`, `unif = (½, ½)`, and the **coordination-game replicator**

```
R(w)_r = w_r² / (w_0² + w_1²)      (= w_r·(Aw)_r / (w·Aw) with A = I)
```

a legitimate `SelectionMap` (nonneg-preserving; `∑_r R(w)_r = 1` when `∑ w = 1`, since
`∑ w = 1` forces `w_0²+w_1² > 0`). The mutation step at `μ = 3/8`:

```
T(w)_r = (1 − 3/8)·R(w)_r + (3/8)·½ = (5/8)·w_r²/(w_0²+w_1²) + 3/16.
```

Parametrize the sum-one line by `x = w_0 ∈ [0,1]`, `D(x) = x² + (1−x)²`. Fixed points
solve `(5/8)·x²/D(x) + 3/16 = x`. Three exact rational solutions:

| `x = w_0` | `D` | `x²/D` | `T(w)_0 = (5/8)(x²/D)+3/16` | fixed? |
|---|---|---|---|---|
| `¾` | `5/8` | `9/10` | `9/16 + 3/16 = ¾` | ✓ |
| `½` | `½` | `½` | `5/16 + 3/16 = ½` | ✓ |
| `¼` | `5/8` | `1/10` | `1/16 + 3/16 = ¼` | ✓ |

So `mutT` fixes the three distinct points

```
P = (¾, ¼),   M = (½, ½),   Q = (¼, ¾).
```

**Floor check.** `μ·unif_r = (3/8)(½) = 3/16`; every coordinate of `P, M, Q` is
`≥ 3/16` (smallest is `¼ = 4/16`), and each sums to `1`, so all three lie in
`FlooredSimplex Bool (3/8) unifHalf`. `P, M, Q` are pairwise distinct (differ at
coordinate `0`). ∎ (on paper)

`P` and `Q` are the two stable "committed-attention" states (a self-reinforcing
majority), `M` the unstable balanced saddle — the textbook bistable picture of a
coordination replicator, here exact and rational because the payoff matrix is `I`
(quadratic fitness) rather than exponential.

## 3. Proof architecture (Lean)

Namespace `Series3.WS9`, importing `ws7` (which transitively provides `FlooredSimplex`,
`SelectionMap`, `mutationStep`, `mutT`, the metric/complete instances). `open
Series3.WS7`.

```
generic layer
  coordR      : (S→ℝ) → S → ℝ                     -- w ↦ (w_r² / Σ w_s²), if-guarded off Σ=0
  coordR_of_pos : 0 < Σ (w s)² → coordR w r = (w r)²/Σ(w s)²
  coordSel    : SelectionMap S unif               -- nonneg + sum_one wrappers around coordR

witness layer (S := Bool)
  unifHalf, unifHalf_nonneg, unifHalf_sum
  vP vM vQ    : Bool → ℝ                           -- underlying vectors (cond-based)
  ptP ptM ptQ : FlooredSimplex Bool (3/8) unifHalf -- with floor+sum membership proofs
  attnStep    : FlooredSimplex … → FlooredSimplex … := mutT (3/8) … (coordSel unifHalf)

fixed points (arithmetic)
  attnStep_fixP : attnStep ptP = ptP
  attnStep_fixM : attnStep ptM = ptM
  attnStep_fixQ : attnStep ptQ = ptQ
  ptP_ne_ptM, ptP_ne_ptQ, ptM_ne_ptQ

headline
  ws9_multistable        : ∃ p q, p ≠ q ∧ attnStep p = p ∧ attnStep q = q
  ws9_multistable_three  : (three fixed) ∧ (pairwise ≠)
  ws9_no_unique_attention: ¬ ∃! p, attnStep p = p
  ws9_no_contraction     : ¬ ∃ K < 1, ∀ p q, dist (attnStep p)(attnStep q) ≤ K·dist p q
```

### 3.1 Definitions and lemmas needed

1. **`coordR` total & guarded.** `coordR w r := if 0 < ∑ s, (w s)^2 then (w r)^2/(∑ s,(w s)^2) else w r`.
   Mirrors the WS8 `linR`/`expR` totalization pattern so `nonneg`/`sum_one` hold
   unconditionally.
2. **`coordSel : SelectionMap S unif`.**
   - `nonneg`: `split_ifs`; `then` branch `div_nonneg (sq_nonneg _) (le_of_lt h)`.
   - `sum_one`: from `∑ w = 1` derive `∃ i, w i ≠ 0` (else the sum is `0 ≠ 1`), hence
     `0 < ∑ (w s)²` via `Finset.sum_pos'` + `pow_two_pos_of_ne_zero`; then
     `simp_rw [coordR_of_pos, ← Finset.sum_div]; exact div_self (ne_of_gt h)`.
3. **Witness membership** via `Fintype.sum_bool` + `norm_num`.
4. **Fixed points.** For each `pt`: `apply Subtype.ext; funext b`, reduce
   `(attnStep pt).1 b` (defeq) to `(1 − 3/8)·coordR v b + (3/8)·unifHalf b`, rewrite
   `coordR_of_pos` with the precomputed `∑ (v s)² = 5/8` (resp. `1/2`), then
   `cases b <;> simp <;> norm_num`.
5. **Distinctness.** Compare underlying vectors at `false` (`congrFun` on
   `Subtype.val`), `norm_num`.
6. **`¬∃!`.** `rintro ⟨p, _, huniq⟩`; `huniq ptP _`, `huniq ptM _` collapse `P = p = M`,
   contradicting `ptP_ne_ptM`.
7. **`¬ contraction`.** `dist_pos.mpr ptP_ne_ptM` and `mul_lt_of_lt_one_left`; rewrite
   both `attnStep`-images to `ptP`/`ptM` (fixed points) and `linarith`.

### 3.2 Dependencies on imported upstream theorems

- **WS7 (used directly):** `FlooredSimplex` (subtype + `MetricSpace`), `SelectionMap`,
  `mutationStep`, `mutT` (the invariance packaging `mutationStep_maps_into` is consumed
  implicitly through `mutT`). No WS7 *theorem* is invoked — only the definitions — so
  WS9 cannot inherit any WS7 hazard.
- **WS8 (referenced, not imported):** the bands `ws8_replicator_converges` /
  `ws8_exp_replicator_converges` are the *sufficient* side; WS9 is their converse
  boundary. `ws9_no_contraction` is exactly the statement that WS8's Banach hypothesis
  fails here, so the two are logically complementary (sufficient band ↔ necessary band)
  with no shared proof surface.
- **Mathlib:** `Fintype.sum_bool`, `Finset.sum_pos'`, `Finset.sum_eq_zero`,
  `pow_two_pos_of_ne_zero`/`positivity`, `div_self`, `div_nonneg`, `sq_nonneg`,
  `Subtype.ext`, `dist_pos`, `mul_lt_of_lt_one_left`, `norm_num`.

### 3.3 Success condition and failure modes (formal)

- **Success.** `lake build` compiles `ws9.lean` sorry-free; `#print axioms` on
  `ws9_no_unique_attention`, `ws9_multistable`, `ws9_no_contraction` reports only
  `[propext, Classical.choice, Quot.sound]`.
- **Failure that would matter.** If the three points were *not* exactly fixed (an
  arithmetic slip), `norm_num` fails at `attnStep_fix*` — caught at build time, no
  `sorry` masks it. If `coordSel` were not a valid `SelectionMap`, the structure fields
  fail to typecheck. There is no route by which a false WS9 claim compiles.

## 4. Scope statement

WS9 delivers the **necessity** half of the convergence characterization: unique
attention convergence is not universal in the plurality regime (`C2`), and the failure
is a true non-contraction (`C3`), witnessed by an exact rational bistable
replicator-mutator instance. It deliberately does **not** claim the interior refinements
(C4 cycles, C6 sharp bifurcation `μ⋆`, C7 conditional Lyapunov convergence); those are
named, triaged, and left as typed future obligations, not laundered into the headline.
The bundle name is `ws9_no_unique_attention` (+ `ws9_no_contraction`), **not**
`ws9_convergence_characterized`.
