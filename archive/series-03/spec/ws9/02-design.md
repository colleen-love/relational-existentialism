# WS9 · 02 — Design

*Triage the blind candidates on paper, collapse to a decision, and design the selected
proof.*

## 1. Triage (decidable on paper, per candidate)

Each candidate is scored on axes that can be settled **without** running Lean: whether
its truth value is decidable by hand, whether the required Lean infrastructure exists in
the current build, the witness complexity, and the sorry-free attainability.

| # | Framing | Truth (on paper) | Decidable by hand? | Needs new Mathlib infra? | Witness form | Sorry-free? |
|---|---|---|---|---|---|---|
| **C1** | universal unique convergence | **false** | yes (refuted by C2) | no | — | n/a (target) |
| **C2** | multistability witness ⇒ `¬∃!` | **true** | **yes** — 3 exact rational fixed points | no | 3 rationals, arithmetic | **yes ✓** |
| **C3** | not a contraction | **true** | **yes** — from C2's two fixed points | no | reuse C2 | **yes ✓** |
| **C4** | genuine 2-cycle (non-settling) | **true** | **yes** — *contrarian* selection, `\|S\|=2` | no | `P ↔ Q`, exact rational | **yes ✓** |
| **C5** | existence everywhere | **true** | **yes** — the center is fixed ∀μ | no | `(½,½)`, arithmetic | **yes ✓** |
| **C6** | interval + bifurcation `μ⋆` | **true** (interval side) | **yes** — IVT anchor + linearized multiplier | no (IVT + `HasDerivAt` present) | `μ`-interval + `deriv` | **yes ✓** |
| **C7** | conditional convergence (no band) | **true** (conditional) | **yes** — nonexpansive ⇒ `(1−μ)L_R<1` | no (reuses WS7 Banach) | structural hypothesis | **yes ✓** |

**Reading of the triage — revised (all seven realized).** The first-pass assessment
under-rated C4–C7 by fixing on their *hardest* readings. Re-triage found a decidable,
infra-free realization for each by **changing the witness, not the bar**:

- **C4** does *not* need `|S|≥3`. The *contrarian* selection `R(w)_r = w_{¬r}²/∑w²`
  (anti-coordination, still a valid `SelectionMap`) has an **exact rational 2-cycle** on
  `Bool` at the same `μ = 3/8`: it swaps `P ↔ Q`. Non-settling, fully checkable.
- **C5** does *not* need the general IVT+continuity apparatus for the headline: the
  coordination replicator's **center `(½,½)` is a fixed point for every `μ`**, so
  existence everywhere is one arithmetic identity. (The IVT machinery is still built —
  it is what C6 needs.)
- **C6**'s *interval* side is decidable: for `μ ∈ (0,3/8]` a fixed anchor `x = 3/4`
  certifies `G(3/4) ≥ 0 ≥ G(1−μ/2)`, so IVT gives an off-center fixed point on the whole
  interval. The **bifurcation** is made explicit not via the (open) exact boundary but
  via the **linearized multiplier** `2(1−μ)` of the persistent center fixed point
  (`HasDerivAt`), whose crossing of `1` at `μ⋆ = 1/2` *is* the pitchfork.
- **C7** does *not* need Baum–Eagon for its provable core: a **nonexpansive** selection
  (`L_R ≤ 1` — the structural condition) gives `(1−μ)·L_R ≤ 1−μ < 1`, so WS7's Banach
  spine fires for *all* `μ ∈ (0,1]`. Trades the band for a structural hypothesis, no band.

What remains genuinely infra-gated (and stays out): the **exact** `μ⋆`-boundary as an
`iff` for general fitness (a bifurcation surface, no closed form), and
`potential ⇒ convergence below the band` via a full discrete Lyapunov/Baum–Eagon theory
(absent from Mathlib). These are the honest open residue; everything else is folded in.

**Decision (revised).** Formalize **all of C2–C7** plus the explicit bifurcation. C2/C3
remain the decisive headline (they refute C1 and make the WS8 band *necessary*); C4–C7
stratify the rest of the region — non-settling (C4), existence floor (C5), interval +
pitchfork (C6), conditional convergence (C7) — each with an exact, hand-decidable,
infra-free witness. The framing choice is the *output* of the re-triage: the bar never
moved; the witnesses got smarter.

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

Namespace `Series03.WS9`, importing `ws7` (which transitively provides `FlooredSimplex`,
`SelectionMap`, `mutationStep`, `mutT`, the metric/complete instances). `open
Series03.WS7`.

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

### 3.1a Machinery for the folded-in pieces (C4–C7 + bifurcation)

8. **C4 (non-settling).** `antiR w r := w_{¬r}²/∑w²` (contrarian), `antiSel`,
   `antiStep := mutT (3/8) … antiSel`. `antiStep_PtoQ : antiStep ptP = ptQ` and
   `antiStep_QtoP` (same arithmetic as the fixed-point lemmas, with the `Bool.not_*`
   reindex). `ws9_two_cycle : antiStep (antiStep ptP) = ptP ∧ antiStep ptP ≠ ptP`.
9. **C5 (existence everywhere).** `coordFix`: a root `coordIndF μ x = x` in
   `[μ/2, 1−μ/2]` reconstructs a `FlooredSimplex` fixed point `(x,1−x)` (false-coord by
   the root, true-coord by mass-conservation through `mutationStep_maps_into`).
   `ws9_center_fixed_all` = `coordFix` at `x = 1/2` (`coordIndF_center`), any `μ`.
10. **C6 (interval + bifurcation).** `coordIndF μ x := (1−μ)·x²/(x²+(1−x)²) + μ/2`, the
    induced 1-D map; `coordDen_pos`, `coordIndF_upper` (`≤ 1−μ/2`), `coordIndF_continuous`.
    `ws9_multistable_interval` (∀ `μ∈(0,3/8]`): center + an IVT root in `[3/4, 1−μ/2]`
    (`intermediate_value_Icc'` with `G(3/4) ≥ 0 ≥ G(1−μ/2)`), distinct by
    false-coord `≥ 3/4 ≠ ½`. `coordMultiplier μ := 2(1−μ)`,
    `coordIndF_hasDerivAt_center : HasDerivAt (coordIndF μ) (coordMultiplier μ) (½)` (via
    `HasDerivAt.pow/.div`), `ws9_bifurcation` (`multiplier < 1 ↔ ½ < μ` and
    `1 < multiplier ↔ μ < ½`) — the pitchfork at `μ⋆ = ½`.
11. **C7 (conditional).** `ws9_nonexpansive_converges`: `SelectionLipschitz` with
    `L_R μ ≤ 1` ⇒ `(1−μ)·L_R ≤ 1−μ < 1` ⇒ `ws7_attention_fixed_point`, all `μ∈(0,1]`.

### 3.2 Dependencies on imported upstream theorems

- **WS7 (used directly):** `FlooredSimplex` (subtype + `MetricSpace`), `SelectionMap`,
  `mutationStep`, `mutT`, `mutationStep_maps_into` (invariance, for C5's true-coord),
  `SelectionLipschitz` + `ws7_attention_fixed_point` (for C7). The necessity core (C2/C3)
  invokes no WS7 *theorem* — only definitions; the conditional (C7) reuses WS7's Banach
  spine as its whole content.
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

## 4. Scope statement (as built)

WS9 delivers a **stratified characterization** of the replicator-mutator convergence
region, all sorry-free and axiom-clean:

- **False (necessity):** `ws9_no_unique_attention` / `ws9_no_contraction` — unique
  convergence is not universal in the plurality regime (three exact fixed points at
  `μ = 3/8`); and `ws9_two_cycle` — a contrarian selection *never settles* (an exact
  period-2 orbit `P ↔ Q`).
- **True (floors):** `ws9_center_fixed_all` — a fixed point exists for every `μ ∈ (0,1]`;
  `ws9_multistable_interval` — multistability holds on the whole interval `μ ∈ (0, 3/8]`.
- **Bifurcation:** `coordIndF_hasDerivAt_center` + `ws9_bifurcation` — the persistent
  center's linearized multiplier `2(1−μ)` crosses `1` at the pitchfork `μ⋆ = 1/2`
  (attracting above, repelling below).
- **Conditional:** `ws9_nonexpansive_converges` — a structural hypothesis (nonexpansive
  selection) buys convergence back on all of `μ ∈ (0,1]`, no band.

**Honest open residue** (genuinely infra-gated, *not* laundered): the **exact** `μ⋆`
boundary as an `iff` for general frequency-dependent fitness (a bifurcation surface with
no closed form), and `potential ⇒ convergence below the band` via a full discrete
Lyapunov/Baum–Eagon theory (absent from Mathlib). The bundle is therefore named by its
parts (`ws9_*`), **not** `ws9_convergence_characterized`: the stratification is complete
in the achievable sense (sufficient conditions + counterexamples that meet at the sharp
threshold), but the single exact-`iff` law is off the table for principled reasons.
