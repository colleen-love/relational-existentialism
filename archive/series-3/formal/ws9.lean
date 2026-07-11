/-
`series-3/formal/ws9.lean` — WS9: the convergence boundary (necessity).

WS8 proved *sufficient* conditions for the replicator-mutator attention step
`mutT μ unif sel` to converge to a unique fixed point: a Banach contraction on an
explicit band `μ > μ⋆` (linear replicator `ws8_replicator_converges`, exponential
`ws8_exp_replicator_converges`). WS9 supplies the **converse boundary**: unique
convergence is **not universal** in the plurality regime `μ > 0`.

The witness is the **coordination-game replicator** `R(w)_r = w_r² / ∑_s w_s²`
(payoff matrix `A = I`; the canonical *bistable* selection) on `S = Bool` with the
uniform reference and `μ = 3/8`. Its mutation step has **three** exact rational fixed
points — `(¾,¼)`, `(½,½)`, `(¼,¾)` — so it is neither uniquely-convergent nor a
contraction. This makes the WS8 band **necessary**, not merely sufficient.

Everything is decided by exact rational arithmetic against the upstream WS7
definitions; nothing here is a bare hypothesis.

This file delivers a **stratified characterization** of the convergence region:
* FALSE (necessity): `ws9_no_unique_attention`, `ws9_no_contraction` (three fixed points
  at `μ = 3/8`), and `ws9_two_cycle` (a *contrarian* selection with an exact period-2
  orbit `P ↔ Q` — attention never settles).
* TRUE (floors): `ws9_center_fixed_all` (a fixed point exists for every `μ ∈ (0,1]`) and
  `ws9_multistable_interval` (multistability on the whole interval `μ ∈ (0, 3/8]`).
* BIFURCATION: `coordIndF_hasDerivAt_center` + `ws9_bifurcation` — the persistent
  center's linearized multiplier `2(1−μ)` crosses `1` at the pitchfork `μ⋆ = 1/2`.
* CONDITIONAL: `ws9_nonexpansive_converges` — a nonexpansive selection converges on all
  `μ ∈ (0,1]` (structural hypothesis, no band).

Honest open residue (not laundered): the exact `μ⋆`-boundary as an `iff` for general
fitness (a bifurcation surface, no closed form), and `potential ⇒ convergence below the
band` via a discrete Lyapunov/Baum–Eagon theory (absent from Mathlib). Hence the bundle
is named by its parts, not `ws9_convergence_characterized`.
-/
import ws7

namespace Series3.WS9

open Series3.WS7
open scoped NNReal

variable {S : Type u} [Fintype S]

/-! ### The coordination-game replicator `R(w)_r = w_r² / ∑ w_s²` -/

/-- The coordination replicator, total on `S → ℝ` (identity off the positive-`∑w²`
region, so `nonneg`/`sum_one` hold unconditionally). On any point with `∑ w² > 0` it is
the genuine `w_r² / ∑_s w_s²` — the replicator of the identity-payoff coordination
game. -/
noncomputable def coordR (w : S → ℝ) (r : S) : ℝ :=
  if 0 < ∑ s, (w s) ^ 2 then (w r) ^ 2 / (∑ s, (w s) ^ 2) else w r

lemma coordR_of_pos {w : S → ℝ} {r : S} (h : 0 < ∑ s, (w s) ^ 2) :
    coordR w r = (w r) ^ 2 / (∑ s, (w s) ^ 2) := by
  simp only [coordR, if_pos h]

/-- The coordination replicator as a `SelectionMap` (nonnegativity- and mass-preserving;
`∑ w = 1` forces `∑ w² > 0`, so the genuine quotient is in force). -/
noncomputable def coordSel (unif : S → ℝ) : SelectionMap S unif where
  R := coordR
  nonneg := fun w hw r => by
    simp only [coordR]
    split_ifs with h
    · exact div_nonneg (sq_nonneg _) h.le
    · exact hw r
  sum_one := fun w hw => by
    have hne : ∃ i, w i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero (by rw [← hw, Finset.sum_eq_zero (fun i _ => hc i)])
    obtain ⟨i, hi⟩ := hne
    have hpos : 0 < ∑ s, (w s) ^ 2 := by
      refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      positivity
    have hR : ∀ r, coordR w r = (w r) ^ 2 / (∑ s, (w s) ^ 2) := fun r => coordR_of_pos hpos
    simp_rw [hR, ← Finset.sum_div]
    exact div_self hpos.ne'

/-! ### The `Bool` witness at `μ = 3/8` -/

/-- The uniform reference on `Bool`. -/
noncomputable def unifHalf : Bool → ℝ := fun _ => 1 / 2

lemma unifHalf_nonneg : ∀ r, 0 ≤ unifHalf r := fun _ => by norm_num [unifHalf]

lemma unifHalf_sum : ∑ r, unifHalf r = 1 := by rw [Fintype.sum_bool]; norm_num [unifHalf]

/-- Underlying vectors of the three fixed points: `P = (¾,¼)`, `M = (½,½)`, `Q = (¼,¾)`. -/
noncomputable def vP : Bool → ℝ := fun b => cond b (1 / 4) (3 / 4)
noncomputable def vM : Bool → ℝ := fun _ => 1 / 2
noncomputable def vQ : Bool → ℝ := fun b => cond b (3 / 4) (1 / 4)

private lemma floor_mem (v : Bool → ℝ) (h : ∀ b, (3 / 16 : ℝ) ≤ v b) :
    ∀ r, (3 / 8 : ℝ) * unifHalf r ≤ v r := fun r => by
  have := h r; simp only [unifHalf]; linarith

/-- `P = (¾,¼)` in the floored simplex. -/
noncomputable def ptP : FlooredSimplex Bool (3 / 8) unifHalf :=
  ⟨vP, floor_mem vP (fun b => by cases b <;> norm_num [vP]),
    by rw [Fintype.sum_bool]; norm_num [vP]⟩

/-- `M = (½,½)` in the floored simplex. -/
noncomputable def ptM : FlooredSimplex Bool (3 / 8) unifHalf :=
  ⟨vM, floor_mem vM (fun b => by cases b <;> norm_num [vM]),
    by rw [Fintype.sum_bool]; norm_num [vM]⟩

/-- `Q = (¼,¾)` in the floored simplex. -/
noncomputable def ptQ : FlooredSimplex Bool (3 / 8) unifHalf :=
  ⟨vQ, floor_mem vQ (fun b => by cases b <;> norm_num [vQ]),
    by rw [Fintype.sum_bool]; norm_num [vQ]⟩

/-- The concrete attention step: coordination replicator, uniform reference, `μ = 3/8`. -/
noncomputable def attnStep : FlooredSimplex Bool (3 / 8) unifHalf →
    FlooredSimplex Bool (3 / 8) unifHalf :=
  mutT (3 / 8) (by norm_num) (by norm_num) unifHalf unifHalf_nonneg unifHalf_sum
    (coordSel unifHalf)

/-! ### The three exact fixed points -/

/-- `T(P) = P`: `(5/8)·(9/10) + 3/16 = ¾`, `(5/8)·(1/10) + 3/16 = ¼`. -/
lemma attnStep_fixP : attnStep ptP = ptP := by
  have hD : (∑ s, (vP s) ^ 2) = 5 / 8 := by rw [Fintype.sum_bool]; norm_num [vP]
  have hDpos : (0 : ℝ) < ∑ s, (vP s) ^ 2 := by rw [hD]; norm_num
  apply Subtype.ext
  funext b
  show (1 - 3 / 8) * coordR vP b + 3 / 8 * unifHalf b = vP b
  rw [coordR_of_pos hDpos, hD]
  cases b <;> norm_num [vP, unifHalf]

/-- `T(M) = M`: `(5/8)·½ + 3/16 = ½`. -/
lemma attnStep_fixM : attnStep ptM = ptM := by
  have hD : (∑ s, (vM s) ^ 2) = 1 / 2 := by rw [Fintype.sum_bool]; norm_num [vM]
  have hDpos : (0 : ℝ) < ∑ s, (vM s) ^ 2 := by rw [hD]; norm_num
  apply Subtype.ext
  funext b
  show (1 - 3 / 8) * coordR vM b + 3 / 8 * unifHalf b = vM b
  rw [coordR_of_pos hDpos, hD]
  cases b <;> norm_num [vM, unifHalf]

/-- `T(Q) = Q`, by the state-swap symmetry with `P`. -/
lemma attnStep_fixQ : attnStep ptQ = ptQ := by
  have hD : (∑ s, (vQ s) ^ 2) = 5 / 8 := by rw [Fintype.sum_bool]; norm_num [vQ]
  have hDpos : (0 : ℝ) < ∑ s, (vQ s) ^ 2 := by rw [hD]; norm_num
  apply Subtype.ext
  funext b
  show (1 - 3 / 8) * coordR vQ b + 3 / 8 * unifHalf b = vQ b
  rw [coordR_of_pos hDpos, hD]
  cases b <;> norm_num [vQ, unifHalf]

/-! ### Distinctness -/

lemma ptP_ne_ptM : ptP ≠ ptM := by
  intro h
  have : vP false = vM false := congrFun (congrArg Subtype.val h) false
  norm_num [vP, vM] at this

lemma ptP_ne_ptQ : ptP ≠ ptQ := by
  intro h
  have : vP false = vQ false := congrFun (congrArg Subtype.val h) false
  norm_num [vP, vQ] at this

lemma ptM_ne_ptQ : ptM ≠ ptQ := by
  intro h
  have : vM false = vQ false := congrFun (congrArg Subtype.val h) false
  norm_num [vM, vQ] at this

/-! ### The necessity results -/

/-- **C2 — multistability (the witness).** The coordination replicator-mutator at
`μ = 3/8 > 0` has two distinct fixed points in the floored simplex — so attention does
not converge to a *unique* state in the plurality regime. -/
theorem ws9_multistable :
    ∃ p q : FlooredSimplex Bool (3 / 8) unifHalf, p ≠ q ∧ attnStep p = p ∧ attnStep q = q :=
  ⟨ptP, ptM, ptP_ne_ptM, attnStep_fixP, attnStep_fixM⟩

/-- **C2 (full bistable structure).** Three distinct fixed points: the two committed
states `P, Q` and the balanced saddle `M`. -/
theorem ws9_multistable_three :
    (attnStep ptP = ptP ∧ attnStep ptM = ptM ∧ attnStep ptQ = ptQ) ∧
      (ptP ≠ ptM ∧ ptP ≠ ptQ ∧ ptM ≠ ptQ) :=
  ⟨⟨attnStep_fixP, attnStep_fixM, attnStep_fixQ⟩, ptP_ne_ptM, ptP_ne_ptQ, ptM_ne_ptQ⟩

/-- **C1 refuted.** Unique attention convergence is **not** universal in the plurality
regime: at this concrete `μ > 0` there is no unique fixed point. -/
theorem ws9_no_unique_attention :
    ¬ ∃! p : FlooredSimplex Bool (3 / 8) unifHalf, attnStep p = p := by
  rintro ⟨p, _, huniq⟩
  exact ptP_ne_ptM ((huniq ptP attnStep_fixP).trans (huniq ptM attnStep_fixM).symm)

/-- **C3 — no contraction.** `attnStep` is not a Banach contraction for any constant
`< 1`: two distinct fixed points force `dist(Tp,Tq) = dist(p,q) > 0`. So WS8's
contraction hypothesis genuinely fails here — the band is necessary, not an artifact. -/
theorem ws9_no_contraction :
    ¬ ∃ K : ℝ, K < 1 ∧ ∀ p q : FlooredSimplex Bool (3 / 8) unifHalf,
        dist (attnStep p) (attnStep q) ≤ K * dist p q := by
  rintro ⟨K, hK, hc⟩
  have hd : 0 < dist ptP ptM := dist_pos.mpr ptP_ne_ptM
  have hle := hc ptP ptM
  rw [attnStep_fixP, attnStep_fixM] at hle
  linarith [hle, mul_lt_of_lt_one_left hd hK]

/-! ### Piece 3 (C4) — genuine non-settling: a contrarian selection with a 2-cycle

The coordination replicator settles (to one of several fixed points). A *contrarian*
selection — favour the state whose opposite is common, `R(w)_r = w_{¬r}² / ∑ w_s²` — has
**no** interior attractor at small `μ`: it produces a true **period-2 orbit**, attention
oscillating forever. This is strictly stronger than WS9's non-uniqueness: here attention
does not settle at all. The orbit is exact and rational — the same two points `P, Q`,
now swapped by the dynamics rather than fixed. -/

/-- The contrarian selection `R(w)_r = w_{¬r}² / ∑_s w_s²`, total on `Bool → ℝ`. -/
noncomputable def antiR (w : Bool → ℝ) (r : Bool) : ℝ :=
  if 0 < ∑ s, (w s) ^ 2 then (w (!r)) ^ 2 / (∑ s, (w s) ^ 2) else w r

lemma antiR_of_pos {w : Bool → ℝ} {r : Bool} (h : 0 < ∑ s, (w s) ^ 2) :
    antiR w r = (w (!r)) ^ 2 / (∑ s, (w s) ^ 2) := by simp only [antiR, if_pos h]

/-- The contrarian selection as a `SelectionMap` (nonneg-preserving; mass-preserving via
the `¬`-reindexing `∑_r w_{¬r}² = ∑_s w_s²`). -/
noncomputable def antiSel : SelectionMap Bool unifHalf where
  R := antiR
  nonneg := fun w hw r => by
    simp only [antiR]
    split_ifs with h
    · exact div_nonneg (sq_nonneg _) h.le
    · exact hw r
  sum_one := fun w hw => by
    have hne : ∃ i, w i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero (by rw [← hw, Finset.sum_eq_zero (fun i _ => hc i)])
    obtain ⟨i, hi⟩ := hne
    have hpos : 0 < ∑ s, (w s) ^ 2 := by
      refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      positivity
    have hR : ∀ r, antiR w r = (w (!r)) ^ 2 / (∑ s, (w s) ^ 2) := fun r => antiR_of_pos hpos
    have hreindex : (∑ r, (w (!r)) ^ 2) = ∑ s, (w s) ^ 2 := by
      rw [Fintype.sum_bool, Fintype.sum_bool]; simp only [Bool.not_true, Bool.not_false]; ring
    simp_rw [hR, ← Finset.sum_div]
    rw [hreindex]
    exact div_self hpos.ne'

/-- The contrarian attention step at `μ = 3/8`. -/
noncomputable def antiStep : FlooredSimplex Bool (3 / 8) unifHalf →
    FlooredSimplex Bool (3 / 8) unifHalf :=
  mutT (3 / 8) (by norm_num) (by norm_num) unifHalf unifHalf_nonneg unifHalf_sum antiSel

/-- `T(P) = Q`: the contrarian step swaps the committed states. -/
lemma antiStep_PtoQ : antiStep ptP = ptQ := by
  have hD : (∑ s, (vP s) ^ 2) = 5 / 8 := by rw [Fintype.sum_bool]; norm_num [vP]
  have hDpos : (0 : ℝ) < ∑ s, (vP s) ^ 2 := by rw [hD]; norm_num
  apply Subtype.ext
  funext b
  show (1 - 3 / 8) * antiR vP b + 3 / 8 * unifHalf b = vQ b
  rw [antiR_of_pos hDpos, hD]
  cases b <;>
    simp only [Bool.not_false, Bool.not_true, vP, vQ, unifHalf, cond_true, cond_false] <;> norm_num

/-- `T(Q) = P`. -/
lemma antiStep_QtoP : antiStep ptQ = ptP := by
  have hD : (∑ s, (vQ s) ^ 2) = 5 / 8 := by rw [Fintype.sum_bool]; norm_num [vQ]
  have hDpos : (0 : ℝ) < ∑ s, (vQ s) ^ 2 := by rw [hD]; norm_num
  apply Subtype.ext
  funext b
  show (1 - 3 / 8) * antiR vQ b + 3 / 8 * unifHalf b = vP b
  rw [antiR_of_pos hDpos, hD]
  cases b <;>
    simp only [Bool.not_false, Bool.not_true, vP, vQ, unifHalf, cond_true, cond_false] <;> norm_num

/-- **C4 — a genuine 2-cycle (non-settling).** The contrarian mutation step at `μ = 3/8`
has a period-2 orbit `P ↔ Q`: `T²(P) = P` yet `T(P) ≠ P`. So in the plurality regime
attention can fail to converge *at all* — not merely fail to be unique. -/
theorem ws9_two_cycle : antiStep (antiStep ptP) = ptP ∧ antiStep ptP ≠ ptP := by
  refine ⟨?_, ?_⟩
  · rw [antiStep_PtoQ, antiStep_QtoP]
  · rw [antiStep_PtoQ]; exact ptP_ne_ptQ.symm

/-! ### Piece 4 (C7) — conditional convergence under a nonexpansive selection

The converse to the necessity results: a *structural* hypothesis on the selection buys
convergence back on the whole plurality regime, with **no** band. If the selection is
nonexpansive (`L_R μ ≤ 1` — what a potential/contractive fitness supplies), then
`(1−μ)·L_R ≤ 1−μ < 1`, so Banach applies for every `μ ∈ (0,1]`. (The deeper
`potential ⇒ convergence` below the band, via a discrete Lyapunov/Baum–Eagon argument,
needs machinery absent from Mathlib and stays open; this is its provable core.) -/

/-- **C7 — conditional convergence (no band).** A nonexpansive selection converges to a
unique fixed point at every `μ ∈ (0,1]`. -/
theorem ws9_nonexpansive_converges (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hL : (sl.L_R μ : ℝ) ≤ 1)
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif,
      mutT μ hμ0.le hμ1 unif hunif_nonneg hunif_sum sel p = p := by
  refine ws7_attention_fixed_point μ hμ0 hμ1 unif hunif_nonneg hunif_sum sel sl ?_
  have h1 : (0 : ℝ) ≤ 1 - μ := by linarith
  have : (1 - μ) * (sl.L_R μ : ℝ) ≤ (1 - μ) * 1 := mul_le_mul_of_nonneg_left hL h1
  linarith

/-! ### Pieces 1 & 2 (C5, C6) — existence everywhere, an interval of multistability,
and the explicit pitchfork bifurcation at `μ⋆ = 1/2`

We now bracket the coordination replicator's convergence region. On `Bool`, a point of
the floored simplex is `wx x = (x, 1−x)`; the induced false-coordinate dynamics is the
rational map `coordIndF μ x = (1−μ)·x²/(x²+(1−x)²) + μ/2`. The center `x = 1/2` is a
fixed point for *every* `μ` (existence everywhere); its linearized multiplier is
`2(1−μ)`, which crosses `1` at `μ⋆ = 1/2` — a **pitchfork**: the center is attracting
above `μ⋆` and repelling below, where the two committed states split off (exhibited on a
whole interval `μ ∈ (0, 3/8]` by the intermediate value theorem). -/

/-- The `Bool` point `(x, 1−x)`. -/
noncomputable def wx (x : ℝ) : Bool → ℝ := fun b => cond b (1 - x) x

lemma wx_mem {μ x : ℝ} (hlo : μ / 2 ≤ x) (hhi : x ≤ 1 - μ / 2) :
    (∀ r, μ * unifHalf r ≤ wx x r) ∧ (∑ r, wx x r = 1) := by
  refine ⟨fun r => ?_, ?_⟩
  · cases r <;> simp only [unifHalf, wx, cond_true, cond_false] <;> linarith
  · rw [Fintype.sum_bool]; simp only [wx, cond_true, cond_false]; ring

/-- The denominator `x² + (1−x)²` is strictly positive everywhere (`= 2(x−½)² + ½`). -/
lemma coordDen_pos (x : ℝ) : 0 < x ^ 2 + (1 - x) ^ 2 := by nlinarith [sq_nonneg (2 * x - 1)]

/-- On `wx x`, the coordination replicator's `false`-fibre is the rational `x²/(x²+(1−x)²)`. -/
lemma coordR_wx {x : ℝ} (h : 0 < x ^ 2 + (1 - x) ^ 2) :
    coordR (wx x) false = x ^ 2 / (x ^ 2 + (1 - x) ^ 2) := by
  have hsum : (∑ s, (wx x s) ^ 2) = x ^ 2 + (1 - x) ^ 2 := by
    rw [Fintype.sum_bool]; simp only [wx, cond_true, cond_false]; ring
  rw [coordR_of_pos (by rw [hsum]; exact h), hsum]
  simp only [wx, cond_false]

/-- The induced false-coordinate dynamics of the coordination replicator-mutator. -/
noncomputable def coordIndF (μ x : ℝ) : ℝ := (1 - μ) * (x ^ 2 / (x ^ 2 + (1 - x) ^ 2)) + μ / 2

/-- The center `x = 1/2` is a fixed point of the induced map for every `μ`. -/
lemma coordIndF_center (μ : ℝ) : coordIndF μ (1 / 2) = 1 / 2 := by
  unfold coordIndF
  rw [show ((1 : ℝ) / 2) ^ 2 / (((1 : ℝ) / 2) ^ 2 + (1 - 1 / 2) ^ 2) = 1 / 2 by norm_num]; ring

/-- The induced map never exceeds the ceiling `1 − μ/2` (since `x²/(x²+(1−x)²) ≤ 1`). -/
lemma coordIndF_upper {μ : ℝ} (hμ1 : μ ≤ 1) (x : ℝ) : coordIndF μ x ≤ 1 - μ / 2 := by
  unfold coordIndF
  have hd := coordDen_pos x
  have h1μ : (0 : ℝ) ≤ 1 - μ := by linarith
  have hphi : x ^ 2 / (x ^ 2 + (1 - x) ^ 2) ≤ 1 := by
    rw [div_le_one hd]; nlinarith [sq_nonneg (1 - x)]
  nlinarith [mul_le_mul_of_nonneg_left hphi h1μ]

lemma coordIndF_continuous (μ : ℝ) : Continuous (coordIndF μ) := by
  unfold coordIndF
  have hden : Continuous (fun x : ℝ => x ^ 2 + (1 - x) ^ 2) := by fun_prop
  have hnum : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  exact (continuous_const.mul (hnum.div hden (fun x => (coordDen_pos x).ne'))).add continuous_const

/-- **Reconstruction.** A root `coordIndF μ x = x` in the interior interval yields a
genuine fixed point `(x, 1−x)` of the coordination replicator-mutator. -/
lemma coordFix {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {x : ℝ}
    (hlo : μ / 2 ≤ x) (hhi : x ≤ 1 - μ / 2) (hfix : coordIndF μ x = x) :
    ∃ p : FlooredSimplex Bool μ unifHalf,
      mutT μ hμ0.le hμ1 unifHalf unifHalf_nonneg unifHalf_sum (coordSel unifHalf) p = p ∧
      p.1 false = x := by
  have hden : 0 < x ^ 2 + (1 - x) ^ 2 := coordDen_pos x
  refine ⟨⟨wx x, wx_mem hlo hhi⟩, ?_, rfl⟩
  apply Subtype.ext
  funext b
  have hf : mutationStep μ unifHalf (coordSel unifHalf) (wx x) false = x := by
    show (1 - μ) * coordR (wx x) false + μ * unifHalf false = x
    rw [coordR_wx hden]; simp only [unifHalf]
    have h := hfix; unfold coordIndF at h; linarith [h]
  have hs := (mutationStep_maps_into μ hμ0.le hμ1 unifHalf unifHalf_nonneg unifHalf_sum
      (coordSel unifHalf) (wx x) (wx_mem hlo hhi).1 (wx_mem hlo hhi).2).2
  rw [Fintype.sum_bool] at hs
  cases b
  · exact hf
  · show mutationStep μ unifHalf (coordSel unifHalf) (wx x) true = wx x true
    have htrue : mutationStep μ unifHalf (coordSel unifHalf) (wx x) true = 1 - x := by
      rw [hf] at hs; linarith
    rw [htrue]; simp only [wx, cond_true]

/-- **C5 — existence everywhere.** For *every* `μ ∈ (0,1]`, the coordination
replicator-mutator has a fixed point (the center `(½,½)`) — attention always settles
somewhere, band or no band. -/
theorem ws9_center_fixed_all {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ p : FlooredSimplex Bool μ unifHalf,
      mutT μ hμ0.le hμ1 unifHalf unifHalf_nonneg unifHalf_sum (coordSel unifHalf) p = p := by
  obtain ⟨p, hp, _⟩ := coordFix hμ0 hμ1 (by linarith) (by linarith) (coordIndF_center μ)
  exact ⟨p, hp⟩

/-- **C6 — multistability on an interval.** For *every* `μ ∈ (0, 3/8]` (not merely one
value) the coordination replicator-mutator has two distinct fixed points: the center and
an off-center committed state produced by the intermediate value theorem. Necessity is a
band, not a point. -/
theorem ws9_multistable_interval {μ : ℝ} (hμ0 : 0 < μ) (hμ38 : μ ≤ 3 / 8) :
    ∃ p q : FlooredSimplex Bool μ unifHalf, p ≠ q ∧
      mutT μ hμ0.le (by linarith) unifHalf unifHalf_nonneg unifHalf_sum (coordSel unifHalf) p = p ∧
      mutT μ hμ0.le (by linarith) unifHalf unifHalf_nonneg unifHalf_sum (coordSel unifHalf) q = q := by
  have hμ1 : μ ≤ 1 := by linarith
  obtain ⟨p, hp, hpf⟩ := coordFix hμ0 hμ1 (by linarith) (by linarith) (coordIndF_center μ)
  have hab : (3 / 4 : ℝ) ≤ 1 - μ / 2 := by linarith
  have hGa : (0 : ℝ) ≤ coordIndF μ (3 / 4) - 3 / 4 := by
    have hval : coordIndF μ (3 / 4) = (1 - μ) * (9 / 10) + μ / 2 := by
      unfold coordIndF
      rw [show ((3 : ℝ) / 4) ^ 2 / (((3 : ℝ) / 4) ^ 2 + (1 - 3 / 4) ^ 2) = 9 / 10 by norm_num]
    rw [hval]; linarith
  have hGb : coordIndF μ (1 - μ / 2) - (1 - μ / 2) ≤ 0 := by
    linarith [coordIndF_upper hμ1 (1 - μ / 2)]
  have hcont : ContinuousOn (fun x => coordIndF μ x - x) (Set.Icc (3 / 4) (1 - μ / 2)) :=
    ((coordIndF_continuous μ).sub continuous_id).continuousOn
  obtain ⟨x0, hx0mem, hx0⟩ :=
    intermediate_value_Icc' hab hcont (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hGb, hGa⟩)
  have hfix : coordIndF μ x0 = x0 := by simp only at hx0; linarith [hx0]
  obtain ⟨hx0lo, hx0hi⟩ := hx0mem
  obtain ⟨q, hq, hqf⟩ := coordFix hμ0 hμ1 (by linarith) hx0hi hfix
  refine ⟨p, q, fun hpq => ?_, hp, hq⟩
  have h12 : (1 : ℝ) / 2 = x0 := by rw [← hpf, hpq]; exact hqf
  linarith [hx0lo]

/-- The center's linearized multiplier `2(1−μ)` — the derivative of the induced map at
the persistent fixed point `x = 1/2`. -/
noncomputable def coordMultiplier (μ : ℝ) : ℝ := 2 * (1 - μ)

/-- **The multiplier is genuine.** `coordMultiplier μ = 2(1−μ)` is the derivative of the
induced dynamics `coordIndF μ` at the center `x = 1/2`. -/
lemma coordIndF_hasDerivAt_center (μ : ℝ) :
    HasDerivAt (coordIndF μ) (coordMultiplier μ) (1 / 2) := by
  have h1x : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have hnum : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * (1 / 2 : ℝ) ^ (2 - 1)) (1 / 2) :=
    hasDerivAt_pow 2 (1 / 2)
  have hden : HasDerivAt (fun x : ℝ => x ^ 2 + (1 - x) ^ 2) 0 (1 / 2) := by
    have h2 := h1x.pow 2
    have hsum := hnum.add h2
    convert hsum using 1; norm_num
  have hd0 : (fun x : ℝ => x ^ 2 + (1 - x) ^ 2) (1 / 2) ≠ 0 := (coordDen_pos (1 / 2)).ne'
  have hφ : HasDerivAt (fun x : ℝ => x ^ 2 / (x ^ 2 + (1 - x) ^ 2)) 2 (1 / 2) := by
    have hq := hnum.div hden hd0
    convert hq using 1; norm_num
  have hstep : HasDerivAt (coordIndF μ) ((1 - μ) * 2) (1 / 2) :=
    (HasDerivAt.const_mul (1 - μ) hφ).add_const (μ / 2)
  rwa [show (1 - μ) * 2 = coordMultiplier μ by unfold coordMultiplier; ring] at hstep

/-- **The pitchfork threshold `μ⋆ = 1/2`.** The center's multiplier is `< 1` (center
attracting) exactly for `μ > 1/2`, and `> 1` (center repelling → the two committed states
split off, as `ws9_multistable_interval` exhibits for `μ ≤ 3/8`) exactly for `μ < 1/2`.
The bifurcation is where the multiplier crosses `1`, at `μ⋆ = 1/2`. -/
theorem ws9_bifurcation (μ : ℝ) :
    (coordMultiplier μ < 1 ↔ 1 / 2 < μ) ∧ (1 < coordMultiplier μ ↔ μ < 1 / 2) := by
  unfold coordMultiplier
  constructor <;> constructor <;> intro h <;> linarith

end Series3.WS9
