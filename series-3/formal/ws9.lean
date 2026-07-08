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

Named `ws9_no_unique_attention` / `ws9_no_contraction` — the honest necessity result,
not `ws9_convergence_characterized` (the interior refinements — cycles, the sharp
bifurcation `μ⋆`, conditional Lyapunov convergence — are left as future obligations).
-/
import ws7

namespace Series3.WS9

open Series3.WS7

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

end Series3.WS9
