/-
# `Theory.MutualCoupling` — the A3 co-direction process (the self-definition node)

The **A3 process** as a *process*: relations co-direct attention asymmetrically in the relata, with
per-relatum capacity `α`. This node holds only the **definitions** the canonical self is built from —
`raise` (the convex pull toward the conserved band), `mutualAttn` (the non-freezable shared attention),
`phaseOf`, the per-relatum `Capacity` `α`, the coupling update `stepMu`, the `jointStep` on `(coupling,
state)`, and the **self** `JointFixed` (a joint fixed point: the state sustained under `Φ_c = schur μ` *and*
the coupling fixed under mutual raising). `Theory.Axioms.IsSelf := JointFixed`, so this node is load-bearing
for paper one's eigenform.

The self is **generative by definition** — `stepMu` (the capacity-limited raising) is baked into
`JointFixed`. The *analysis* of whether the process ignites or spends down (the two-sided `Engine`, the
ignition/spend-down verdict, the boundedness and leading–lagging structure) is the **growth-analysis node**,
unused by any shipped paper; it lives in [`scratch/formal/GenerativeEngine.lean`](../../../scratch/formal/GenerativeEngine.lean)
(paper-three frontier), derived there from these definitions.
-/
import Theory.BandFromAxioms

namespace Theory.MutualCoupling

open Theory.RotatingSpectrum Theory.BandCoincidence Theory.BandFromAxioms
open Matrix
open scoped BigOperators

variable {A : Type*}

/-! ## Part A — the mutual coupling law -/

/-- **Raising.** The convex pull of a coupling modulus `r` toward the conserved band `1`, with weight the
mutual attention `a`: `raise r a = (1 − a) r + a = r + a (1 − r)`. Fixed from A3's "being attended-to
raises the coupling toward the band" — a convex combination of `r` and the band value `1`, *not* tuned. -/
def raise (r a : ℝ) : ℝ := (1 - a) * r + a

@[simp] lemma raise_zero (r : ℝ) : raise r 0 = r := by simp [raise]

@[simp] lemma raise_one (r : ℝ) : raise r 1 = 1 := by simp [raise]

/-- **Raising never lowers** (monotone, toward the band): for `0 ≤ a` and `r ≤ 1`, `r ≤ raise r a`. The
update increases coupling on its own and never decreases it. -/
lemma le_raise {r a : ℝ} (ha : 0 ≤ a) (hr : r ≤ 1) : r ≤ raise r a := by
  have : raise r a - r = a * (1 - r) := by simp [raise]; ring
  nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - r)]

/-- **Raising stays within the band** (capacity bound): for `a, r ∈ [0,1]`, `raise r a ≤ 1`. The convex
form caps the coupling at the conserved band — the built-in brake. -/
lemma raise_le_one {r a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr : r ≤ 1) : raise r a ≤ 1 := by
  unfold raise; nlinarith [mul_le_mul_of_nonneg_left hr (by linarith : (0:ℝ) ≤ 1 - a)]

/-- **Raising stays nonnegative**: for `0 ≤ a`, `0 ≤ r ≤ 1`, `0 ≤ raise r a`. (Uses only `r ≤ 1`, no upper
bound on `a`: `raise r a = a(1−r) + r`.) -/
lemma raise_nonneg {r a : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ raise r a := by
  have : raise r a = a * (1 - r) + r := by simp [raise]; ring
  rw [this]; nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - r)]

/-- **Raising is monotone in the base coupling** (for attention `a ≤ 1`): `b ≤ b' ⟹ raise b a ≤ raise b' a`. -/
lemma raise_mono_base {a b b' : ℝ} (hbb : b ≤ b') (ha : a ≤ 1) : raise b a ≤ raise b' a := by
  unfold raise; nlinarith [mul_le_mul_of_nonneg_left hbb (by linarith : (0:ℝ) ≤ 1 - a)]

/-- **Raising is monotone in the attention** (for base `b ≤ 1`): `a ≤ a' ⟹ raise b a ≤ raise b a'`. -/
lemma raise_mono_attn {a a' b : ℝ} (haa : a ≤ a') (hb : b ≤ 1) : raise b a ≤ raise b a' := by
  unfold raise; nlinarith [mul_le_mul_of_nonneg_right haa (by linarith : (0:ℝ) ≤ 1 - b)]

/-- **`raise` is sensitive to the attention** (for an unsaturated edge `r < 1`): distinct attentions give
distinct results. The engine of non-factoring — the partner's attention genuinely moves the update. -/
lemma raise_ne_of_attn_ne {r a a' : ℝ} (hr : r < 1) (h : a ≠ a') : raise r a ≠ raise r a' := by
  intro he
  have : (a - a') * (1 - r) = 0 := by simp only [raise] at he; nlinarith [he]
  rcases mul_eq_zero.mp this with h1 | h2
  · exact h (by linarith [sub_eq_zero.mp h1])
  · linarith

/-- **Mutual attention across edge `(i,j)`.** The symmetric product of the two ends' attention — `i`'s to
`j` (`M i j`) and `j`'s to `i` (`M j i`). Symmetric, and it vanishes if *either* end is frozen. -/
noncomputable def mutualAttn (M : Matrix A A ℂ) (i j : A) : ℝ := ‖M i j‖ * ‖M j i‖

/-- **Co-directed (symmetric).** `mutualAttn M i j = mutualAttn M j i`. -/
lemma mutualAttn_symm (M : Matrix A A ℂ) (i j : A) : mutualAttn M i j = mutualAttn M j i := by
  simp [mutualAttn, mul_comm]

/-- **Freezing the partner collapses attention.** If `j` gives no attention back (`M j i = 0`), the mutual
attention is `0` — the update will not raise the coupling. ("Neither end closes the loop alone.") -/
lemma mutualAttn_collapse_right {M : Matrix A A ℂ} {i j : A} (h : M j i = 0) :
    mutualAttn M i j = 0 := by simp [mutualAttn, h]

/-- Symmetrically, freezing `i` (`M i j = 0`) collapses the attention. -/
lemma mutualAttn_collapse_left {M : Matrix A A ℂ} {i j : A} (h : M i j = 0) :
    mutualAttn M i j = 0 := by simp [mutualAttn, h]

lemma mutualAttn_nonneg (M : Matrix A A ℂ) (i j : A) : 0 ≤ mutualAttn M i j :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The unit phase of `z` (and `1` at `0`): the direction `z` points, stripped of modulus. -/
noncomputable def phaseOf (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] lemma norm_phaseOf (z : ℂ) : ‖phaseOf z‖ = 1 := by
  unfold phaseOf
  by_cases h : z = 0
  · simp [h]
  · rw [if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (by simpa using h)]

/-- **Per-end capacity (constitutive finiteness `α`).** `α i ∈ [0,1]` is how much node `i` can afford to
raise its couplings, given its standing in *all* its other relations. A depleted end (`α i` small) raises
slowly; a rich end raises fast. This is what makes the mutual loop **asymmetric** without imposing or
forbidding `μ_{ij} = μ_{ji}` — the inequality `α i ≠ α j` is structure, not symmetry to break. -/
abbrev Capacity (A : Type*) := A → ℝ

/-- **The coupling update** `μ ↦ μ'`: end `i` raises its coupling to `j` toward the band by the *mutual*
attention across the edge — but **rate-limited by `i`'s own capacity** `α i`. `μ' i j = raise ‖μ i j‖
(α i · mutualAttn M i j) · phaseOf (μ i j)`. The attention `mutualAttn` is non-freezable (both ends, by the
product); the gain `α i` is `i`'s alone, so `μ_{ij}` and `μ_{ji}` are raised at *different* rates and the
loop is asymmetric (`asymmetry_emerges`). The phase is preserved, so a raised rotating edge lands in the
rotating *energy* band, faithful to `PhaseBearing`. -/
noncomputable def stepMu (α : Capacity A) (μ : A → A → ℂ) (M : Matrix A A ℂ) (i j : A) : ℂ :=
  ((raise ‖μ i j‖ (α i * mutualAttn M i j) : ℝ) : ℂ) * phaseOf (μ i j)

/-- **The modulus reduction.** The whole dynamical content of `stepMu` is the real `raise` law on moduli,
with `i`'s capacity gating the gain: `‖stepMu α μ M i j‖ = raise ‖μ i j‖ (α i · mutualAttn M i j)`. -/
lemma norm_stepMu {α : Capacity A} {μ : A → A → ℂ} {M : Matrix A A ℂ} {i j : A}
    (h : 0 ≤ raise ‖μ i j‖ (α i * mutualAttn M i j)) :
    ‖stepMu α μ M i j‖ = raise ‖μ i j‖ (α i * mutualAttn M i j) := by
  rw [stepMu, norm_mul, norm_phaseOf, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h]

/-- **The joint step** on `(coupling, state)`: the state evolves under `Φ_c = schur μ` (old coupling) and
each end raises its coupling by the old state's mutual attention, at its own capacity. A **self** is a joint
fixed point of both. -/
noncomputable def jointStep (α : Capacity A) (p : (A → A → ℂ) × Matrix A A ℂ) :
    (A → A → ℂ) × Matrix A A ℂ :=
  (fun i j => stepMu α p.1 p.2 i j, schur p.1 p.2)

/-- A **joint fixed point** (a self): the state is sustained under `Φ_c = schur μ` *and* the coupling is
fixed under mutual raising. The two conditions do not factor through either end alone (`coupling_not_factor`). -/
def JointFixed (α : Capacity A) (μ : A → A → ℂ) (M : Matrix A A ℂ) : Prop :=
  (∀ i j, schur μ M i j = M i j) ∧ (∀ i j, stepMu α μ M i j = μ i j)

end Theory.MutualCoupling
