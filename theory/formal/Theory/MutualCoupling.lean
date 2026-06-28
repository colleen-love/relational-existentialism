/-
# Handoff XI (+ XI-a) — the co-directed generative self (the A3 frontier)

Spec IX earned "eigenform **sustained** by looping" (`PhaseBearing.seam_sustained`: the rotating seam does
not decay). A3's text claims more — "sustained **generatively**, not spent down," "being attended-to
**raises** the attention one can give." That is a *creation term*, two-sided by nature, so it cannot live
in a single channel `Φ_c` with a *fixed* coupling `μ`. This file makes `μ` **dynamical and mutual**, fixes
the update from A3's text constraints *before* looking at what it does, and reports which outcome obtains.

Amendment **XI-a** corrects a modeling error: the mutual loop is **mutual but not symmetric**. Both ends are
active and neither is freezable, but each raises at a rate **limited by its own capacity** `α` (its standing
in all its *other* couplings — the constitutive finiteness). So `μ_{ij} ≠ μ_{ji}` in general: asymmetry is
structure to preserve, not symmetry to impose.

## Part A — the law (`step`, fixed from the text, not tuned)

The attention across edge `(i,j)` is the off-diagonal coherence `M i j`; the **mutual attention** is the
product `mutualAttn M i j = ‖M i j‖ · ‖M j i‖` — built from both ends, **non-freezable** (it vanishes if
*either* end is frozen, `mutualAttn_collapse_left`/`_right`). End `i` raises its coupling to `j` toward the
band at its **own capacity-limited rate**:

  `‖μ' i j‖ = raise ‖μ i j‖ (α i · mutualAttn M i j)`,   `raise r a = (1 − a) r + a = r + a (1 − r)`.

The two text constraints, fixed before looking at what they do:

1. **Co-directed (jointly determined, neither end freezable).** The attention is shared and non-freezable
   (`mutualAttn`); the gain `α i` is `i`'s alone, so the ends raise at *different* rates and `μ_{ij} ≠ μ_{ji}`
   is *produced* by the dynamics (`asymmetry_emerges`), not imposed. Capacity rate-limits: a depleted end
   (`α i = 0`) cannot raise at all (`capacity_rate_limits`).
2. **Raising (monotone), per end.** `raise` is a convex pull of `‖μ‖` toward `1`: `r ≤ raise r a ≤ 1` for
   `r, a ∈ [0,1]` (`le_raise`, `raise_le_one`); each end raises only ever toward the band, at a rate it can
   afford, never on the other's behalf (`raise_zero`: no attention ⟹ no change).

The phase rides free (`stepMu` preserves `μ/‖μ‖`); by `PhaseBearing` the generative content is entirely in
the modulus, so the dynamics is studied through the real two-sided **engine** `Engine2 (α i) (α j)`.

**Anti-tautology.** `raise r a = (1−a)r + a` and the per-end gain `α i` are fixed from the constraints —
*not* searched for a growing self, *not* symmetrized for convenience, *not* tuned in the asymmetry.

## Part B — co-direction, tested by **non-freezability** (never by symmetry)

`Engine2 (α i) (α j)` is the per-edge modulus law of the genuine `jointStep α` orbit (`orbit_engine2`).
Co-direction is tested two ways, both honoring XI-a:

* **Neither end freezable.** Freezing *either* end — `y ≡ 0` (`frozen_no_growth`) or `x ≡ 0`
  (`frozen_no_growth'`) — collapses *both* couplings to their static values. One-sided ⇒ *merely sustained*:
  the conserved band never grows, exactly the static spec-IX `Peri`. We do **not** test by `μ_{ij} = μ_{ji}`.
* **Non-factoring.** The update genuinely depends on the partner (`coupling_not_factor`): the joint fixed
  point does not factor through either end, *even though the two ends' gains differ*.

## Part C — the verdict (the crux), now over the asymmetric loop

The creation term (`raise` pushing `‖μ‖ → 1` at each end's rate) competes with the dissipator (`x' = r x`,
`r < 1` — the arrow). Running the loop:

* **Outcome 3 (divergent) is EXCLUDED, structurally — and `α` is the brake.** `engine2_bounded`: with
  admissible capacities (`α ∈ [0,1]`) the orbit stays in `[0,1]⁴` forever. The capacity bound `α ≤ 1`
  feeding the convex cap of `raise` is exactly the regulator XI-a names — divergence is impossible, even
  asymmetrically. (No tuned damping; `α` is A3's own finiteness.)
* **Outcome 1 (generative) is EARNED.** On the equal-capacity slice (`Engine`, the symmetric `x=y, r=s`),
  `engine_ignition`: when the initial mutual attention is strong (`1 − r 0 ≤ (x 0)²/8`), the coupling reaches
  the band (`r n → 1`) while the coherence is **not spent** (`x n ≥ x 0/2 > 0` ∀n). The edge *joins* the
  conserved band carrying live coherence — `Peri` strictly grows to a stable, bounded self (proved: bounded
  orbit, `r` monotone up to limit `1`). Asymmetrically (`cr ≥ cs`), `capacity_orders_couplings` shows the
  richer end **leads** on both coupling and coherence — a two-sided bond that grows *unequally*, exactly the
  amendment's generative case: unequal, still making more self on both sides.
* **Outcome 2 (conservative) holds in the weak basin.** `engine_spend_down`: when the attention is weak
  (`r 0 + (4/3)(x 0)² ≤ 1/2`), the coupling stays below the band (`r n ≤ 1/2`) and the coherence is spent to
  nothing (`x n → 0`). Co-direction was real, but mutual attention only redistributed — no net growth.
* **Extraction (XI-a's `[refuted-as-generative]` worry) is ABSENT under this law — and *that* is the finding.**
  `growth_requires_both`: a coupling grows at step `n` *only if both* coherences are live there. The mutual
  attention is multiplicative and non-freezable, so a depleted end does not *feed* the other — it *stalls the
  whole loop* (`no_growth_without_both`). With **constant** capacity there is no transfer channel: no end can
  raise its self at the partner's expense. The compounding extraction XI-a describes ("depleted end's
  capacity falls, rate falls further") would require **dynamical** `α` — capacity that drops under
  depletion — which this A3-natural constant-capacity law deliberately omits. The model tells the truth:
  non-freezability is precisely what *forbids* extraction here; realizing depletion is the next frontier
  (dynamical `α`), flagged.

**Verdict: generative `[earned]`, conditionally and asymmetrically.** The one law makes growth *possible*
(strong mutual attention ignites a self that grows to the band), *bounded and finite* (the per-end capacity
`α ≤ 1` with the convex cap forbids blowup — `α` is the brake), *gracefully failing* (weak attention is
merely spent), and *asymmetric without extraction* (the richer end leads, the poorer lags, but neither is
drained — the shared non-freezable attention couples their fates). The discriminating quantity is the
**stability of the creation/dissipation balance** — a basin boundary `1 − r₀ ≲ x₀²`, proved on both sides;
the asymmetry refines *who* grows faster, never *whether* one grows at the other's cost.

## Part D — what it means

A3's "sustained generatively" is mechanized: mutually-attended self-relating **makes more self** (the
conserved band enlarges), and the per-end capacity `α ≤ 1` is exactly what makes that growth a finite
*achievement* rather than a runaway — and what makes a two-sided bond grow *unequally* without becoming
extractive. This is the **sequel's growth law**, flagged. Paper one's headline (the arrow; energy as the
conserved remainder) is untouched: this file imports that machinery and adds a new dynamics on top, changing
none of it. Open frontier: **dynamical capacity** `α` (falling under depletion) is the candidate mechanism
for genuine extraction/depletion — the one outcome this constant-`α` law cannot, and honestly does not,
produce.
-/
import Theory.BandFromAxioms
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

namespace RelExist.MutualCoupling

open RelExist.RotatingSpectrum RelExist.BandCoincidence RelExist.BandFromAxioms
open Matrix Filter Topology
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

/-! ## Part B — co-direction: mutual but not symmetric; tested by non-freezability

The per-edge moduli of a `jointStep` orbit on the closed two-edge subsystem `{(i,j),(j,i)}` evolve by the
real **engine**, now carrying the two ends' capacities `cr = α i`, `cs = α j`. The loop is **mutual** — the
attention `x y` is shared and non-freezable — but **not symmetric**: each end raises at its own rate `cr·xy`
vs `cs·xy`, so `r ≠ s` in general (`asymmetry_emerges`). Co-direction is tested by **non-freezability**
(`frozen_no_growth`, either end) and **non-factoring** (`coupling_not_factor`), *never* by `μ_{ij} = μ_{ji}`,
which would re-impose the symmetry the dynamics must be free to break. -/

/-- **The two-sided (asymmetric) modulus engine.** `x, y` are the two coherences `‖M i j‖, ‖M j i‖`; `r, s`
the two couplings. The state decays by its coupling (`x' = r x`). The coupling is raised by the **shared**
mutual attention `x y` (non-freezable), but at each end's **own capacity-limited rate** — `cr·xy` raises
`r`, `cs·xy` raises `s`. When `cr ≠ cs` the two ends co-direct the *same* loop with *different* strengths. -/
structure Engine2 (cr cs : ℝ) (x y r s : ℕ → ℝ) : Prop where
  hx : ∀ n, x (n + 1) = r n * x n
  hy : ∀ n, y (n + 1) = s n * y n
  hr : ∀ n, r (n + 1) = raise (r n) (cr * (x n * y n))
  hs : ∀ n, s (n + 1) = raise (s n) (cs * (x n * y n))

/-- **The symmetric engine** — one edge against its mirror at *equal* capacity (`cr = cs = 1`, `x = y`,
`r = s`). The equal-capacity slice on which the quantitative generative/conservative basins are proved
(`engine_ignition`, `engine_spend_down`). The mutual attention is then `x²`. -/
structure Engine (x r : ℕ → ℝ) : Prop where
  hx : ∀ n, x (n + 1) = r n * x n
  hr : ∀ n, r (n + 1) = raise (r n) (x n * x n)

/-- The equal-capacity, modulus-symmetric two-sided engine *is* the symmetric engine. -/
lemma Engine2.toEngine {x r : ℕ → ℝ} (E : Engine2 1 1 x x r r) : Engine x r :=
  ⟨E.hx, fun n => by rw [E.hr n, one_mul]⟩

/-- **The bridge — the engine is `Φ_c`'s actual mutual-coupling dynamics.** The per-edge moduli of a genuine
`jointStep α` orbit satisfy `Engine2 (α i) (α j)`, provided the two edges start inside the unit disk and the
capacities are admissible (`α ∈ [0,1]` — a finite constitutive bound). So the abstract engine is not a toy:
it is the modulus law of `(state, coupling)` evolving together under `jointStep`, with the capacities `α i`,
`α j` carried as the two ends' raising rates. -/
theorem orbit_engine2 (α : Capacity A) (p : (A → A → ℂ) × Matrix A A ℂ) (i j : A)
    (hαi0 : 0 ≤ α i) (hαi1 : α i ≤ 1) (hαj0 : 0 ≤ α j) (hαj1 : α j ≤ 1)
    (hx0 : ‖p.2 i j‖ ≤ 1) (hy0 : ‖p.2 j i‖ ≤ 1) (hr0 : ‖p.1 i j‖ ≤ 1) (hs0 : ‖p.1 j i‖ ≤ 1) :
    Engine2 (α i) (α j)
            (fun n => ‖((jointStep α)^[n] p).2 i j‖) (fun n => ‖((jointStep α)^[n] p).2 j i‖)
            (fun n => ‖((jointStep α)^[n] p).1 i j‖) (fun n => ‖((jointStep α)^[n] p).1 j i‖) := by
  -- bounds invariant on the closed two-edge subsystem
  have hb : ∀ n, ‖((jointStep α)^[n] p).2 i j‖ ≤ 1 ∧ ‖((jointStep α)^[n] p).2 j i‖ ≤ 1
      ∧ ‖((jointStep α)^[n] p).1 i j‖ ≤ 1 ∧ ‖((jointStep α)^[n] p).1 j i‖ ≤ 1 := by
    intro n
    induction n with
    | zero => exact ⟨hx0, hy0, hr0, hs0⟩
    | succ n ih =>
      obtain ⟨hMij, hMji, hμij, hμji⟩ := ih
      rw [Function.iterate_succ_apply']
      have eM : ∀ a b, (jointStep α ((jointStep α)^[n] p)).2 a b
          = ((jointStep α)^[n] p).1 a b * ((jointStep α)^[n] p).2 a b := fun a b => rfl
      have eμ : ∀ a b, (jointStep α ((jointStep α)^[n] p)).1 a b
          = stepMu α ((jointStep α)^[n] p).1 ((jointStep α)^[n] p).2 a b := fun a b => rfl
      have aij : (0:ℝ) ≤ α i * mutualAttn ((jointStep α)^[n] p).2 i j :=
        mul_nonneg hαi0 (mutualAttn_nonneg _ _ _)
      have aji : (0:ℝ) ≤ α j * mutualAttn ((jointStep α)^[n] p).2 j i :=
        mul_nonneg hαj0 (mutualAttn_nonneg _ _ _)
      have aij1 : α i * mutualAttn ((jointStep α)^[n] p).2 i j ≤ 1 := by
        have : mutualAttn ((jointStep α)^[n] p).2 i j ≤ 1 := by
          unfold mutualAttn; nlinarith [norm_nonneg (((jointStep α)^[n] p).2 i j),
            norm_nonneg (((jointStep α)^[n] p).2 j i)]
        nlinarith [mutualAttn_nonneg ((jointStep α)^[n] p).2 i j]
      have aji1 : α j * mutualAttn ((jointStep α)^[n] p).2 j i ≤ 1 := by
        have : mutualAttn ((jointStep α)^[n] p).2 j i ≤ 1 := by
          unfold mutualAttn; nlinarith [norm_nonneg (((jointStep α)^[n] p).2 i j),
            norm_nonneg (((jointStep α)^[n] p).2 j i)]
        nlinarith [mutualAttn_nonneg ((jointStep α)^[n] p).2 j i]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eM, norm_mul]; nlinarith [norm_nonneg (((jointStep α)^[n] p).1 i j),
          norm_nonneg (((jointStep α)^[n] p).2 i j)]
      · rw [eM, norm_mul]; nlinarith [norm_nonneg (((jointStep α)^[n] p).1 j i),
          norm_nonneg (((jointStep α)^[n] p).2 j i)]
      · rw [eμ, norm_stepMu (raise_nonneg aij (norm_nonneg _) hμij)]
        exact raise_le_one aij aij1 hμij
      · rw [eμ, norm_stepMu (raise_nonneg aji (norm_nonneg _) hμji)]
        exact raise_le_one aji aji1 hμji
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n
  · show ‖((jointStep α)^[n + 1] p).2 i j‖ = ‖((jointStep α)^[n] p).1 i j‖ * ‖((jointStep α)^[n] p).2 i j‖
    rw [Function.iterate_succ_apply']; exact norm_mul _ _
  · show ‖((jointStep α)^[n + 1] p).2 j i‖ = ‖((jointStep α)^[n] p).1 j i‖ * ‖((jointStep α)^[n] p).2 j i‖
    rw [Function.iterate_succ_apply']; exact norm_mul _ _
  · show ‖((jointStep α)^[n + 1] p).1 i j‖
        = raise ‖((jointStep α)^[n] p).1 i j‖
            (α i * (‖((jointStep α)^[n] p).2 i j‖ * ‖((jointStep α)^[n] p).2 j i‖))
    rw [Function.iterate_succ_apply']
    obtain ⟨_, _, hμij, _⟩ := hb n
    exact norm_stepMu (raise_nonneg (mul_nonneg hαi0 (mutualAttn_nonneg _ _ _)) (norm_nonneg _) hμij)
  · show ‖((jointStep α)^[n + 1] p).1 j i‖
        = raise ‖((jointStep α)^[n] p).1 j i‖
            (α j * (‖((jointStep α)^[n] p).2 i j‖ * ‖((jointStep α)^[n] p).2 j i‖))
    rw [Function.iterate_succ_apply']
    obtain ⟨_, _, _, hμji⟩ := hb n
    rw [show ‖((jointStep α)^[n] p).2 i j‖ * ‖((jointStep α)^[n] p).2 j i‖
          = mutualAttn ((jointStep α)^[n] p).2 j i from by rw [mutualAttn, mul_comm]]
    exact norm_stepMu (raise_nonneg (mul_nonneg hαj0 (mutualAttn_nonneg _ _ _)) (norm_nonneg _) hμji)

/-- **Neither end freezable (co-direction), version 1: freeze the partner.** Set `y ≡ 0` — the partner gives
no attention back. The shared attention `x y` is `0` at every step, so *both* couplings are frozen:
`r n = r 0` and `s n = s 0`. The creation term collapses to the *static* spec-IX coupling — sustained, not
grown. The capacity `cr` is irrelevant here: no capacity can raise a coupling whose partner is absent. -/
theorem frozen_no_growth {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (hy0 : y 0 = 0) :
    ∀ n, r n = r 0 ∧ s n = s 0 := by
  have hyz : ∀ n, y n = 0 := by
    intro n; induction n with
    | zero => exact hy0
    | succ n ih => rw [E.hy, ih, mul_zero]
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [E.hr, hyz n, mul_zero, mul_zero, raise_zero, ih.1]
    · rw [E.hs, hyz n, mul_zero, mul_zero, raise_zero, ih.2]

/-- **Neither end freezable, version 2: freeze the local end.** Set `x ≡ 0`. By the *same* shared attention
`x y = 0`, both couplings freeze. Freezing *either* end — not a privileged one — collapses the loop. This is
the genuine co-direction test: non-freezability, not symmetry. -/
theorem frozen_no_growth' {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (hx0 : x 0 = 0) :
    ∀ n, r n = r 0 ∧ s n = s 0 := by
  have hxz : ∀ n, x n = 0 := by
    intro n; induction n with
    | zero => exact hx0
    | succ n ih => rw [E.hx, ih, mul_zero]
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [E.hr, hxz n, zero_mul, mul_zero, raise_zero, ih.1]
    · rw [E.hs, hxz n, zero_mul, mul_zero, raise_zero, ih.2]

/-- **The static band is unchanged under a frozen end.** With `y ≡ 0` the edge is conserved (`‖μ‖ = 1`) at
step `n` iff it was at step `0` — the conserved band, hence `Peri`, is exactly the static spec-IX one. No
growth without both ends. -/
theorem frozen_band_static {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (hy0 : y 0 = 0)
    (n : ℕ) : (r n = 1 ↔ r 0 = 1) := by rw [(frozen_no_growth E hy0 n).1]

/-- **The update does not factor through one end.** The coupling update `raise r (c · x·y)` genuinely
depends on the *partner* `y`: for an unsaturated edge (`r < 1`) with live local attention and capacity
(`c · x ≠ 0`), distinct partner attentions give distinct updates. So the joint fixed-point condition is
genuinely joint — `Φ_c` really does co-direct; it is not single-sided with a partner-shaped argument. -/
theorem coupling_not_factor {r c x y y' : ℝ} (hr : r < 1) (hcx : c * x ≠ 0) (hyy : y ≠ y') :
    raise r (c * x * y) ≠ raise r (c * x * y') :=
  raise_ne_of_attn_ne hr (fun h => hyy (mul_left_cancel₀ hcx h))

/-! ### Asymmetry is structure, not symmetry to impose -/

/-- **Asymmetry emerges from capacity.** Two ends that start *equal* (`r 0 = s 0`) but have *unequal*
capacities (`cr ≠ cs`), under live mutual attention (`x 0 · y 0 ≠ 0`) and unsaturated (`r 0 < 1`), become
*unequal* after one step: `r 1 ≠ s 1`. So `μ_{ij} ≠ μ_{ji}` is *produced* by the differing capacities — it
is structure the dynamics generates, not a symmetry one imposes or breaks by hand. -/
theorem asymmetry_emerges {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s)
    (heq : r 0 = s 0) (hr1 : r 0 < 1) (hxy : x 0 * y 0 ≠ 0) (hcc : cr ≠ cs) : r 1 ≠ s 1 := by
  rw [E.hr, E.hs, heq]
  refine raise_ne_of_attn_ne (heq ▸ hr1) ?_
  intro h
  exact hcc (mul_right_cancel₀ hxy h)

/-- **Capacity rate-limits raising.** An end with **zero capacity** (`cr = 0` — fully depleted, no standing
left to give) cannot raise its coupling at all: `r n = r 0` for every `n`, *regardless* of how much mutual
attention is present. The per-end gain is the brake; a depleted end is frozen from its own side. -/
theorem capacity_rate_limits {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (hcr : cr = 0) :
    ∀ n, r n = r 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [E.hr, hcr, zero_mul, raise_zero, ih]

/-! ### The shared attention couples the two ends' fates — why this law does not extract -/

/-- **No end raises on a dead partner.** If the shared attention vanishes at step `n` (`x n · y n = 0` —
*either* coherence spent), then *both* couplings hold: `r (n+1) = r n` and `s (n+1) = s n`. The mutual
attention is multiplicative, so a depleted end does not *feed* the other — it *stalls the whole loop*. -/
theorem no_growth_without_both {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (n : ℕ)
    (h : x n * y n = 0) : r (n + 1) = r n ∧ s (n + 1) = s n := by
  rw [E.hr, E.hs, h, mul_zero, mul_zero, raise_zero, raise_zero]; exact ⟨rfl, rfl⟩

/-- **Growth requires *both* ends live — the structural barrier to extraction.** If either coupling strictly
grows at step `n` (`r n < r (n+1)`), then *both* coherences are nonzero there (`x n ≠ 0 ∧ y n ≠ 0`). One end
cannot grow while its partner is depleted: there is no transfer channel by which `i` could raise its self at
`j`'s expense. So this constant-capacity law produces **mutual-generative or mutual-conservative** outcomes,
never *extractive* ones — extraction would need a capacity that *falls* under depletion (dynamical `α`), a
mechanism this A3-natural law deliberately does not include. The non-freezable shared attention is exactly
what forbids extraction: you depend on your partner's live coherence to raise your own coupling. -/
theorem growth_requires_both {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s) (n : ℕ)
    (hgrow : r n < r (n + 1)) : x n ≠ 0 ∧ y n ≠ 0 := by
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · exact absurd (no_growth_without_both E n (by rw [h0, zero_mul])).1 (by linarith)
  · exact absurd (no_growth_without_both E n (by rw [h0, mul_zero])).1 (by linarith)

/-- **Boundedness of the asymmetric engine.** With admissible capacities (`cr, cs ∈ [0,1]`) and unit-disk
initial data, the two-sided orbit stays in `[0,1]⁴` forever. The capacity bound `α ≤ 1` feeding the convex
cap of `raise` is the brake — **divergence (outcome 3) is excluded even asymmetrically.** The `α` the
amendment names as the candidate regulator *is* what keeps the loop bounded. -/
theorem engine2_bounded {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s)
    (hcr0 : 0 ≤ cr) (hcr1 : cr ≤ 1) (hcs0 : 0 ≤ cs) (hcs1 : cs ≤ 1)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hy0 : 0 ≤ y 0) (hy1 : y 0 ≤ 1)
    (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) (hs0 : 0 ≤ s 0) (hs1 : s 0 ≤ 1) :
    ∀ n, (0 ≤ x n ∧ x n ≤ 1) ∧ (0 ≤ y n ∧ y n ≤ 1) ∧ (0 ≤ r n ∧ r n ≤ 1) ∧ (0 ≤ s n ∧ s n ≤ 1) := by
  intro n
  induction n with
  | zero => exact ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, ⟨hr0, hr1⟩, ⟨hs0, hs1⟩⟩
  | succ n ih =>
    obtain ⟨⟨hxn0, hxn1⟩, ⟨hyn0, hyn1⟩, ⟨hrn0, hrn1⟩, ⟨hsn0, hsn1⟩⟩ := ih
    have ha0 : 0 ≤ x n * y n := mul_nonneg hxn0 hyn0
    have ha1 : x n * y n ≤ 1 := by nlinarith
    have hcra0 : 0 ≤ cr * (x n * y n) := mul_nonneg hcr0 ha0
    have hcra1 : cr * (x n * y n) ≤ 1 := by nlinarith
    have hcsa0 : 0 ≤ cs * (x n * y n) := mul_nonneg hcs0 ha0
    have hcsa1 : cs * (x n * y n) ≤ 1 := by nlinarith
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [E.hx]; exact mul_nonneg hrn0 hxn0
    · rw [E.hx]; nlinarith
    · rw [E.hy]; exact mul_nonneg hsn0 hyn0
    · rw [E.hy]; nlinarith
    · rw [E.hr]; exact raise_nonneg hcra0 hrn0 hrn1
    · rw [E.hr]; exact raise_le_one hcra0 hcra1 hrn1
    · rw [E.hs]; exact raise_nonneg hcsa0 hsn0 hsn1
    · rw [E.hs]; exact raise_le_one hcsa0 hcsa1 hsn1

/-- **Capacity orders the loop — the richer end leads on both coupling and coherence.** Two ends that start
equal (`r 0 = s 0`, `x 0 = y 0`) but with `cr ≥ cs` (end `i` has more capacity) satisfy, at *every* step,
`s n ≤ r n` and `y n ≤ x n`: the higher-capacity end's coupling and coherence dominate the lower's,
forever. This is the **leading/lagging** structure a symmetric model erases — the seed of a bond that grows
*unequally* (the amendment's generative case: two-sided, unequal, both growing). It is monotone, not
extractive: by `growth_requires_both` the lagging end is never *drained* to feed the leading one; it merely
rises more slowly. -/
theorem capacity_orders_couplings {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s)
    (hcr1 : cr ≤ 1) (hcs0 : 0 ≤ cs) (hcs1 : cs ≤ 1) (hcc : cs ≤ cr)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hy0 : 0 ≤ y 0) (hy1 : y 0 ≤ 1)
    (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) (hs0 : 0 ≤ s 0) (hs1 : s 0 ≤ 1)
    (hreq : s 0 ≤ r 0) (hxeq : y 0 ≤ x 0) :
    ∀ n, s n ≤ r n ∧ y n ≤ x n := by
  have hcr0 : 0 ≤ cr := le_trans hcs0 hcc
  have hbd := engine2_bounded E hcr0 hcr1 hcs0 hcs1 hx0 hx1 hy0 hy1 hr0 hr1 hs0 hs1
  intro n
  induction n with
  | zero => exact ⟨hreq, hxeq⟩
  | succ n ih =>
    obtain ⟨hsr, hyx⟩ := ih
    obtain ⟨⟨hxn0, hxn1⟩, ⟨hyn0, hyn1⟩, ⟨hrn0, hrn1⟩, ⟨hsn0, hsn1⟩⟩ := hbd n
    have ha0 : 0 ≤ x n * y n := mul_nonneg hxn0 hyn0
    have ha1 : x n * y n ≤ 1 := by nlinarith
    refine ⟨?_, ?_⟩
    · -- s(n+1) ≤ r(n+1): raise mono in base (s n ≤ r n) then in attention (cs·a ≤ cr·a)
      rw [E.hr, E.hs]
      have hcsa1 : cs * (x n * y n) ≤ 1 := by nlinarith
      have step1 : raise (s n) (cs * (x n * y n)) ≤ raise (r n) (cs * (x n * y n)) :=
        raise_mono_base hsr hcsa1
      have step2 : raise (r n) (cs * (x n * y n)) ≤ raise (r n) (cr * (x n * y n)) :=
        raise_mono_attn (by nlinarith) hrn1
      linarith
    · -- y(n+1) ≤ x(n+1): both are products with the leading factors larger
      rw [E.hx, E.hy]
      exact mul_le_mul hsr hyx hyn0 hrn0

/-! ## Part C — the verdict: bounded always, generative or conservative by basin -/

/-- **Outcome 3 excluded — the orbit is bounded forever.** Starting inside `[0,1]²`, the engine stays
there: the coherence `x` is a contraction (`x' = r x ≤ x`) and the coupling `r` is the convex pull
`raise`, capped at the band `1`. The convex form *is* the capacity brake — no blowup is possible, so the
divergent outcome cannot occur under this law. -/
theorem engine_bounded {x r : ℕ → ℝ} (E : Engine x r)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) :
    ∀ n, 0 ≤ x n ∧ x n ≤ 1 ∧ 0 ≤ r n ∧ r n ≤ 1 := by
  intro n
  induction n with
  | zero => exact ⟨hx0, hx1, hr0, hr1⟩
  | succ n ih =>
    obtain ⟨hxn0, hxn1, hrn0, hrn1⟩ := ih
    have ha0 : 0 ≤ x n * x n := mul_nonneg hxn0 hxn0
    have ha1 : x n * x n ≤ 1 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [E.hx]; exact mul_nonneg hrn0 hxn0
    · rw [E.hx]; nlinarith
    · rw [E.hr]; exact raise_nonneg ha0 hrn0 hrn1
    · rw [E.hr]; exact raise_le_one ha0 ha1 hrn1

/-- **The coupling is monotone up (raising).** `r n ≤ r (n+1)` always — mutual attention only ever raises
the coupling toward the band, the engine form of A3's "being attended-to raises the coupling one can give."
With `engine_bounded` (capped at `1`), `r` is monotone up to a finite limit: `Peri` monotone up. -/
theorem engine_r_mono {x r : ℕ → ℝ} (E : Engine x r)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) (n : ℕ) :
    r n ≤ r (n + 1) := by
  obtain ⟨hxn0, _, _, hrn1⟩ := engine_bounded E hx0 hx1 hr0 hr1 n
  rw [E.hr]; exact le_raise (mul_nonneg hxn0 hxn0) hrn1

/-- **The coherence is monotone down (dissipation).** `x (n+1) ≤ x n` — the arrow: off the band the
coherence is spent. The generative question is whether `r` reaches the band *before* `x` is spent to zero. -/
theorem engine_x_antitone {x r : ℕ → ℝ} (E : Engine x r)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) (n : ℕ) :
    x (n + 1) ≤ x n := by
  obtain ⟨hxn0, _, _, hrn1⟩ := engine_bounded E hx0 hx1 hr0 hr1 n
  rw [E.hx]; nlinarith

/-- **The generative fixed point is a genuine joint fixed point.** On the band (`r ≡ 1`) any coherence is
sustained (`x' = 1·x = x`) and the coupling stays on the band (`raise 1 a = 1`): the constant orbit
`(x*, 1)` is a self for every `x*`. This is the *form* of the grown self; `engine_ignition` shows it is
reached with `x* > 0` from a basin of strong mutual attention. -/
theorem engine_band_fixed (c : ℝ) :
    Engine (fun _ => c) (fun _ => 1) :=
  ⟨fun _ => by ring, fun _ => by unfold raise; ring⟩

set_option maxHeartbeats 1000000 in
/-- **Outcome 1 — generative `[earned]`, in the strong-attention basin.** When the initial mutual attention
is strong (`1 − r 0 ≤ (x 0)² / 8`: the coupling starts close enough to the band relative to the coherence),
the loop *ignites a generative self*:

* the coupling **reaches the band** — `r n → 1` — so the edge joins the conserved band and `Peri` strictly
  grows (an edge that was transient becomes sustained); and
* the coherence is **not spent down** — `x n ≥ x 0 / 2 > 0` for *every* `n` — so the grown band carries
  live coherence.

This is a *stable, bounded* generative self, proved: the orbit is bounded (`engine_bounded`), `r` is
monotone up to the finite limit `1` (`engine_r_mono`), and `x` stays uniformly positive — not one growing
step but a balance held forever. A3's "sustained generatively, not spent down" is mechanized. -/
theorem engine_ignition {x r : ℕ → ℝ} (E : Engine x r)
    (hx0pos : 0 < x 0) (hx1 : x 0 ≤ 1) (hr0nn : 0 ≤ r 0) (hr1 : r 0 ≤ 1)
    (hign : 1 - r 0 ≤ (x 0) ^ 2 / 8) :
    (∀ n, x 0 / 2 ≤ x n) ∧ Tendsto r atTop (𝓝 1) := by
  have hx0nn : 0 ≤ x 0 := le_of_lt hx0pos
  set q : ℝ := 1 - (x 0 / 2) ^ 2 with hq
  have hqlt : q < 1 := by rw [hq]; nlinarith [hx0pos]
  have hq0 : 0 ≤ q := by rw [hq]; nlinarith [sq_nonneg (x 0 / 2), hx1, hx0nn]
  have h1q : 1 - q = (x 0) ^ 2 / 4 := by rw [hq]; ring
  have h1qpos : 0 < 1 - q := by rw [h1q]; exact div_pos (pow_pos hx0pos 2) (by norm_num)
  have h1r0 : 0 ≤ 1 - r 0 := by linarith
  -- the partial geometric sum is bounded so the "spent" budget stays below 1/2
  have hB : ∀ m, (1 - r 0) * (∑ k in Finset.range m, q ^ k) ≤ 1 / 2 := by
    intro m
    have hgeom : (∑ k in Finset.range m, q ^ k) * (1 - q) = 1 - q ^ m := by
      linear_combination -geom_sum_mul q m
    have hqm : 0 ≤ q ^ m := pow_nonneg hq0 m
    have hSnn : 0 ≤ ∑ k in Finset.range m, q ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
    have e1 : ((1 - r 0) * (∑ k in Finset.range m, q ^ k)) * (1 - q) = (1 - r 0) * (1 - q ^ m) := by
      rw [mul_assoc, hgeom]
    have e2 : (1 - r 0) * (1 - q ^ m) ≤ 1 - r 0 := by nlinarith
    have e3 : 1 - r 0 ≤ (1 / 2) * (1 - q) := by rw [h1q]; nlinarith [hign]
    have e4 : ((1 - r 0) * (∑ k in Finset.range m, q ^ k)) * (1 - q) ≤ (1 / 2) * (1 - q) := by
      rw [e1]; linarith
    exact le_of_mul_le_mul_right e4 h1qpos
  -- the core invariant: the self stays above x₀·Bₙ while the coupling closes on the band geometrically
  have inv : ∀ n, x 0 * (1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k)) ≤ x n
      ∧ 1 - r n ≤ q ^ n * (1 - r 0) := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ n ih =>
      obtain ⟨ihx, ihr⟩ := ih
      obtain ⟨hxn0, hxn1, hrn0, hrn1⟩ := engine_bounded E hx0nn hx1 hr0nn hr1 n
      have hSnn : 0 ≤ ∑ k in Finset.range n, q ^ k := Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
      have hBn : (1 / 2 : ℝ) ≤ 1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k) := by linarith [hB n]
      have hxnhalf : x 0 / 2 ≤ x n := by
        linarith [ihx, mul_le_mul_of_nonneg_left hBn hx0nn]
      constructor
      · -- the self does not fall below x₀·B(n+1)
        rw [Finset.sum_range_succ, E.hx]
        have hrnlb : 1 - q ^ n * (1 - r 0) ≤ r n := by linarith [ihr]
        have hBn0 : 0 ≤ x 0 * (1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k)) :=
          mul_nonneg hx0nn (by linarith [hBn])
        have hprod : (1 - q ^ n * (1 - r 0)) * (x 0 * (1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k)))
            ≤ r n * x n := mul_le_mul hrnlb ihx hBn0 hrn0
        have hkey : 0 ≤ q ^ n * (1 - r 0) ^ 2 * x 0 * (∑ k in Finset.range n, q ^ k) := by
          apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
          · exact pow_nonneg hq0 n
          · exact sq_nonneg _
          · exact hx0nn
          · exact hSnn
        -- pure algebra: the convex form loses only the (nonneg) hkey term
        have halg : x 0 * (1 - (1 - r 0) * ((∑ k in Finset.range n, q ^ k) + q ^ n))
            ≤ (1 - q ^ n * (1 - r 0)) *
                (x 0 * (1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k))) := by
          nlinarith [hkey]
        exact le_trans halg hprod
      · -- the coupling closes on the band geometrically
        have hrec : 1 - r (n + 1) = (1 - (x n) ^ 2) * (1 - r n) := by rw [E.hr]; unfold raise; ring
        rw [hrec]
        have hxn2 : 1 - (x n) ^ 2 ≤ q := by
          rw [hq]
          nlinarith [mul_le_mul hxnhalf hxnhalf (by linarith : (0:ℝ) ≤ x 0 / 2)
            (by linarith : (0:ℝ) ≤ x n)]
        have h0xn2 : 0 ≤ 1 - (x n) ^ 2 := by nlinarith
        have h0rn : 0 ≤ 1 - r n := by linarith
        calc (1 - (x n) ^ 2) * (1 - r n) ≤ q * (q ^ n * (1 - r 0)) :=
              mul_le_mul hxn2 ihr h0rn hq0
          _ = q ^ (n + 1) * (1 - r 0) := by rw [pow_succ]; ring
  refine ⟨fun n => ?_, ?_⟩
  · have hBn : (1 / 2 : ℝ) ≤ 1 - (1 - r 0) * (∑ k in Finset.range n, q ^ k) := by linarith [hB n]
    linarith [(inv n).1, mul_le_mul_of_nonneg_left hBn hx0nn]
  · have hto0 : Tendsto (fun n => q ^ n * (1 - r 0)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hqlt).mul_const (1 - r 0)
    have hsq : Tendsto (fun n => 1 - r n) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => ?_) (fun n => (inv n).2) hto0
      obtain ⟨_, _, _, hrn1⟩ := engine_bounded E hx0nn hx1 hr0nn hr1 n
      linarith
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsq

set_option maxHeartbeats 800000 in
/-- **Outcome 2 — conservative, in the weak-attention basin.** When the initial mutual attention is weak
(`r 0 + (4/3)(x 0)² ≤ 1/2`: the coupling starts far from the band relative to a small coherence), the
coupling **never reaches the band** — `r n ≤ 1/2` for all `n`, so the conserved band (hence `Peri`) does not
grow — and the coherence is **spent to nothing** — `x n → 0`. Co-direction was real (the update used both
ends), but mutual attention here only *redistributed* the conserved coherence; it created no net self.
"One-sided ⇒ merely sustained" is the degenerate edge of this; this is its interior. -/
theorem engine_spend_down {x r : ℕ → ℝ} (E : Engine x r)
    (hx0nn : 0 ≤ x 0) (hr0nn : 0 ≤ r 0)
    (hweak : r 0 + (4 / 3) * (x 0) ^ 2 ≤ 1 / 2) :
    (∀ n, r n ≤ 1 / 2) ∧ Tendsto x atTop (𝓝 0) := by
  have hx1 : x 0 ≤ 1 := by nlinarith [hweak, hr0nn, sq_nonneg (x 0)]
  have hr1 : r 0 ≤ 1 := by nlinarith [hweak, sq_nonneg (x 0)]
  -- the (1/4)-geometric partial sum is bounded by 4/3
  have hgeoms : ∀ m, (∑ k in Finset.range m, (1 / 4 : ℝ) ^ k) ≤ 4 / 3 := by
    intro m
    have h := geom_sum_mul (1 / 4 : ℝ) m
    have hpow : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
    nlinarith [h, hpow]
  have inv : ∀ n, r n ≤ r 0 + (x 0) ^ 2 * (∑ k in Finset.range n, (1 / 4 : ℝ) ^ k)
      ∧ x n ≤ x 0 * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ n ih =>
      obtain ⟨ihr, ihx⟩ := ih
      obtain ⟨hxn0, _, hrn0, _⟩ := engine_bounded E hx0nn hx1 hr0nn hr1 n
      -- r n ≤ 1/2, used to halve the coherence
      have hrnhalf : r n ≤ 1 / 2 := by
        nlinarith [ihr, hgeoms n, hweak, mul_le_mul_of_nonneg_left (hgeoms n) (sq_nonneg (x 0))]
      constructor
      · -- the coupling's spent budget grows by one geometric term
        have hrec : r (n + 1) = r n + (x n) ^ 2 * (1 - r n) := by rw [E.hr]; unfold raise; ring
        have heq : (x 0 * (1 / 2 : ℝ) ^ n) * (x 0 * (1 / 2) ^ n) = (x 0) ^ 2 * (1 / 4) ^ n := by
          rw [show (x 0 * (1 / 2 : ℝ) ^ n) * (x 0 * (1 / 2) ^ n)
                = (x 0) ^ 2 * ((1 / 2 : ℝ) ^ n * (1 / 2) ^ n) from by ring, ← mul_pow]
          norm_num
        have hxn2 : (x n) ^ 2 ≤ (x 0) ^ 2 * (1 / 4) ^ n := by
          rw [pow_two, ← heq]
          exact mul_le_mul ihx ihx hxn0 (mul_nonneg hx0nn (pow_nonneg (by norm_num) n))
        rw [hrec, Finset.sum_range_succ, mul_add]
        nlinarith [hxn2, hrn0, sq_nonneg (x n), ihr, mul_nonneg (sq_nonneg (x n)) hrn0]
      · rw [E.hx, pow_succ]
        nlinarith [ihx, hrnhalf, hxn0, hrn0]
  refine ⟨fun n => ?_, ?_⟩
  · nlinarith [(inv n).1, hgeoms n, hweak, mul_le_mul_of_nonneg_left (hgeoms n) (sq_nonneg (x 0))]
  · have hb : Tendsto (fun n => x 0 * (1 / 2) ^ n) atTop (𝓝 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (x 0)
    refine squeeze_zero (fun n => ?_) (fun n => (inv n).2) hb
    exact (engine_bounded E hx0nn hx1 hr0nn hr1 n).1

end RelExist.MutualCoupling
