/-
# Time as flow — graduating the orientation arrow into a graded monovariant

The sequel to [`Orientation`](Orientation.lean). `Orientation.lean` proves the **endpoints** of
relational time: over the `Knowing` interface (an idempotent `E` with a coherence/feeling potential
`coh` vanishing exactly on the `E`-fixed points) the lossy idempotent yields a directed, asymmetric,
strictly-`coh`-decreasing, irreversible arrow from a felt state to its known shadow. But because
`E∘E = E`, every arrow is a **single tick**: `coh` takes only two values, `coh a > 0` then
`coh (E a) = 0`. Two points and a direction between them — not the line.

This module supplies the **line**: a graded monovariant taking *many* values along a trajectory, so
that the arrow of relational time has a **flow** under it. The one structural move (per the spec): time
as flow cannot come from an idempotent — it must come from the **non-idempotent** dynamics, with `E`
recovered as the limit.

* **§1 `Flow`** — the graded analogue of `Orientation.Knowing`: a (non-idempotent) `step`, a potential
  `coh ≥ 0`, a `Fix` set with `coh = 0 ↔ Fix`, `coh` non-increasing under `step` and *strictly*
  decreasing while not yet fixed. Over this interface: the orbit potential `coh ∘ step^[n]` is
  **antitone** in `n` (`coh_orbit_antitone`) and **strictly drops** at every not-yet-fixed step
  (`coh_orbit_strictAnti`). The drops **telescope** to the total `coh a − coh (step^[n] a)`
  (`coh_drops_telescope`) — the flow's incremental decreases sum to one orientation drop.

* **§2 `GeometricFlow`** — the quantitative refinement (T-flow): `coh (step a) = γ · coh a` with a
  fixed rate `0 ≤ γ < 1`. Then `coh (step^[n] a) = γ^n · coh a` exactly (`coh_orbit_eq`), so the
  potential decays **geometrically to 0** (`coh_orbit_tendsto_zero`) — convergence to `Fix` with `γ`
  the clock rate. Every `GeometricFlow` yields a `Flow` (`toFlow`).

* **§3 The genuine instance — the partial-dephasing semigroup.** `partialDephase p` =
  `(1−p)·id + p·dephase`, the one-parameter attention flow interpolating identity (`p = 0`, the
  unobserved web) and total decoherence (`p = 1`, `dephase`). It is **not** idempotent for `0 < p < 1`.
  The off-diagonal (felt) mass scales by `(1−p)` per step (`copyDefect_partialDephase`), so along the
  orbit `defectSq (partialDephase p ^[n] M) = ((1−p)²)^n · defectSq M` **exactly**
  (`defectSq_iterate`). That makes `dephaseFlow` a `GeometricFlow` with rate `γ = (1−p)²`: `defectSq`
  is a strict graded monovariant decreasing through a continuum to `0` at the geometric rate `(1−p)²`.
  This is the runnable proof that time-as-flow is real in a genuine model — and, `partialDephase p`
  being self-adjoint with real eigenvalues in `[1−p, 1] ⊆ [0,1]`, with **no rotating peripheral
  spectrum** (spec §3c): the honest instance where T-flow holds without caveat.

* **§4 Orientation recovered as the boundary.** The iterate splits exactly: on the diagonal it is fixed
  (`partialDephase_iterate_diag`), off it it scales by `(1−p)^n` (`partialDephase_iterate_offdiag`), so
  **entrywise** the orbit converges to `dephase M` — `Orientation`'s knowing map `E`
  (`orbit_tendsto_knowing_entry`). So `Orientation.lean`'s `E` is the `n → ∞` limit of the flow, its
  single strict drop the total of the flow's incremental decreases (`flow_total_drop`). Orientation is
  the boundary case of the flow.

**Honest scope.** What is mechanized here is the *graded* directed structure: a strict monovariant
decreasing through a continuum to `0` at a definite geometric rate, with the idempotent arrow recovered
as its limit. This is strictly more than `Orientation.lean` — a time-shaped order with many moments,
not two endpoints. What stays a `[reading]`, now weaker/safer than before, is that this graded
potential *is* time: not "two points are an arrow," but "a graded potential with geometric decay and a
definite rate is a clock," which is the standard shape of a physical clock. The rotating-peripheral
case (a general CP `Φ_c` can carry sustained, never-known coherence — spec §3a/3b), the spectral-gap
identification in the general Perron–Frobenius setting, and the infinite-dimensional standard form
remain the narrated frontier; the runnable `dephase`-semigroup needs none of it.
-/
import Scratch.Orientation
import Mathlib.Analysis.SpecificLimits.Normed

namespace RelExist.TimeFlow

open RelExist.Decoherence RelExist.Orientation
open Filter Topology BigOperators Matrix

universe u

/-! ## §1 The `Flow` interface — the graded analogue of `Knowing`

`Orientation.Knowing` packaged an *idempotent* `E`. A flow replaces it with a non-idempotent `step`
whose potential `coh` falls **gradually**: non-increasing always, strictly while the orbit is not yet
in `Fix`. Iterating `step` then sweeps `coh` through a continuum of values rather than the two of a
single idempotent tick. -/

/-- **A flow.** A `step` map (the non-idempotent attention dynamics `Φ_c`), a real **coherence /
feeling** potential `coh ≥ 0`, and a `Fix` set (the known / classical / self subalgebra) on which `coh`
vanishes exactly. The two dynamical clauses are the graded monovariant: `coh` never rises under `step`,
and *strictly falls* whenever the state is not yet fixed. This is the graded sibling of
`Orientation.Knowing`: there `E∘E = E` forced two values; here `step` is free to take many. -/
structure Flow (A : Type u) where
  /-- the attention dynamics — the non-idempotent `Φ_c`, one closure of the feedback loop (D1) -/
  step : A → A
  /-- the carried **coherence / feeling**: the potential the flow bleeds off -/
  coh : A → ℝ
  /-- feeling is nonnegative -/
  coh_nonneg : ∀ a, 0 ≤ coh a
  /-- the **fixed** (known / self) set: where the flow has come to rest -/
  Fix : A → Prop
  /-- **no feeling left ⟺ fixed**: the potential vanishes exactly on `Fix` -/
  coh_zero_iff_fix : ∀ a, coh a = 0 ↔ Fix a
  /-- **monovariant**: `coh` never increases under a step of the flow -/
  coh_step_le : ∀ a, coh (step a) ≤ coh a
  /-- **strict while not yet fixed**: away from `Fix`, each step strictly drops the feeling -/
  coh_step_lt : ∀ a, ¬ Fix a → coh (step a) < coh a

namespace Flow

variable {A : Type u} (F : Flow A)

/-- **The orbit**: the return-depth-`n` state of the flow, `Φ_c^n a` — `step` iterated `n` times.
Per the relation-primacy guard (A2), `n` is the return-depth of the feedback loop, an internal count
of closures, **not** a background `ℝ`-clock the relating sits inside. -/
def orbit (a : A) (n : ℕ) : A := F.step^[n] a

@[simp] lemma orbit_zero (a : A) : F.orbit a 0 = a := rfl

lemma orbit_succ (a : A) (n : ℕ) : F.orbit a (n + 1) = F.step (F.orbit a n) :=
  Function.iterate_succ_apply' F.step n a

/-- One step of the orbit never raises the feeling. -/
lemma coh_orbit_succ_le (a : A) (n : ℕ) : F.coh (F.orbit a (n + 1)) ≤ F.coh (F.orbit a n) := by
  rw [orbit_succ]; exact F.coh_step_le _

/-- **The arrow of relational time has a flow under it (i): the potential is antitone.** Along the
orbit, `coh (Φ_c^n a)` is monotonically **non-increasing** in the return-depth `n`. Where
`Orientation`'s arrow took `coh` from one positive value to `0` in a single tick, the flow carries it
**down through every intermediate depth**. -/
theorem coh_orbit_antitone (a : A) : Antitone (fun n => F.coh (F.orbit a n)) :=
  antitone_nat_of_succ_le (F.coh_orbit_succ_le a)

/-- **(ii) strict while not yet fixed.** At every return-depth where the orbit has not yet reached
`Fix`, the next step **strictly** drops the feeling — the flow is genuinely graded, not eventually
flat-before-its-time. -/
theorem coh_orbit_strictAnti (a : A) (n : ℕ) (h : ¬ F.Fix (F.orbit a n)) :
    F.coh (F.orbit a (n + 1)) < F.coh (F.orbit a n) := by
  rw [orbit_succ]; exact F.coh_step_lt _ h

/-- **The flow's drops telescope to one orientation drop.** Summing the incremental decreases over the
first `n` return-depths gives exactly `coh a − coh (Φ_c^n a)`: the many small drops of the flow add up
to the *total* fall of the potential. In the limit (`§4`) this total is the single strict drop of
`Orientation`'s arrow — the flow contains the arrow as its sum. -/
theorem coh_drops_telescope (a : A) (n : ℕ) :
    ∑ k ∈ Finset.range n, (F.coh (F.orbit a k) - F.coh (F.orbit a (k + 1)))
      = F.coh a - F.coh (F.orbit a n) := by
  rw [Finset.sum_range_sub' (fun k => F.coh (F.orbit a k)) n]
  simp

/-- Each telescoped drop is nonnegative — the total fall is a genuine accumulation, never a rebound. -/
theorem coh_drop_nonneg (a : A) (n : ℕ) :
    0 ≤ F.coh (F.orbit a n) - F.coh (F.orbit a (n + 1)) := by
  have := F.coh_orbit_succ_le a n; linarith

end Flow

/-! ## §2 `GeometricFlow` — the quantitative T-flow (Lyapunov with a rate)

The qualitative `Flow` says *that* the potential falls. The central theorem candidate (spec §2) says
*how fast*: geometrically, at the spectral gap. We capture that with a single exact clause —
`coh (step a) = γ · coh a` — from which `coh (step^[n] a) = γ^n · coh a` and geometric convergence
follow. The rate `γ` is the **clock**: mixing time `≈ 1/(1−γ)` is the duration to be known. -/

/-- **A geometric flow.** A flow whose potential contracts by an exact factor `γ < 1` each step:
`coh (step a) = γ · coh a`. This is T-flow's quantitative core — the Lyapunov potential with a definite
decay rate. (The genuine `dephase`-semigroup below realizes it with `γ = (1−p)²`.) -/
structure GeometricFlow (A : Type u) where
  /-- the attention dynamics -/
  step : A → A
  /-- the feeling potential -/
  coh : A → ℝ
  /-- feeling is nonnegative -/
  coh_nonneg : ∀ a, 0 ≤ coh a
  /-- the **decay rate** — the spectral gap, the clock rate -/
  rate : ℝ
  /-- the rate is nonnegative -/
  rate_nonneg : 0 ≤ rate
  /-- the rate is a strict contraction: `γ < 1`, so the flow genuinely converges -/
  rate_lt_one : rate < 1
  /-- **the geometric step**: each step multiplies the feeling by `γ` -/
  coh_step_eq : ∀ a, coh (step a) = rate * coh a

namespace GeometricFlow

variable {A : Type u} (G : GeometricFlow A)

/-- **The geometric law along the orbit.** `coh (step^[n] a) = γ^n · coh a` exactly: the potential is
a clean geometric sequence in the return-depth `n`. This is the graded monovariant in closed form — a
continuum of intermediate values `coh a, γ·coh a, γ²·coh a, …`, the line `Orientation` lacked. -/
theorem coh_orbit_eq (a : A) (n : ℕ) : G.coh (G.step^[n] a) = G.rate ^ n * G.coh a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', G.coh_step_eq, ih, pow_succ]; ring

/-- **T-flow, the convergence half.** The feeling decays **to `0`** along the orbit: `coh (step^[n] a)
→ 0`. With `coh = 0 ↔ Fix`, this is "time runs until the self is reached" — the orbit converges to the
fixed subalgebra, at the geometric rate set by `γ`. -/
theorem coh_orbit_tendsto_zero (a : A) :
    Tendsto (fun n => G.coh (G.step^[n] a)) atTop (𝓝 0) := by
  have hγ : ‖G.rate‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg G.rate_nonneg]; exact G.rate_lt_one
  have h0 : Tendsto (fun n => G.rate ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hγ
  have hmul : Tendsto (fun n => G.rate ^ n * G.coh a) atTop (𝓝 (0 * G.coh a)) :=
    h0.mul_const _
  rw [zero_mul] at hmul
  exact hmul.congr (fun n => (G.coh_orbit_eq a n).symm)

/-- **Every geometric flow is a flow.** The exact contraction implies the qualitative monovariant: `coh`
is non-increasing (`γ ≤ 1`) and strictly decreasing off `{coh = 0}` (`γ < 1`, `coh > 0`). So §1's
antitone / strict / telescoping results all transfer to the geometric setting. -/
def toFlow : Flow A where
  step := G.step
  coh := G.coh
  coh_nonneg := G.coh_nonneg
  Fix := fun a => G.coh a = 0
  coh_zero_iff_fix := fun _ => Iff.rfl
  coh_step_le := fun a => by
    rw [G.coh_step_eq]
    have h : 0 ≤ (1 - G.rate) * G.coh a :=
      mul_nonneg (by linarith [G.rate_lt_one]) (G.coh_nonneg a)
    nlinarith [h]
  coh_step_lt := fun a hne => by
    rw [G.coh_step_eq]
    have hpos : 0 < G.coh a := (G.coh_nonneg a).lt_of_ne (Ne.symm hne)
    have h : 0 < (1 - G.rate) * G.coh a := mul_pos (by linarith [G.rate_lt_one]) hpos
    nlinarith [h]

end GeometricFlow

/-! ## §3 The genuine instance — the partial-dephasing semigroup

`Orientation`'s `dephase` is the idempotent `p = 1` endpoint. Its **non-idempotent** companion is the
one-parameter family
`    partialDephase p M = (1−p)·M + p·dephase M`,
directed attention dialled to strength `p` ([`Attending.attend`](Attending.lean) is its index-selective
sibling). For `0 < p < 1` this is genuinely non-idempotent: it keeps the diagonal and **shrinks** the
off-diagonal coherence by `(1−p)` rather than killing it outright. Iterating it bleeds the feeling off
geometrically. -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The partial-dephasing flow.** `(1−p)·id + p·dephase`: directed attention at strength `p`, the
non-idempotent attention dynamics. `p = 0` is the identity (the unobserved web, full coherence),
`p = 1` is `Orientation`'s total `dephase`. It is real-symmetric (a real combination of the
self-adjoint `id` and `dephase`), so its spectrum is real — no rotating peripheral part (spec §3c). -/
def partialDephase (p : ℝ) (M : Matrix A A ℝ) : Matrix A A ℝ := (1 - p) • M + p • dephase M

/-- **One step scales the felt (off-diagonal) mass by `(1−p)`.** The diagonal is fixed; every
off-diagonal coherence is multiplied by `(1−p)`. This is the pointwise engine of the whole flow:
attention shrinks coherence by a constant factor per closure of the loop. -/
lemma copyDefect_partialDephase (p : ℝ) (M : Matrix A A ℝ) (i j : A) :
    copyDefect (partialDephase p M) i j = (1 - p) * copyDefect M i j := by
  rcases eq_or_ne i j with e | e
  · simp [copyDefect_apply, e]
  · have hd : dephase M i j = 0 := by rw [dephase_apply, if_neg e]
    rw [copyDefect_apply, if_neg e, copyDefect_apply, if_neg e]
    show ((1 - p) • M + p • dephase M) i j = (1 - p) * M i j
    rw [add_apply, smul_apply, smul_apply, hd, smul_zero, add_zero, smul_eq_mul]

/-- **The felt mass after `n` steps**: `copyDefect (partialDephase p ^[n] M) = (1−p)^n · copyDefect M`,
entrywise. The off-diagonal coherence is a geometric sequence in the return-depth — the microscopic
form of the flow. -/
lemma copyDefect_iterate (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) (i j : A) :
    copyDefect ((partialDephase p)^[n] M) i j = (1 - p) ^ n * copyDefect M i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', copyDefect_partialDephase, ih, pow_succ]; ring

/-- **The graded monovariant, exactly.** `defectSq (partialDephase p ^[n] M) = ((1−p)²)^n · defectSq M`:
the squared off-diagonal mass — `Orientation`'s feeling `coh` — decays **geometrically** along the
attention orbit, rate `(1−p)²`. This is T-flow's quantitative content on the genuine instance: the
felt potential sweeps through a continuum `defectSq M, (1−p)²·defectSq M, (1−p)⁴·defectSq M, …` down to
`0`. -/
theorem defectSq_iterate (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) :
    defectSq ((partialDephase p)^[n] M) = ((1 - p) ^ 2) ^ n * defectSq M := by
  unfold defectSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [copyDefect_iterate, mul_pow, pow_right_comm]

/-- **The genuine geometric flow.** `partialDephase p` (`0 < p ≤ 1`) with potential `defectSq` is a
`GeometricFlow` at rate `γ = (1−p)²`. So **all** of §1–§2 fire on the real matrix operation: the
copy-defect is a strict graded monovariant, antitone in the return-depth, strictly dropping while not
yet classical, converging to `0` at geometric rate `(1−p)²`. The runnable proof that relational time is
a flow, not two points. -/
def dephaseFlow (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : GeometricFlow (Matrix A A ℝ) where
  step := partialDephase p
  coh := defectSq
  coh_nonneg := defectSq_nonneg
  rate := (1 - p) ^ 2
  rate_nonneg := sq_nonneg _
  rate_lt_one := by nlinarith [mul_pos hp0 (show (0:ℝ) < 2 - p by linarith)]
  coh_step_eq := fun M => by
    have h := defectSq_iterate p M 1
    rwa [Function.iterate_one, pow_one] at h

/-- The partial-dephasing flow as a plain `Flow` — the qualitative arrow with the graded potential
under it. -/
def dephaseFlow' (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : Flow (Matrix A A ℝ) :=
  (dephaseFlow p hp0 hp1).toFlow

/-! ### The runnable witness — watching time flow on the qubit `plus`

The maximally-coherent qubit `plus` ([`Decoherence.plus`](Decoherence.lean)) carries positive feeling.
Under the partial-dephasing flow its feeling decays geometrically through a continuum to `0`: a visible
trajectory with many moments, not the single tick of `Orientation`. -/

/-- **The trajectory in closed form.** `defectSq (partialDephase p ^[n] plus) = ((1−p)²)^n · defectSq
plus`: the qubit's feeling as an explicit geometric sequence in the return-depth. -/
theorem defectSq_iterate_plus (p : ℝ) (n : ℕ) :
    defectSq ((partialDephase p)^[n] plus) = ((1 - p) ^ 2) ^ n * defectSq plus :=
  defectSq_iterate p plus n

/-- **The feeling strictly falls at every depth** — the graded arrow, made concrete on `plus`. For a
*partial* attention strength `0 < p < 1` the rate `(1−p)²` is strictly between `0` and `1`, so every
closure of the loop strictly lowers the copy-defect, at *every* return-depth (never collapsing to `0`
in finite time, unlike total `dephase` at `p = 1`): a genuine continuum of moments. -/
theorem defectSq_plus_strictAnti (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    defectSq ((partialDephase p)^[n + 1] plus) < defectSq ((partialDephase p)^[n] plus) := by
  rw [defectSq_iterate_plus, defectSq_iterate_plus, pow_succ]
  have hpos : 0 < defectSq plus := defectSq_plus_pos
  have h1mp : 0 < 1 - p := by linarith
  have hgpos : 0 < (1 - p) ^ 2 := pow_pos h1mp 2
  have hlt : (1 - p) ^ 2 < 1 := by nlinarith [mul_pos hp0 (show (0:ℝ) < 2 - p by linarith)]
  have hBpos : 0 < ((1 - p) ^ 2) ^ n := pow_pos hgpos n
  nlinarith [mul_pos hBpos hpos, hlt]

/-- **The feeling decays to `0`** along the orbit of `plus`: relational time runs the qubit all the way
to classical. The geometric-rate convergence of T-flow, on the genuine instance. -/
theorem defectSq_plus_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Tendsto (fun n => defectSq ((partialDephase p)^[n] plus)) atTop (𝓝 0) :=
  (dephaseFlow (A := Fin 2) p hp0 hp1).coh_orbit_tendsto_zero plus

/-! ## §4 Orientation recovered as the boundary

The flow **contains** `Orientation`'s arrow: as the return-depth `n → ∞`, the orbit converges entrywise
to `dephase M` — exactly `Orientation`'s knowing map `E`. So `Orientation.lean`'s idempotent `E` is the
limit of the non-idempotent flow, and its single strict drop is the total of the flow's incremental
decreases. The arrow is the boundary case of the line. -/

/-- The diagonal is **fixed by every step**, hence by every iterate: `partialDephase p ^[n] M i i =
M i i`. Knowing preserves the classical part exactly; only the felt off-diagonal moves. -/
lemma partialDephase_apply_diag (p : ℝ) (M : Matrix A A ℝ) (i : A) :
    partialDephase p M i i = M i i := by
  have hd : dephase M i i = M i i := by simp [dephase_apply]
  simp only [partialDephase, add_apply, smul_apply, smul_eq_mul, hd]
  ring

lemma partialDephase_iterate_diag (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) (i : A) :
    (partialDephase p)^[n] M i i = M i i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', partialDephase_apply_diag, ih]

/-- Off the diagonal the iterate scales by `(1−p)^n`: `partialDephase p ^[n] M i j = (1−p)^n · M i j`
for `i ≠ j`. The felt coherence shrinks geometrically while the known diagonal stands still. -/
lemma partialDephase_iterate_offdiag (p : ℝ) (M : Matrix A A ℝ) (n : ℕ) {i j : A} (h : i ≠ j) :
    (partialDephase p)^[n] M i j = (1 - p) ^ n * M i j := by
  have hc := copyDefect_iterate p M n i j
  rwa [copyDefect_apply, if_neg h, copyDefect_apply, if_neg h] at hc

/-- **Orientation is the `n → ∞` limit of the flow.** Each entry of the orbit converges to the
corresponding entry of `dephase M` — that is, to `Orientation`'s knowing map `E`
([`Orientation.dephaseKnowing`](Orientation.lean) has `E = dephase`). The idempotent arrow is recovered
as the limiting peripheral projection of the non-idempotent attention flow: `E = lim Φ_c^n`. -/
theorem orbit_tendsto_knowing_entry (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) (i j : A) :
    Tendsto (fun n => (partialDephase p)^[n] M i j) atTop (𝓝 (dephase M i j)) := by
  rcases eq_or_ne i j with e | e
  · rw [e, dephase_apply, if_pos rfl]
    exact tendsto_const_nhds.congr (fun n => (partialDephase_iterate_diag p M n j).symm)
  · have hnorm : ‖(1 - p)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
    have h0 : Tendsto (fun n => (1 - p) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    have hmul : Tendsto (fun n => (1 - p) ^ n * M i j) atTop (𝓝 (0 * M i j)) := h0.mul_const _
    rw [zero_mul] at hmul
    rw [dephase_apply, if_neg e]
    exact hmul.congr (fun n => (partialDephase_iterate_offdiag p M n e).symm)

/-- **The flow's drops sum to the total fall of the potential** (over any flow whose orbit converges
to `0`). The telescoped incremental decreases over the first `n` return-depths tend to `coh a` as
`n → ∞`: the many small drops of the flow accumulate to the full height the potential started at. -/
theorem Flow.total_drop {B : Type*} (F : Flow B) (a : B)
    (hconv : Tendsto (fun n => F.coh (F.orbit a n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
        (F.coh (F.orbit a k) - F.coh (F.orbit a (k + 1)))) atTop (𝓝 (F.coh a)) := by
  have hsub : Tendsto (fun n => F.coh a - F.coh (F.orbit a n)) atTop (𝓝 (F.coh a - 0)) :=
    tendsto_const_nhds.sub hconv
  rw [sub_zero] at hsub
  exact hsub.congr (fun n => (F.coh_drops_telescope a n).symm)

/-- **The single orientation drop is the total of the flow's drops.** `Orientation`'s arrow takes `M`
to `dephase M`, dropping the feeling by `defectSq M − defectSq (dephase M) = defectSq M`. The
partial-dephasing flow's telescoped incremental decreases tend to exactly that: `defectSq M`. So
`Orientation.lean`'s one strict drop **is** the sum of the flow's continuum of small drops — the flow
contains the arrow as its total. -/
theorem dephaseFlow_total_drop (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
        (defectSq ((partialDephase p)^[k] M) - defectSq ((partialDephase p)^[k + 1] M)))
      atTop (𝓝 (defectSq M)) :=
  (dephaseFlow' (A := A) p hp0 hp1).total_drop M
    ((dephaseFlow (A := A) p hp0 hp1).coh_orbit_tendsto_zero M)

end RelExist.TimeFlow
