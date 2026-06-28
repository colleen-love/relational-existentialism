/-
# From the arrow back to the knowing — the converse direction

The dual of [`TimeFlow`](TimeFlow.lean) / [`Orientation`](Orientation.lean). The forward chain proves
**`knowing ⟹ arrow`**: an idempotent conditional expectation `E` (`Orientation`) graduates into a
graded monovariant flow (`TimeFlow`) whose sign and target subalgebra are fixed by the seam
(`TimeArrow`, `SeamForcing`). Knowing is the input; the time-arrow is the derived output.

This module runs the implication **backwards** on the genuine instance:

> **Take an arrow as given and recover the knowing.** From a dynamics exhibiting the arrow-properties
> alone — a strict monovariant `V ≥ 0` that runs to a floor under a `step` — its limit **is** a
> knowing: an idempotent conditional expectation onto a subalgebra, with the monovariant equal to the
> off-diagonal mass that limit annihilates.

The structural move (spec §1): the forward direction *assumed* `E` and a potential and *derived* the
flow; the converse *assumes the flow's conclusions* (the interface `Arrow`) and *derives* `E` as the
orbit's limit. `Arrow` carries the same fields as `TimeFlow.Flow`; only the direction of inference
differs (`Flow : E ⊢ V`, `Arrow : V ⊢ E`). The *quantitative* hypotheses the general lift needs —
`step` a positive, unital contraction with trivial peripheral spectrum — are supplied **concretely**
by `partialDephase p` here (real-symmetric, spectrum in `[0,1]`, no rotating part); their abstract
form is the keystone [`MeanErgodic`](MeanErgodic.lean) (`[open]`, Conjecture R), gated out of this
build.

**Relation-primacy guard (A2).** As in `TimeFlow`, the orbit index `n` is the internal return-depth
of the feedback loop, not an external `ℝ`-time. The recovered `E` is the `n → ∞` limit *of the orbit*,
not a knower sitting in a background interval — the guard that forecloses reading it as a persistent
external subject (spec §6).

**Honest scope.** `[proved]` here: on the genuine instance the converse is a theorem —
`partialDephase p` is an `Arrow`, and its orbit converges entrywise to `dephase`, the knowing map `E`
of `Orientation.dephaseKnowing`, which is idempotent, is the seam-forced conditional expectation
`SeamForcing.knowSeam ∅`, and annihilates exactly the monovariant `defectSq` that defined the arrow.
The instance closes by **re-export**, not new proof. `[open]`: the general lift to every contractive
arrow with trivial peripheral spectrum (`MeanErgodic`, Conjecture R). `[reading]`, unchanged from the
forward direction: that the recovered `E` deserves the name *knowing* in the lived sense.
-/
import Scratch.TimeFlow
import Scratch.SeamForcing

namespace RelExist.KnowingFromArrow

open RelExist.Decoherence RelExist.Orientation RelExist.TimeFlow RelExist.SeamForcing
open Filter Topology BigOperators Matrix

universe u

/-! ## §1 The `Arrow` interface — the dual of `Flow`

`TimeFlow.Flow` packaged a `step`, a potential `coh`, and the monovariant clauses, and *derived* the
flow's order behaviour. `Arrow` carries the **same fields**; the difference is what we treat as given.
For the forward direction the potential is read off a known `E`; for the converse the potential is the
*datum* and the `E` is what its orbit must converge to. The order behaviour is shared — so we obtain it
by coercing to `Flow` and re-exporting, rather than re-proving. -/

/-- **An arrow.** A `step` `T`, a real monovariant `V ≥ 0`, and a `Fix` set on which `V` vanishes
exactly; `V` never rises under `T` and strictly falls while not yet fixed. Identical fields to
`TimeFlow.Flow` — the converse reads them as `V ⊢ E` rather than `E ⊢ V`. (The *quantitative*
contraction hypotheses on `T` — positive, unital, trivial peripheral spectrum — that the general lift
needs are properties of the concrete `step`; the genuine instance supplies them, the abstract lift is
`MeanErgodic`.) -/
structure Arrow (A : Type u) where
  /-- the dynamics whose limit we recover as a knowing -/
  step : A → A
  /-- the strict monovariant — the off-diagonal / felt mass the limit will annihilate -/
  V : A → ℝ
  /-- the monovariant is nonnegative -/
  V_nonneg : ∀ a, 0 ≤ V a
  /-- the **fixed** (known / self) set -/
  Fix : A → Prop
  /-- `V` vanishes exactly on `Fix` -/
  V_zero_iff_fix : ∀ a, V a = 0 ↔ Fix a
  /-- `V` never rises under a step -/
  V_step_le : ∀ a, V (step a) ≤ V a
  /-- `V` strictly falls while not yet fixed -/
  V_step_lt : ∀ a, ¬ Fix a → V (step a) < V a

namespace Arrow

variable {A : Type u} (R : Arrow A)

/-- **The orbit** — the return-depth-`n` state `T^n a`. As in `Flow`, `n` is the internal return-depth
of the feedback loop (A2 guard), not an external clock. -/
def orbit (a : A) (n : ℕ) : A := R.step^[n] a

/-- An `Arrow` *is* a `Flow` (same fields) — the coercion that lets every `Flow` order theorem fire on
the converse interface for free. -/
def toFlow : Flow A where
  step := R.step
  coh := R.V
  coh_nonneg := R.V_nonneg
  Fix := R.Fix
  coh_zero_iff_fix := R.V_zero_iff_fix
  coh_step_le := R.V_step_le
  coh_step_lt := R.V_step_lt

@[simp] lemma toFlow_orbit (a : A) (n : ℕ) : R.toFlow.orbit a n = R.orbit a n := rfl

/-- **The monovariant is antitone along the orbit** (re-export of `Flow.coh_orbit_antitone`). -/
theorem V_orbit_antitone (a : A) : Antitone (fun n => R.V (R.orbit a n)) :=
  R.toFlow.coh_orbit_antitone a

/-- **The monovariant strictly falls while not yet fixed** (re-export of `Flow.coh_orbit_strictAnti`). -/
theorem V_orbit_strictAnti (a : A) (n : ℕ) (h : ¬ R.Fix (R.orbit a n)) :
    R.V (R.orbit a (n + 1)) < R.V (R.orbit a n) :=
  R.toFlow.coh_orbit_strictAnti a n h

/-- **The drops telescope to the total fall** (re-export of `Flow.coh_drops_telescope`). -/
theorem V_drops_telescope (a : A) (n : ℕ) :
    ∑ k ∈ Finset.range n, (R.V (R.orbit a k) - R.V (R.orbit a (k + 1)))
      = R.V a - R.V (R.orbit a n) :=
  R.toFlow.coh_drops_telescope a n

end Arrow

/-- **A flow gives an arrow.** The forward interface, read backwards: any `TimeFlow.Flow` is an
`Arrow` over the same data. -/
def Arrow.ofFlow {A : Type u} (F : Flow A) : Arrow A where
  step := F.step
  V := F.coh
  V_nonneg := F.coh_nonneg
  Fix := F.Fix
  V_zero_iff_fix := F.coh_zero_iff_fix
  V_step_le := F.coh_step_le
  V_step_lt := F.coh_step_lt

/-! ## §2 The genuine instance — `partialDephase p` is an arrow whose limit is a knowing

`partialDephase p` (`0 < p ≤ 1`), with monovariant `defectSq`, is the `TimeFlow.dephaseFlow'` read as
an `Arrow`. Its orbit converges entrywise to `dephase` — the knowing map `E` of
`Orientation.dephaseKnowing` — and every conjunct of "the limit is a knowing" is an existing theorem.
The instance closes by re-export. -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The partial-dephasing arrow.** `partialDephase p` with monovariant `defectSq`, packaged as an
`Arrow` from `TimeFlow.dephaseFlow'`. -/
def dephaseArrow (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : Arrow (Matrix A A ℝ) :=
  Arrow.ofFlow (dephaseFlow' p hp0 hp1)

@[simp] lemma dephaseArrow_step (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) :
    (dephaseArrow p hp0 hp1).step M = partialDephase p M := rfl

@[simp] lemma dephaseArrow_orbit (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) (n : ℕ) :
    (dephaseArrow p hp0 hp1).orbit M n = (partialDephase p)^[n] M := rfl

@[simp] lemma dephaseArrow_V (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) :
    (dephaseArrow p hp0 hp1).V M = defectSq M := rfl

/-- **T-recover (i): the orbit converges, and its limit is the knowing map `E`.** Entrywise, the
arrow's orbit `(partialDephase p)^[n] M` converges to `(dephaseKnowing A).E M = dephase M`. So the
recovered `E` is literally `Orientation`'s knowing map — *the arrow's limit is a knowing*. Re-export of
`TimeFlow.orbit_tendsto_knowing_entry`. -/
theorem arrow_limit_is_knowing (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) (i j : A) :
    Tendsto (fun n => (dephaseArrow p hp0 hp1).orbit M n i j) atTop
      (𝓝 ((dephaseKnowing A).E M i j)) := by
  simpa using orbit_tendsto_knowing_entry p hp0 hp1 M i j

/-- **T-recover (ii): the limit is idempotent** — `E ∘ E = E`. The recovered limit is a genuine
projection. Re-export of `Decoherence.dephase_idem`. -/
theorem limit_idempotent (M : Matrix A A ℝ) :
    (dephaseKnowing A).E ((dephaseKnowing A).E M) = (dephaseKnowing A).E M :=
  (dephaseKnowing A).idem M

/-- **T-recover (iii): the limit is the seam-forced conditional expectation.** The recovered `E` is
exactly `SeamForcing.knowSeam ∅` — the maximal available knowing at the empty seam, an idempotent
conditional expectation onto the (diagonal) classical subalgebra. So the arrow's limit is a
*conditional expectation onto a subalgebra*, in the precise sense `SeamForcing` certifies at `J = ∅`.
Re-export of `SeamForcing.knowSeam_empty`. -/
theorem limit_is_seam_CE (M : Matrix A A ℝ) :
    knowSeam (∅ : Finset A) M = (dephaseKnowing A).E M :=
  knowSeam_empty M

/-- **T-recover (iv): the limit annihilates the monovariant.** The recovered `E` sends the arrow's
potential `V = defectSq` to `0`: `defectSq (E M) = 0`. The off-diagonal mass that *defined* the arrow
is exactly the mass its limit kills — the converse of "knowing decoheres." Re-export of
`Orientation.Knowing.coh_image`. -/
theorem limit_annihilates_potential (M : Matrix A A ℝ) :
    (dephaseKnowing A).coh ((dephaseKnowing A).E M) = 0 :=
  (dephaseKnowing A).coh_image M

/-- **The monovariant's geometric law**, recording that the arrow is genuinely *dissipative*: the
potential along the orbit is `((1−p)²)^n · defectSq M`, with no conserved (rotating) remainder. The
veto of spec §3 is vacuous on this real-symmetric instance. Re-export of `TimeFlow.defectSq_iterate`. -/
theorem potential_geometric (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) (n : ℕ) :
    (dephaseArrow p hp0 hp1).V ((dephaseArrow p hp0 hp1).orbit M n)
      = ((1 - p) ^ 2) ^ n * defectSq M := by
  simpa using defectSq_iterate p M n

/-- **The potential runs to the floor.** Along the arrow's orbit the monovariant tends to `0` — the
arrow is dissipative, so its limit is reached and there is a knowing to recover. Re-export of
`GeometricFlow.coh_orbit_tendsto_zero` via the instance. -/
theorem potential_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (M : Matrix A A ℝ) :
    Tendsto (fun n => (dephaseArrow p hp0 hp1).V ((dephaseArrow p hp0 hp1).orbit M n)) atTop (𝓝 0) := by
  simpa using (dephaseFlow (A := A) p hp0 hp1).coh_orbit_tendsto_zero M

end RelExist.KnowingFromArrow
