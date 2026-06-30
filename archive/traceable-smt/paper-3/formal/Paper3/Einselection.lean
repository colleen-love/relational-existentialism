/-
# Handoff XVI — the einselection principle, and whether it defines presence

Two open questions, resolved here as one. The **einselection residue** (does the framework *force* the
decoherence basis B1 to be the modular eigenbasis, or is it assumed?) and the **presence definition** (is
there a quantity with `presence = knowing + energy` as a *theorem*, not a name?) are the same question — the
knowing/energy split is only well-defined when the two bases coincide. Building on `Paper3.OneGenerator` (the
equilibrium one generator) and the band machinery (`BandFromAxioms`). Finite-dimensional; paper one untouched.

## What is built

* **Part A (`§1`) — the alignment is *forced* by stationarity.** Spec XV *assumed* `B1 = eigenbasis(ρ)`.
  Here it is **derived**: the modular state `ρ` (whose flow is the clock) must be the **rest-state** of the
  dissipator, `𝒟(ρ) = 0`. Under the live/nondegenerate baseline that forces `ρ` **diagonal in B1**
  (`stationary_eq_diagonal`), and for Hermitian `ρ` into exactly the `diagonal (RCLike.ofReal ∘ d)` shape
  spec XV needed (`stationary_eq_diagonal_real`). *The clock-state is the rest-state.* Boundaries named:
  **degenerate `ρ`** (eigenbasis under-determined in a degenerate block — diagonality, hence the commutation,
  still holds) and **out-of-equilibrium** (no single stationary `ρ` — the Connes–Rovelli regime).

* **Part B (`§2`) — the einselected structure is the conserved band `Peri = fixed ⊕ rotating`.** The modes
  robust under `𝓛` (`genReal = 0`) are exactly the conserved band (`genReal_zero_iff_conservedEdge`), which
  splits *disjointly* into the **fixed** sub-band (the diagonal record — knowing) and the **rotating**
  sub-band (the modular phase — energy): `conservedEdge_iff_fixed_or_rotating`, `not_fixed_and_rotating`.

* **Part C (`§3`) — presence, defined from the einselected band and *tested*.** `presence² :=` the HS weight
  on the conserved band (`presenceSq`), `knowing²`/`energy²` its fixed/rotating halves. The three tests:
  1. **Conserved? Yes — exactly.** Both faces of `𝓛` are modulus-one Schur multipliers on the conserved band
     (the clock everywhere, `norm_modularMul`; the dissipator on `‖μ‖ = 1` edges, `norm_dissipatorMul`), so
     `presence_conserved`/`presence_conserved_norm` are *ℂ-exact*, not a floor.
  2. **Decomposes as knowing + energy? Yes — Pythagorean, exactly.** `presence² = knowing² + energy²`
     (`pythagorean`, `pythagorean_norm`): the sub-bands are coordinate-orthogonal in the HS inner product, and
     the orthogonality **survives the modular rotation** (it is a Schur multiplier in the same basis — checked,
     not assumed).
  3. **The arrow as relocation? No — refuted.** `knowing` is *exactly constant* (`knowing_conserved`) while
     the transient (attendable, `‖μ‖ < 1`) weight tends to **zero** (`transient_tendsto_zero`): the decohered
     coherence is **lost, not relocated** into the record (`arrow_is_loss_not_relocation`). With
     `‖M‖²_HS = presence² + transient²` (`full_split`), the eroded transient does not reappear in knowing.

## Honest outcome (Outcome 1 for the definition; a real negative for relocation)

Presence **is** definable from the einselection principle — derived (A), identified with the conserved band
(B), invariant and split as knowing ⊕ energy (C1, C2). *Paper three's foundational definition exists, earned,
not posited.* But the *relocation/conservation-law* reading (knowing grows as coherence decoheres, at constant
presence) is **false for the minimal one generator** (C3): pure phase-damping erases the transient rather than
moving it into the record. Paper three's conservation law is therefore **not** of the relocation kind here — it
needs a genuine population-transferring dissipator beyond pure dephasing. The negative is precisely located:
exactly what is still missing is named.

## Conditions / open

`[proved, at equilibrium]` rests on the same named readings as spec XV: KMS-equilibrium and (now *derived*
from stationarity) `B1 = eigenbasis(ρ)`, plus the live/nondegenerate dephasing baseline. **Open:** the
out-of-equilibrium identification (Connes–Rovelli) and a population-transfer dissipator that would make the
relocation law true (paper three).

**Provenance.** `R / S` — einselection, decoherence-free subspaces, the Hilbert–Schmidt geometry, and
phase-damping decay are standard; the synthesis is deriving the basis alignment from "the clock-state is the
rest-state," reading the conserved band as the einselected structure, and *checking* whether its HS invariant
is presence — finding it conserved and split into knowing/energy, but the arrow a pure loss, not the
relocation paper three's conservation law would need.
-/
import Paper3.OneGenerator
import Theory.BandFromAxioms

namespace Paper3.Einselection

open Matrix Complex Filter Topology
open Paper3.OneGenerator Theory.ModularFlow Theory.RotatingSpectrum
open Theory.BandCoincidence Theory.BandFromAxioms
open scoped ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1 Part A — stationarity forces the alignment `B1 = eigenbasis(ρ)` -/

omit [Fintype n] [DecidableEq n] in
/-- **Stationarity kills off-diagonal coherence.** If the modular state `ρ` is at rest under the dissipator
(`𝒟(ρ) = 0`), then on every genuinely-damping edge (`μ ≠ 1`, live) its coherence vanishes. Under the
nondegenerate/live baseline (`μ i j = 1 ↔ i = j`; `μ ≠ 0`) that is exactly the off-diagonal: `ρ` is
**diagonal in B1**. The selection principle in one line — *the clock-state is the rest-state.* -/
theorem stationary_forces_offdiag_zero (ρ : Matrix n n ℂ) (μ : n → n → ℂ)
    (hlive : ∀ i j, μ i j ≠ 0) (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    (hstat : dissipatorGen μ ρ = 0) :
    ∀ i j, i ≠ j → ρ i j = 0 := by
  intro i j hij
  have h := congrFun (congrFun hstat i) j
  simp only [dissipatorGen, schur_apply, Matrix.zero_apply] at h
  rcases mul_eq_zero.mp h with hlog | hρ
  · exfalso
    have hμ1 : μ i j = 1 := by
      have he := Complex.exp_log (hlive i j)
      rw [hlog, Complex.exp_zero] at he
      exact he.symm
    exact hij ((hnd i j).mp hμ1)
  · exact hρ

omit [Fintype n] in
/-- **`ρ` is diagonal in B1** (its own diagonal) — the stationary state of the arrow is diagonal in the
decoherence basis. -/
theorem stationary_eq_diagonal (ρ : Matrix n n ℂ) (μ : n → n → ℂ)
    (hlive : ∀ i j, μ i j ≠ 0) (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    (hstat : dissipatorGen μ ρ = 0) :
    ρ = diagonal (fun i => ρ i i) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h; rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ h]
    exact stationary_forces_offdiag_zero ρ μ hlive hnd hstat i j h

omit [Fintype n] [DecidableEq n] in
/-- A Hermitian matrix has real diagonal entries: `ρ i i = ↑(ρ i i).re`. -/
theorem isHermitian_diag_real (ρ : Matrix n n ℂ) (hHerm : ρ.IsHermitian) (i : n) :
    ρ i i = ((ρ i i).re : ℂ) := by
  have h := congrFun (congrFun hHerm i) i
  rw [conjTranspose_apply] at h
  -- h : conj (ρ i i) = ρ i i  (RCLike.star)
  have him : (ρ i i).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp
  · simp [him]

omit [Fintype n] in
/-- **B1 = eigenbasis(ρ), derived.** For a Hermitian stationary state `ρ`, stationarity under the arrow
forces `ρ = diag(d)` with `dᵢ = (ρ i i).re` real — precisely the `diagonal (RCLike.ofReal ∘ d)` shape that
`Paper3.OneGenerator` (spec XV) *assumed*. So spec XV's alignment is a **consequence** of "one generator with
one rest-state," not a posit — in the non-degenerate equilibrium case. **Boundaries:** for *degenerate* `ρ`
the eigenbasis within a degenerate block is under-determined (diagonality still holds, so the commutation
result stands; the unique knowing/energy frame does not); *out of equilibrium* there is no single stationary
`ρ` (the inherited Connes–Rovelli regime). -/
theorem stationary_eq_diagonal_real (ρ : Matrix n n ℂ) (μ : n → n → ℂ) (hHerm : ρ.IsHermitian)
    (hlive : ∀ i j, μ i j ≠ 0) (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    (hstat : dissipatorGen μ ρ = 0) :
    ρ = diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ fun i => (ρ i i).re) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    rw [diagonal_apply_eq, Function.comp_apply]
    exact isHermitian_diag_real ρ hHerm i
  · rw [diagonal_apply_ne _ h]
    exact stationary_forces_offdiag_zero ρ μ hlive hnd hstat i j h

/-! ## §2 Part B — the einselected structure is the conserved band `Peri = fixed ⊕ rotating`

The modes robust under the one generator `𝓛 = -i[K,·] + 𝒟` are exactly the non-decaying band
(`genReal = 0`), i.e. the conserved band — A3's sustainable field `Peri` (`peri_iff_mem_conservedBand`). The
selection principle picks `Peri` as what survives; band-coincidence already splits it into the **fixed**
sub-band (the diagonal record — knowing) and the **rotating** sub-band (the modular phase — energy). No new
proof — the identification, made explicit. -/

omit [Fintype n] [DecidableEq n] in
/-- **Robust = conserved**, edge level: the generator's non-decaying edges (`genReal = 0`) are exactly the
conserved edges (`‖μ‖ = 1`). (Restates `RotatingSpectrum.genReal_eq_zero_iff` against `conservedEdge`.) -/
theorem genReal_zero_iff_conservedEdge (μ : n → n → ℂ) (i j : n) (h : μ i j ≠ 0) :
    genReal μ i j = 0 ↔ conservedEdge μ i j :=
  genReal_eq_zero_iff μ i j h

omit [Fintype n] [DecidableEq n] in
/-- **The einselected band splits in two — `conserved = fixed ∨ rotating`**, disjointly. The conserved
(robust) band is the **fixed** sub-band (`μ = 1`, the persistent diagonal record / knowing) together with the
**rotating** sub-band (`‖μ‖ = 1, μ ≠ 1`, the un-attendable modular phase / energy). -/
theorem conservedEdge_iff_fixed_or_rotating (μ : n → n → ℂ) (i j : n) :
    conservedEdge μ i j ↔ fixedEdge μ i j ∨ rotatingEdge μ i j := by
  unfold conservedEdge fixedEdge rotatingEdge
  constructor
  · intro hc
    by_cases hμ : μ i j = 1
    · exact Or.inl hμ
    · exact Or.inr ⟨hc, hμ⟩
  · rintro (hf | hr)
    · rw [hf]; exact norm_one
    · exact hr.1

omit [Fintype n] [DecidableEq n] in
/-- The two sub-bands are **disjoint**: an edge cannot be both fixed (`μ = 1`) and rotating (`μ ≠ 1`). -/
theorem not_fixed_and_rotating (μ : n → n → ℂ) (i j : n) :
    ¬(fixedEdge μ i j ∧ rotatingEdge μ i j) := by
  rintro ⟨hf, hr⟩; exact hr.2 hf

/-! ## §3 Part C — define presence, and test conservation / split / relocation

**Define** presence from the einselected band — the Hilbert–Schmidt weight carried by the conserved band —
and then *test*, proving or refuting each claim. We work with the **squared** HS weight (the inner-product
content; the norm is its square root), so the Pythagorean split is an exact equation. -/

open scoped Classical in
/-- The squared Hilbert–Schmidt weight a matrix carries on the `P`-edges: `∑_{(i,j)∈P} ‖Mᵢⱼ‖²`. The
orthogonal projection onto a coordinate band, measured in the HS inner product. -/
noncomputable def weightOn (P : n → n → Prop) (M : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, if P i j then Complex.normSq (M i j) else 0

/-- **presence²** — the conserved-band weight, the candidate invariant. -/
noncomputable def presenceSq (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := weightOn (conservedEdge μ) M

/-- **knowing²** — the fixed (diagonal record) sub-band weight. -/
noncomputable def knowingSq (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := weightOn (fixedEdge μ) M

/-- **energy²** — the rotating (modular phase) sub-band weight. -/
noncomputable def energySq (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := weightOn (rotatingEdge μ) M

/-- The transient (attendable, decaying) weight — *outside* the conserved band (`‖μ‖ < 1`). -/
noncomputable def transientSq (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ :=
  weightOn (fun i j => ‖μ i j‖ < 1) M

theorem normSq_of_norm_one (z : ℂ) (h : ‖z‖ = 1) : Complex.normSq z = 1 := by
  rw [Complex.normSq_eq_abs, ← Complex.norm_eq_abs, h, one_pow]

omit [DecidableEq n] in
/-- **A modulus-one Schur multiplier preserves band weight.** If `‖ν i j‖ = 1` on every `P`-edge, then
`schur ν` leaves the `P`-band weight unchanged: the entries on `P` only get rotated, never scaled. The engine
of every conservation statement below. -/
theorem weightOn_schur_of_norm_one (P : n → n → Prop) (ν : n → n → ℂ) (M : Matrix n n ℂ)
    (hν : ∀ i j, P i j → ‖ν i j‖ = 1) :
    weightOn P (schur ν M) = weightOn P M := by
  classical
  unfold weightOn
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : P i j
  · rw [if_pos h, if_pos h, schur_apply, Complex.normSq_mul, normSq_of_norm_one _ (hν i j h),
      one_mul]
  · rw [if_neg h, if_neg h]

omit [DecidableEq n] in
/-- **The Pythagorean split — `presence² = knowing² + energy²`.** The fixed and rotating sub-bands have
*disjoint* edge supports whose union is the conserved band, so their HS weights add to the conserved weight.
The orthogonality is coordinate-orthogonality in the matrix-unit basis — and it **survives the modular
rotation** because the rotation is a Schur multiplier diagonal in that same basis (`weightOn_schur` maps
fixed→fixed, rotating→rotating), never mixing the two. So the split is exact and flow-invariant. -/
theorem pythagorean (μ : n → n → ℂ) (M : Matrix n n ℂ) :
    presenceSq μ M = knowingSq μ M + energySq μ M := by
  classical
  unfold presenceSq knowingSq energySq weightOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hf : fixedEdge μ i j
  · have hc : conservedEdge μ i j := (conservedEdge_iff_fixed_or_rotating μ i j).mpr (Or.inl hf)
    rw [if_pos hc, if_pos hf, if_neg (fun hr => not_fixed_and_rotating μ i j ⟨hf, hr⟩), add_zero]
  · by_cases hr : rotatingEdge μ i j
    · have hc : conservedEdge μ i j := (conservedEdge_iff_fixed_or_rotating μ i j).mpr (Or.inr hr)
      rw [if_pos hc, if_neg hf, if_pos hr, zero_add]
    · have hc : ¬ conservedEdge μ i j := by
        intro hcc
        rcases (conservedEdge_iff_fixed_or_rotating μ i j).mp hcc with h1 | h1
        · exact hf h1
        · exact hr h1
      rw [if_neg hc, if_neg hf, if_neg hr, add_zero]

/-! ### Test 1 — presence is conserved (exactly), and so are knowing and energy

Both faces of `𝓛` are Schur multipliers; on the conserved band each has modulus exactly `1` — the modular
clock everywhere (`norm_modularMul`), the dissipator on `‖μ‖ = 1` edges (`norm_dissipatorMul`). So the joint
flow `combinedFlow` rotates the conserved-band entries without scaling them: presence is **exactly**
conserved (ℂ-exact, not an operational floor), and likewise its two halves. -/

omit [Fintype n] [DecidableEq n] in
/-- The modular clock is everywhere modulus-one: `‖(dᵢ/dⱼ)^{is}‖ = 1`. The unitary face scales nothing. -/
theorem norm_modularMul (d : n → ℝ) (s : ℝ) (i j : n) : ‖modularMul d s i j‖ = 1 := by
  rw [modularMul, Complex.norm_eq_abs, Complex.abs_exp]
  have hre : (Complex.I * (s : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (d j) : ℂ))).re = 0 := by
    rw [show Complex.I * (s : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (d j) : ℂ))
          = Complex.I * ((s * (Real.log (d i) - Real.log (d j)) : ℝ) : ℂ) from by push_cast; ring,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero]

omit [Fintype n] [DecidableEq n] in
/-- The dissipator's per-edge modulus is `exp(t · genReal)`; on conserved (`‖μ‖ = 1`) edges it is `1`. -/
theorem norm_dissipatorMul (μ : n → n → ℂ) (t : ℝ) (i j : n) :
    ‖dissipatorMul μ t i j‖ = Real.exp (t * genReal μ i j) := by
  rw [dissipatorMul, Complex.norm_eq_abs, Complex.abs_exp]
  congr 1
  rw [Complex.re_ofReal_mul, genReal]

omit [Fintype n] [DecidableEq n] in
theorem norm_dissipatorMul_of_norm_one (μ : n → n → ℂ) (t : ℝ) (i j : n) (h : ‖μ i j‖ = 1) :
    ‖dissipatorMul μ t i j‖ = 1 := by
  rw [norm_dissipatorMul, genReal_eq_log_norm, h, Real.log_one, mul_zero, Real.exp_zero]

/-- **The modular clock preserves every band weight** — it is a modulus-one Schur multiplier on all edges. -/
theorem weightOn_modularFlow (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (P : n → n → Prop)
    (M : Matrix n n ℂ) :
    weightOn P (modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M) = weightOn P M := by
  rw [modularFlow_diagonal_eq_schur]
  exact weightOn_schur_of_norm_one P (modularMul d s) M (fun i j _ => norm_modularMul d s i j)

omit [DecidableEq n] in
/-- **The dissipator preserves any band of conserved edges** — on `‖μ‖ = 1` edges it is modulus-one. -/
theorem weightOn_dephaseFlow (P : n → n → Prop) (μ : n → n → ℂ) (t : ℝ) (M : Matrix n n ℂ)
    (hP : ∀ i j, P i j → ‖μ i j‖ = 1) :
    weightOn P (dephaseFlow μ t M) = weightOn P M := by
  unfold dephaseFlow
  exact weightOn_schur_of_norm_one P (dissipatorMul μ t) M
    (fun i j hij => norm_dissipatorMul_of_norm_one μ t i j (hP i j hij))

/-- **presence is conserved under the one generator** — exactly. The conserved-band weight is invariant
under `combinedFlow`: the dissipator does not touch `‖μ‖ = 1` edges and the modular clock only rotates them.
`[proved — ℂ-exact conservation, at equilibrium]`. -/
theorem presence_conserved (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β t : ℝ)
    (M : Matrix n n ℂ) :
    presenceSq μ (combinedFlow d hρ μ β t M) = presenceSq μ M := by
  unfold presenceSq combinedFlow
  rw [weightOn_modularFlow]
  exact weightOn_dephaseFlow (conservedEdge μ) μ t M (fun i j h => h)

/-- **knowing is conserved** — the diagonal record weight is exactly invariant under `combinedFlow`. This is
the key to Test 3: the persistent record does **not** grow under the flow. -/
theorem knowing_conserved (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β t : ℝ)
    (M : Matrix n n ℂ) :
    knowingSq μ (combinedFlow d hρ μ β t M) = knowingSq μ M := by
  unfold knowingSq combinedFlow
  rw [weightOn_modularFlow]
  exact weightOn_dephaseFlow (fixedEdge μ) μ t M
    (fun i j h => by rw [show μ i j = 1 from h]; exact norm_one)

/-- **energy is conserved** — the modular-phase weight is exactly invariant under `combinedFlow`. -/
theorem energy_conserved (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β t : ℝ)
    (M : Matrix n n ℂ) :
    energySq μ (combinedFlow d hρ μ β t M) = energySq μ M := by
  unfold energySq combinedFlow
  rw [weightOn_modularFlow]
  exact weightOn_dephaseFlow (rotatingEdge μ) μ t M (fun i j h => h.1)

/-! ### presence as a norm, and the Pythagorean split in norms

`presence := √(presence²)`, etc. The squared identities above are the content; these are their square-root
shadows, recording `presence² = knowing² + energy²` and the invariance of `presence` directly. -/

omit [DecidableEq n] in
theorem weightOn_nonneg (P : n → n → Prop) (M : Matrix n n ℂ) : 0 ≤ weightOn P M := by
  classical
  unfold weightOn
  refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
  by_cases h : P i j
  · rw [if_pos h]; exact Complex.normSq_nonneg _
  · rw [if_neg h]

/-- **presence** — the Hilbert–Schmidt norm of the conserved-band projection. -/
noncomputable def presence (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := Real.sqrt (presenceSq μ M)
/-- **knowing** — the HS norm of the fixed (record) sub-band projection. -/
noncomputable def knowing (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := Real.sqrt (knowingSq μ M)
/-- **energy** — the HS norm of the rotating (modular phase) sub-band projection. -/
noncomputable def energy (μ : n → n → ℂ) (M : Matrix n n ℂ) : ℝ := Real.sqrt (energySq μ M)

omit [DecidableEq n] in
theorem presence_sq (μ : n → n → ℂ) (M : Matrix n n ℂ) : presence μ M ^ 2 = presenceSq μ M :=
  Real.sq_sqrt (weightOn_nonneg _ _)
omit [DecidableEq n] in
theorem knowing_sq (μ : n → n → ℂ) (M : Matrix n n ℂ) : knowing μ M ^ 2 = knowingSq μ M :=
  Real.sq_sqrt (weightOn_nonneg _ _)
omit [DecidableEq n] in
theorem energy_sq (μ : n → n → ℂ) (M : Matrix n n ℂ) : energy μ M ^ 2 = energySq μ M :=
  Real.sq_sqrt (weightOn_nonneg _ _)

omit [DecidableEq n] in
/-- **Test 2, in norms: `presence² = knowing² + energy²`.** The Pythagorean decomposition of presence into
the persistent record (knowing) and the modular phase (energy), orthogonal in the HS inner product and
preserved through the modular rotation. `[proved — exact, at equilibrium]`. -/
theorem pythagorean_norm (μ : n → n → ℂ) (M : Matrix n n ℂ) :
    presence μ M ^ 2 = knowing μ M ^ 2 + energy μ M ^ 2 := by
  rw [presence_sq, knowing_sq, energy_sq, pythagorean]

/-- **Test 1, in norms: presence is conserved under the one generator.** -/
theorem presence_conserved_norm (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β t : ℝ)
    (M : Matrix n n ℂ) :
    presence μ (combinedFlow d hρ μ β t M) = presence μ M := by
  unfold presence; rw [presence_conserved]

/-! ### Test 3 — the arrow is loss, not relocation

The candidate intuition for paper three is that decoherence *relocates* the attendable transient into the
record (knowing grows at constant presence). We **refute** it for this generator: `knowing` is exactly
constant under the flow (`knowing_conserved`), while the transient weight tends to **zero**
(`transient_tendsto_zero`) — the attendable coherence is *lost*, not moved into the record. The total weight
splits as `presence² + transient²` (`full_split`), `presence²` is invariant, and the lost `transient²` does
**not** reappear in `knowing²`. So the minimal one generator supplies a *conserved presence* but **no
relocation/conservation law of the "knowing grows" kind** — paper three needs a genuine population-transfer
dissipator for that. A real negative, precisely located (Outcome 2). -/

omit [DecidableEq n] in
/-- **The total HS weight splits into conserved + transient** (contractive `‖μ‖ ≤ 1`): every edge is either
conserved (`‖μ‖ = 1`) or transient (`‖μ‖ < 1`). So `‖M‖²_HS = presence² + transient²`. -/
theorem full_split (μ : n → n → ℂ) (M : Matrix n n ℂ) (hc : ∀ i j, ‖μ i j‖ ≤ 1) :
    weightOn (fun _ _ => True) M = presenceSq μ M + transientSq μ M := by
  classical
  unfold presenceSq transientSq weightOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [if_pos trivial]
  rcases lt_or_eq_of_le (hc i j) with hlt | heq
  · rw [if_neg (show ¬ conservedEdge μ i j from ne_of_lt hlt), if_pos hlt, zero_add]
  · rw [if_pos (show conservedEdge μ i j from heq),
      if_neg (not_lt.mpr (le_of_eq heq.symm)), add_zero]

omit [DecidableEq n] in
/-- **The transient weight vanishes** — under the dissipative flow the attendable (`‖μ‖ < 1`, live)
coherence decays to `0`. The arrow erodes it to nothing. -/
theorem transient_tendsto_zero (μ : n → n → ℂ) (M : Matrix n n ℂ) (hlive : ∀ i j, μ i j ≠ 0) :
    Tendsto (fun t => transientSq μ (dephaseFlow μ t M)) atTop (𝓝 0) := by
  classical
  have key : ∀ i j, Tendsto
      (fun t => if ‖μ i j‖ < 1 then Complex.normSq (dephaseFlow μ t M i j) else 0) atTop (𝓝 0) := by
    intro i j
    by_cases h : ‖μ i j‖ < 1
    · have hr : genReal μ i j < 0 := (genReal_neg_iff μ i j (hlive i j)).mpr h
      have hfun : (fun t => if ‖μ i j‖ < 1 then Complex.normSq (dephaseFlow μ t M i j) else 0)
          = fun t : ℝ => Real.exp (t * genReal μ i j) ^ 2 * Complex.normSq (M i j) := by
        funext t
        rw [if_pos h]
        unfold dephaseFlow
        rw [schur_apply, Complex.normSq_mul]
        congr 1
        rw [Complex.normSq_eq_abs, ← Complex.norm_eq_abs, norm_dissipatorMul]
      rw [hfun]
      have h1 : Tendsto (fun t : ℝ => t * genReal μ i j) atTop atBot :=
        Tendsto.atTop_mul_const_of_neg hr tendsto_id
      have h2 : Tendsto (fun t : ℝ => Real.exp (t * genReal μ i j) ^ 2) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atBot.comp h1).pow 2
        simpa using this
      simpa using h2.mul_const (Complex.normSq (M i j))
    · simp only [if_neg h]; exact tendsto_const_nhds
  have hsum := tendsto_finset_sum (Finset.univ : Finset n)
    (fun i _ => tendsto_finset_sum (Finset.univ : Finset n) (fun j _ => key i j))
  simpa [transientSq, weightOn] using hsum

/-- **Test 3, the verdict: the arrow is loss, not relocation.** Under the one generator, `knowing` is
*exactly constant* for all time while the transient weight tends to `0`: the decohered coherence is erased,
not moved into the record. Presence is conserved (Test 1), splits as knowing ⊕ energy (Test 2), and the arrow
removes the *non-present* (attendable) part without feeding the record — so paper three's conservation law is
**not** of the relocation kind here; it needs a population-transferring dissipator beyond pure phase damping.
`[the relocation reading: refuted; presence/knowing/energy: conserved and split]`. -/
theorem arrow_is_loss_not_relocation (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (μ : n → n → ℂ) (β : ℝ)
    (M : Matrix n n ℂ) (hlive : ∀ i j, μ i j ≠ 0) :
    (∀ t, knowingSq μ (combinedFlow d hρ μ β t M) = knowingSq μ M)
      ∧ Tendsto (fun t => transientSq μ (dephaseFlow μ t M)) atTop (𝓝 0) :=
  ⟨fun t => knowing_conserved d hρ μ β t M, transient_tendsto_zero μ M hlive⟩

end Paper3.Einselection
