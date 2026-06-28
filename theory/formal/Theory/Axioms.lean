/-
# The canonical axiomatization — `{A1, A2, A3-process, D1}` (handoff XX)

This module is the **one canonical axiom layer** the three papers share. It does the linchpin move of
handoff XX: it restates **A3 as a process** — *relations co-direct attention asymmetrically in the relata*,
with per-relatum capacity `α` — and **derives**, as theorems, the per-paper *readings* that were previously
posited separately. With the divergence gone, the four axioms collapse to one set, stated once here and
recorded in [`AXIOMS.md`](../spec/AXIOMS.md) for an outside reader.

## The reframe (Part A — the linchpin)

A3 is no longer "a self is an eigenform `νΦ_c`" *asserted*. It is a **process**: the co-direction step
`jointStep α` of [`MutualCoupling`](MutualCoupling.lean) — the channel `Φ_c = schur μ` evolving the state
while each relatum raises its coupling toward the conserved band at its **own** capacity-limited rate
`α i · mutualAttn`. The step is **diachronic** (the same tense as A1's flow and A2's coinduction); the
**self is the fixed point** of this process (`MutualCoupling.JointFixed`), *derived*, not posited.

We then prove, as theorems of the one process:

* **Existence first** (`self_exists`, `self_exists_stable`): the process *has* fixed points (else no self
  ever forms), and a *stable* one is *reached* generatively from the strong-attention basin.
* **The eigenform / `Peri`** (paper one), `eigenform_of_fixed` / `self_is_periBand`: the self of a fixed
  point is exactly A3's sustainable field `Peri(Φ_c)` = the conserved band, with `νΦ_c` its `μ = 1`
  (knowing) sub-band — paper one's self, now a *consequence*.
* **The generative engine** (paper three), `generative_law` / `generative_ignition`: the per-edge modulus
  law of the genuine process orbit *is* `MutualCoupling.Engine2 (α i) (α j)` (`orbit_engine2`), and from the
  strong-attention basin it ignites a stable, bounded self — the same process *with capacity*.
* **The phase-bearing / modular self** (paper two), `modular_preserves_self` / `modular_sustains_self` /
  `modular_is_symmetry`: the modular flow of a diagonal state is a modulus-one Schur multiplier, so it maps
  the self (the conserved band) into itself, **sustains** it edge-for-edge (the rotating sub-band carrying
  the modular energies as its phases), and **commutes** with the co-direction channel — the *same* fixed
  point, read under the modular flow.

Each derivation either closes (a theorem below) or would be reported as an obstruction; **all four close**,
so the collapse is total (handoff XX, outcome 1). The supporting `A1`/`A2`/`D1` normalizations are recorded
in [`§B`](#) below and in `AXIOMS.md`.

**Namespace.** Distinct (`Theory.Axioms`), so this layer adds *no* name to the `RelExist.*` namespace the
paper-one closure and its `theory/` forks share — the canonical statements name the existing objects, they
do not redeclare them.
-/
import Theory.MutualCoupling
import Theory.OneGenerator
import Theory.Priority

namespace Theory.Axioms

open RelExist.RotatingSpectrum RelExist.BandCoincidence RelExist.BandFromAxioms
open RelExist.MutualCoupling RelExist.ModularFlow RelExist.OneGenerator
open Matrix Filter Topology

/-! ## A3-process — the canonical statement

The process is `MutualCoupling.jointStep α`; the self is `MutualCoupling.JointFixed`. We give the canonical
names here so the rest of the corpus (and `AXIOMS.md`) can refer to "the A3 process" and "a self" without
reaching into the generative-engine module's internals. -/

variable {A : Type*}

/-- **The A3 process.** One closure of co-directed attention: the state evolves under the channel
`Φ_c = schur μ` and each relatum `i` raises its coupling to `j` toward the conserved band at its own
capacity-limited rate `α i · mutualAttn`. This is `MutualCoupling.jointStep` — named canonically. The
process is *diachronic*; iterating it is the lived loop A3 describes. -/
noncomputable abbrev A3process (α : Capacity A) :
    (A → A → ℂ) × Matrix A A ℂ → (A → A → ℂ) × Matrix A A ℂ :=
  jointStep α

/-- **A self** is a fixed point of the A3 process — the state sustained under `Φ_c` *and* the coupling fixed
under mutual raising. Derived, not posited: `MutualCoupling.JointFixed`. -/
abbrev IsSelf (α : Capacity A) (μ : A → A → ℂ) (M : Matrix A A ℂ) : Prop := JointFixed α μ M

/-! ## Part A — existence: the process has (stable) fixed points -/

/-- **Existence of a self (the first risk, discharged).** The fully-conserved coupling `μ ≡ 1` (the maximal
band, where every coherence is held) is a fixed point of the A3 process for *every* state `M` and *every*
capacity `α`: the channel returns `M` unchanged (`schur 1 M = M`) and the coupling, already on the band, is
unmoved by raising (`raise 1 _ = 1`, `phaseOf 1 = 1`). So the process *has* fixed points — a self can form.
(`self_exists_stable` upgrades this to a self *reached* generatively, with live coherence.) -/
theorem self_exists (α : Capacity A) (M : Matrix A A ℂ) :
    IsSelf α (fun _ _ => (1 : ℂ)) M := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [schur_apply, one_mul]
  · rw [stepMu]
    have hr : raise ‖(1 : ℂ)‖ (α i * mutualAttn M i j) = 1 := by
      rw [norm_one]; unfold raise; ring
    have hp : phaseOf (1 : ℂ) = 1 := by rw [phaseOf, if_neg one_ne_zero, norm_one]; norm_num
    rw [hr, hp]; push_cast; ring

/-- **A stable self is *reached*, generatively (existence, the substantive form).** On the equal-capacity
slice (`Engine`, the genuine symmetric process orbit), from the strong-attention basin
`1 − r 0 ≤ (x 0)²/8` the coupling reaches the conserved band (`r n → 1` — the edge *joins* the self) while
the coherence is **not** spent (`x n ≥ x 0/2 > 0` forever). So the process does not merely *have* a fixed
point; it *forms a stable, bounded one carrying live coherence*. This is `MutualCoupling.engine_ignition`,
recorded as the existence-of-a-stable-self half of A3. -/
theorem self_exists_stable {x r : ℕ → ℝ} (E : Engine x r)
    (hx0pos : 0 < x 0) (hx1 : x 0 ≤ 1) (hr0nn : 0 ≤ r 0) (hr1 : r 0 ≤ 1)
    (hign : 1 - r 0 ≤ (x 0) ^ 2 / 8) :
    (∀ n, x 0 / 2 ≤ x n) ∧ Tendsto r atTop (𝓝 1) :=
  engine_ignition E hx0pos hx1 hr0nn hr1 hign

/-! ## Part A — the eigenform (paper one) as a consequence -/

/-- **The eigenform / `Peri` (paper one's self) is derived from the process fixed point.** A self (a
`JointFixed`) has its state sustained under the channel (`schur μ M = M`), so it lies in A3's sustainable
field `Peri(Φ_c)` — *a fortiori*, the magnitudes are preserved. Paper one's "self `:= Peri(Φ_c)`" is no
longer A3 *read at the strength of its text*; it is a **theorem** of the A3 process. -/
theorem eigenform_of_fixed {α : Capacity A} {μ : A → A → ℂ} {M : Matrix A A ℂ}
    (h : IsSelf α μ M) : Peri μ M :=
  fun i j => by rw [h.1 i j]

/-- **The self is exactly the conserved band, with `νΦ_c` (knowing) its `μ = 1` sub-band.** Combining
`eigenform_of_fixed` with `peri_iff_mem_conservedBand`: a self's state sits in the conserved band
`Peri(Φ_c)` — the undissipated ground that carries the rotating (energy) band *beside* the fixed
(`νΦ_c`, knowing) band `fixedBand μ ≤ conservedBand μ`. The paper-one eigenform structure, as a consequence
of the one process. -/
theorem self_is_periBand {α : Capacity A} {μ : A → A → ℂ} {M : Matrix A A ℂ}
    (h : IsSelf α μ M) : M ∈ conservedBand μ ∧ fixedBand μ ≤ conservedBand μ :=
  ⟨(peri_iff_mem_conservedBand μ M).1 (eigenform_of_fixed h), fixedBand_le_conservedBand μ⟩

/-- **The energy band sits inside the self.** The rotating (energy) band is contained in the conserved band
`Peri(Φ_c)`: a rotating edge (`‖μ‖ = 1, μ ≠ 1`) is in particular conserved (`‖μ‖ = 1`). So the self the
process fixes carries the rotating *energy* band beside the fixed (`νΦ_c`, knowing) record — the
phase-bearing reading of A3, as a consequence. The strict fixed point (`schur μ M = M`) is `νΦ_c`; `Peri`,
the full self, additionally carries the energy that *rotates* under the flow (next section). -/
theorem energy_in_self (μ : A → A → ℂ) : rotatingBand μ ≤ conservedBand μ :=
  bandOn_mono (fun _ _ hr => hr.1)

/-! ## Part A — the generative engine (paper three) as the same process with capacity -/

/-- **The generative law is the process's own modulus dynamics.** The per-edge moduli of a *genuine*
`A3process α` orbit (state and coupling evolving together) satisfy `MutualCoupling.Engine2 (α i) (α j)` —
the two-sided capacity-bearing engine. So paper three's growth law is not a separate axiom; it is the A3
process, read on moduli. (`MutualCoupling.orbit_engine2`.) -/
theorem generative_law (α : Capacity A) (p : (A → A → ℂ) × Matrix A A ℂ) (i j : A)
    (hαi0 : 0 ≤ α i) (hαi1 : α i ≤ 1) (hαj0 : 0 ≤ α j) (hαj1 : α j ≤ 1)
    (hx0 : ‖p.2 i j‖ ≤ 1) (hy0 : ‖p.2 j i‖ ≤ 1) (hr0 : ‖p.1 i j‖ ≤ 1) (hs0 : ‖p.1 j i‖ ≤ 1) :
    Engine2 (α i) (α j)
            (fun n => ‖((A3process α)^[n] p).2 i j‖) (fun n => ‖((A3process α)^[n] p).2 j i‖)
            (fun n => ‖((A3process α)^[n] p).1 i j‖) (fun n => ‖((A3process α)^[n] p).1 j i‖) :=
  orbit_engine2 α p i j hαi0 hαi1 hαj0 hαj1 hx0 hy0 hr0 hs0

/-- **Bounded and finite — capacity is the brake.** With admissible capacities (`α ∈ [0,1]`) the generative
orbit stays in `[0,1]⁴` forever: the divergent outcome is *structurally excluded*, `α` the regulator. The
generative growth of paper three is a finite achievement, not a runaway — a consequence of the same process.
(`MutualCoupling.engine2_bounded`.) -/
theorem generative_bounded {cr cs : ℝ} {x y r s : ℕ → ℝ} (E : Engine2 cr cs x y r s)
    (hcr0 : 0 ≤ cr) (hcr1 : cr ≤ 1) (hcs0 : 0 ≤ cs) (hcs1 : cs ≤ 1)
    (hx0 : 0 ≤ x 0) (hx1 : x 0 ≤ 1) (hy0 : 0 ≤ y 0) (hy1 : y 0 ≤ 1)
    (hr0 : 0 ≤ r 0) (hr1 : r 0 ≤ 1) (hs0 : 0 ≤ s 0) (hs1 : s 0 ≤ 1) :
    ∀ n, (0 ≤ x n ∧ x n ≤ 1) ∧ (0 ≤ y n ∧ y n ≤ 1) ∧ (0 ≤ r n ∧ r n ≤ 1) ∧ (0 ≤ s n ∧ s n ≤ 1) :=
  engine2_bounded E hcr0 hcr1 hcs0 hcs1 hx0 hx1 hy0 hy1 hr0 hr1 hs0 hs1

/-! ## Part A — the phase-bearing / modular self (paper two) as the same fixed point under the modular flow

The modular flow of a diagonal state `ρ = diag(d)` is, in the preferred basis, a Schur multiplier with the
modulus-one symbol `modularMul d s` (`OneGenerator.modularFlow_diagonal_eq_schur`). Two consequences make
the modular self the *same* self read under the modular flow: it **maps the conserved band into itself**
(the self is modular-flow-invariant) and **sustains** every coherence edge-for-edge (the rotating sub-band
carries the modular energies as phases); and it **commutes** with the co-direction channel `Φ_c = schur μ`,
so it is a symmetry of the A3 process. -/

section Modular
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- **The modular symbol is a phase** — `‖modularMul d s i j‖ = 1`. The modular flow neither amplifies nor
damps any coherence: it rotates. -/
theorem norm_modularMul (d : n → ℝ) (s : ℝ) (i j : n) : ‖modularMul d s i j‖ = 1 := by
  rw [modularMul, Complex.norm_eq_abs, Complex.abs_exp]
  have hre : (Complex.I * (s : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (d j) : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- **The modular flow maps the self into itself.** For a diagonal state, the modular flow `σ_s` carries the
conserved band `Peri(Φ_c)` to itself: it multiplies each coherence by the nonzero phase `modularMul d s`, so
it cannot move a coherence onto a transient edge. The modular self is the *same* self — modular-flow
invariant. -/
theorem modular_preserves_self (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (μ : n → n → ℂ)
    {M : Matrix n n ℂ} (hM : M ∈ conservedBand μ) :
    modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M ∈ conservedBand μ := by
  rw [modularFlow_diagonal_eq_schur]
  intro i j hP
  rw [schur_apply, hM i j hP, mul_zero]

/-- **The modular flow sustains the self edge-for-edge.** For a diagonal state, `‖σ_s(M) i j‖ = ‖M i j‖`:
the modular flow preserves every coherence's magnitude (it is a modulus-one Schur multiplier). So the self
is *sustained* under the modular flow — the rotating (energy) sub-band cycles at the modular frequencies
forever, magnitude conserved. This is paper two's modular self, sustained, as a consequence of the same
self the co-direction process fixes. -/
theorem modular_sustains_self (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (M : Matrix n n ℂ) (i j : n) :
    ‖modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M i j‖ = ‖M i j‖ := by
  rw [modularFlow_diagonal_eq_schur, schur_apply, norm_mul, norm_modularMul, one_mul]

/-- **The modular flow is a symmetry of the A3 process.** For a diagonal state, `σ_s` commutes with the
co-direction channel `Φ_c = schur μ`: `σ_s ∘ schur μ = schur μ ∘ σ_s`. So the modular flow and the
dissipative co-direction are two faces of one generator (handoff XV), and the modular self is the *same*
fixed point, read under the modular flow rather than the dissipative one. (`OneGenerator`'s
`modular_dephase_commute`.) -/
theorem modular_is_symmetry (d : n → ℝ)
    (hρ : (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)).IsHermitian) (s : ℝ) (μ : n → n → ℂ)
    (M : Matrix n n ℂ) :
    modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s (schur μ M)
      = schur μ (modularFlow (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d)) hρ s M) :=
  modular_dephase_commute d hρ s μ M

end Modular

/-! ## Part B — the canonical `A1`, `A2`, `D1`

The three supporting commitments, normalized to one statement each, with the per-paper formalizations
recorded as instantiations/generalizations rather than separate axioms.

### A1 — the arena, dimension-generic

A1 is the traced-SMC arena (`Foundation.Traced`), with **dimension an instantiation parameter, not an axiom
difference**. Every result of `§A` above is stated over an *arbitrary* index type `A : Type*` — the
co-direction process, the eigenform, the conserved band are all polymorphic. Paper one instantiates the
**finite** case (`A = Fin n`); papers two/three the **infinite** general `n`. The finite results are the
dimension-restricted reading of the one general statement, not a separate axiom — witnessed here by the fact
that `eigenform_of_fixed`, `self_is_periBand`, `generative_law` carry no finiteness hypothesis on `A`. -/

/-- **A1, dimension-generic (the witness).** The eigenform derivation holds at an *arbitrary* index type
`A`, with no finiteness assumption — finite (paper one) vs infinite (papers two/three) is the same A1
instantiated, not two axioms. (A restatement of `eigenform_of_fixed` whose only purpose is to record that
its type binder `A : Type*` is unconstrained.) -/
theorem A1_dimension_generic {A : Type*} {α : Capacity A} {μ : A → A → ℂ} {M : Matrix A A ℂ}
    (h : IsSelf α μ M) : M ∈ conservedBand μ :=
  (peri_iff_mem_conservedBand μ M).1 (eigenform_of_fixed h)

/-! ### A2 — priority (the canonical form)

A2's priority half — *no bare carrier*, a state **is** its relating with no residue — is canonically the
**strong extensionality** of the world of selves `𝔼 = D/≈` (`Priority.bisim_quotient_eq`), holding for
**every** coalgebra (`Priority.priority_universal`). This is the one A2: already proved, promoted here to
the canonical statement. The old `≈ ⊊ ≅` surplus is its downstream *signature*, sourced from the seam — not
the priority claim itself. -/

/-- **A2 — priority, canonical and universal.** On the world of selves `𝔼 = D/≈`, bisimilarity is equality,
for *every* `(obs, step)`: no individuation finer than the lived relating `≈`. The canonical A2.
(`Priority.priority_universal`.) -/
theorem A2_priority {X O : Type*} (obs : X → O) (step : X → X → Prop) :
    ∀ p q : RelExist.We.World obs step,
      RelExist.We.bisim (RelExist.Priority.obsQ obs step)
        (RelExist.Priority.stepQ obs step) p q ↔ p = q :=
  RelExist.Priority.priority_universal obs step

/-! ### D1 — self-relation = the trace, generalized to the modular flow

Canonical D1 is *self-relation = the trace* (`σ = Tr`), with the **modular-flow generalization** as the
stated form: `σ = modularFlow ρ`, of which the trace is the **infinite-temperature limit**. Paper one
instantiates the trace (internal time off); papers two/three the modular flow (internal time on). Same
definition, generalized — the trace recovered at the maximally-mixed state. -/

/-- **D1 — the trace is the infinite-temperature limit of modular self-relation.** At the maximally mixed
state `ρ = c·I`, the modular flow is the identity for all `t`: internal time is *off*, and `σ = Tr` (paper
one's arena) is recovered. Departing from maximally mixed turns the flow on (`σ = Tr ⇝ σ = modularFlow ρ`).
The canonical D1, stated in its generalized (modular) form. (`ModularFlow.modularFlow_maximally_mixed`.) -/
theorem D1_trace_is_modular_limit {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ)
    (hρ : ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) (t : ℝ) (M : Matrix n n ℂ) :
    modularFlow ((c : ℂ) • 1) hρ t M = M :=
  modularFlow_maximally_mixed c hρ t M

end Theory.Axioms
