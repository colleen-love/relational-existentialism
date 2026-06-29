/-
# A3 at the strength of its text — the phase-bearing self, and the phase experiment

A3 names the self an **eigenform sustained by looping — the greatest sustainable field**, which under a
map carrying phase is `Peri(Φ_c) = {X : ‖Φ_c X‖ = ‖X‖}`. The same dropped degree of freedom surfaced
twice in the calibration specs: going *up*, the rotating (energy) band would not fit inside the strict
fixed point `νΦ_c`, forcing the `Align`/C1 concession; going *down*, a phaseless map made the self inert
(a contraction only relaxes onto a fixed point). One fault — **phase** — two reports.

This file rebuilds A3 with the operative self-relating operator **phase-bearing** (`schur μ`:
modulus-contracting, phase-free), promoted from "the energy channel beside attention" to *the* `Φ_c`,
and runs the falsifiable experiment of handoff IX: *does the Lawvere self-inclusion seam carry phase?*

## The result — outcome 1 (earned), with its scope named

**Part A.** `self := Peri(Φ_c)`. The rotating (energy) band sits *inside* the self by construction —
`rotating_mem_peri` — because phase rides free on `‖μ‖ = 1`. So `Peri` carries energy beside the fixed
(known) record; it is not the strict `νΦ_c`.

**Part C — the decisive experiment.** The seam `J` is characterized from **attention / un-attendability**
(`SeamConserved.offdiag_conserved_iff_seam`, `Seam.self_cannot_trace_relation`) — *never* from `‖μ‖`. The
test: is the un-attendable seam confined to the fixed band `{μ = 1}` (phaseless — refutation), or does it
carry phase (`⊆` rotating — energy earned)? The answer is **energy earned**: under a *nondegenerate*
phase-bearing map (`μ = 1 ↔ i = j` — only the diagonal classical record is held), an un-damped
off-diagonal edge necessarily **rotates** (`undamped_offdiag_rotates`), so the un-attendable seam sits in
the rotating energy band (`seam_carries_phase`). The self-inclusion obstruction is **phase-blind**: it
constrains modulus (un-attendable ⟹ un-damped, `‖μ‖ = 1`) but not phase — and off the diagonal the
nondegenerate dynamics has only rotation left to give.

**Part B — subsumption.** The phaselessness of the 0/1 attention gate
(`SeamConserved.attend_fixes_are_identity`: a kept off-diagonal edge has multiplier `1`) was the gate
**violating nondegeneracy** — it *holds* off-diagonal coherence at `1`. That degeneracy, not the
obstruction, made the seam static. The phase-bearing reading of A3 restores nondegeneracy; the gate is
its `θ = 0` restriction (`dephase_no_rotating_peripheral`: the real shadow has empty rotating band).

**Part D — sustained, not grown.** The rotating seam does not decay (`seam_sustained`): it cycles at its
frequencies forever — the self is **non-inert** (A3's "sustained by looping"). Whether looping *enlarges*
`Peri` (makes *more* self) is a separate creation/registration question — `[open]`, flagged not built.

## Honest scope

What is `[proved]` is the **phase-blindness**: the obstruction does not force `θ = 0`, so the
un-attendable seam carries energy under a nondegenerate phase-bearing `Φ_c`. What stays `[reading]` are
the two modeling inputs this rests on — **the Lindblad reading** `seam_undamped` (the dissipator *is*
attention, so un-attendable ⟹ un-damped) and **nondegeneracy** `fixed_eq_diagonal` (A3-at-strength: only
the diagonal record is held). Clause B's joint thus moves from `[open]` (the spec-VIII cross-channel
posit) to `[proved] under those two named readings` — and it needs **no** `Align`: `seam_carries_phase`
is the one-directional `seamBand ⊆ rotatingBand`, exactly what "the conserved remainder *is* energy"
asserts. The exact set-equality `seam = rotatingBand` (the converse) still needs `Align`, but clause B
does not.
-/
import Theory.BandFromAxioms
import Scratch.SeamConserved

namespace RelExist.PhaseBearing

open Theory.BandCoincidence Theory.BandFromAxioms Theory.RotatingSpectrum
open Matrix

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## Part A — the self is `Peri(Φ_c)`, and energy sits inside it -/

omit [Fintype A] [DecidableEq A] in
/-- The rotating (energy) band is contained in the conserved band: a rotating edge (`‖μ‖ = 1, μ ≠ 1`)
is in particular conserved (`‖μ‖ = 1`). -/
theorem rotatingBand_le_conservedBand (μ : A → A → ℂ) : rotatingBand μ ≤ conservedBand μ :=
  bandOn_mono (fun _ _ hr => hr.1)

omit [Fintype A] [DecidableEq A] in
/-- **Energy sits inside the self.** `self := Peri(Φ_c)`; every rotating (energy) coherence is in `Peri`
— magnitude-preserved under one loop — because phase rides free on `‖μ‖ = 1`. So the self carries the
rotating energy band *beside* the fixed (known) record; A3's "sustainable field" is not the strict
`νΦ_c`. -/
theorem rotating_mem_peri {μ : A → A → ℂ} {M : Matrix A A ℂ} (hM : M ∈ rotatingBand μ) :
    Peri μ M :=
  (peri_iff_mem_conservedBand μ M).2 (rotatingBand_le_conservedBand μ hM)

/-! ## Part C — the experiment: does the un-attendable seam carry phase? -/

omit [Fintype A] [DecidableEq A] in
/-- **Phase rides free on an un-damped off-diagonal edge — the per-edge heart.** Under a *nondegenerate*
phase-bearing map (`μ = 1 ↔ i = j`: only the diagonal is held), an un-damped (`‖μ‖ = 1`) off-diagonal
edge necessarily **rotates** (`μ ≠ 1`). Damping fixes modulus; nondegeneracy forbids *holding*
off-diagonal coherence at `1`; so an un-damped off-diagonal edge has nowhere to be but the rotating band.
The seam is given by attention (no `‖μ‖`); this lemma adds only that the dynamics is nondegenerate. -/
theorem undamped_offdiag_rotates {μ : A → A → ℂ} (hnd : ∀ i j, μ i j = 1 ↔ i = j)
    {i j : A} (hund : ‖μ i j‖ = 1) (hij : i ≠ j) : rotatingEdge μ i j :=
  ⟨hund, fun h1 => hij ((hnd i j).mp h1)⟩

omit [Fintype A] [DecidableEq A] in
/-- **The experiment's answer: the un-attendable seam carries phase = energy.** With the seam `J` given
by attention, the Lindblad reading that it is un-damped (`UnitaryBaseline.seam_undamped`), and the
nondegenerate phase-bearing dynamics (`UnitaryBaseline.fixed_eq_diagonal`), the seam sits inside the
rotating energy band. This re-exports `BandCoincidence.seamBand_subset_rotating` under the
phase-experiment framing: the self-inclusion obstruction is **phase-blind** — it constrains modulus
(un-attendable ⟹ un-damped) but the phase is whatever the nondegenerate dynamics carries, and off the
diagonal that is rotation. *Refutation (seam confined to `{μ = 1}`) is false.* -/
theorem seam_carries_phase {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (hoff : SeamOffdiagonal J) :
    seamBand J ≤ rotatingBand μ :=
  seamBand_subset_rotating hb hoff

/-- **The witness — a nondegenerate phase-bearing self whose attention-seam is energy.** `quarterMul`
(diagonal `1`; `(0,1) = i`, `(1,0) = −i` rotating; else `1/2` transient) is nondegenerate
(`quarterMul_fixed_eq_diagonal`), and the seam `Jq` — the index pairs `(0,1), (1,0)`, a **combinatorial**
block carrying no `‖μ‖` — is un-damped and off-diagonal, so it sits inside the rotating energy band. The
seam carries phase, concretely. -/
theorem quarterMul_seam_carries_phase : seamBand Jq ≤ rotatingBand quarterMul :=
  seam_carries_phase quarterMul_unitaryBaseline quarterMul_seamOffdiagonal

/-! ## Part D — sustained, not grown -/

omit [Fintype A] [DecidableEq A] in
/-- **The phase-bearing self is non-inert (sustained by looping).** Every coherence of the un-attendable
seam keeps its magnitude at *every* depth — `‖Φ^n M i j‖ = ‖M i j‖` — so the rotating seam does not
decay; it cycles at its frequencies forever, A3's "sustained by looping," not the static fixed point a
contraction relaxes onto. *Grown* — whether looping enlarges `Peri` (makes more self) — is a separate
creation/registration question (unitary rotation preserves `Peri`, it does not grow it); it is `[open]`,
flagged, not built here. -/
theorem seam_sustained {μ : A → A → ℂ} {J : A → A → Prop}
    (hb : UnitaryBaseline μ J) (hoff : SeamOffdiagonal J)
    {M : Matrix A A ℂ} (hM : M ∈ seamBand J) (n : ℕ) (i j : A) :
    ‖(schur μ)^[n] M i j‖ = ‖M i j‖ :=
  rotatingBand_sustained (seam_carries_phase hb hoff hM) n i j

end RelExist.PhaseBearing
