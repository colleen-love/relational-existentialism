/-
# Paper one's eigenform, as a *derived* theorem of the A3 process (handoff XX, Part D)

Handoff XX reframes **A3 as a process** — *relations co-direct attention asymmetrically in the relata* — and
derives the per-paper *readings* of the self as theorems of that one process, canonically in
[`theory/Theory/Axioms.lean`](../../../theory/formal/Theory/Axioms.lean) (`Theory.Axioms`). Paper one is
*opened* by that move: its self `νΦ_c` / `Peri(Φ_c)` was previously **A3 read at the strength of its text**
(the `C1` reading — "the self *is* `Peri`"); under the reframe it is the **fixed point of a faithful A3
process**, *derived*.

This module records that improvement **inside paper one's own closure**, so paper one carries the eigenform
as a derived theorem rather than a posit:

> **`eigenform_of_sustained`** : a state the channel `Φ_c = schur μ` returns unchanged (`Sustained`, the
> state-half of the canonical `Theory.Axioms.IsSelf` = `MutualCoupling.JointFixed`) lies in A3's sustainable
> field `Peri(Φ_c)`. The eigenform is the fixed point of the process, not a separate posit.

## Update (handoff XXI): the collision is gone — this module is now redundant

When this was written (spec XX), a *direct* `import Theory.Axioms` into paper one was **namespace-blocked**:
the `theory/` band forks shared paper one's `RelExist.*` names, so importing both collided. The proof-DAG
reorg **dissolved that block** — it promoted the band layer into clean `Theory.*` and paper one now imports
`Theory.BandFromAxioms` directly (this very file does). So paper one **could** now simply
`import Theory.Axioms` and use `Theory.Axioms.eigenform_of_fixed`, making this local mirror **redundant**. It
is kept for now to preserve the green+footprint baseline across the reorg; deleting it (and importing
`Theory.Axioms` directly) is a flagged follow-up. The state-half re-proved below is identical to the
canonical `Theory.Axioms.eigenform_of_fixed`; the full process lives in `Theory.Axioms`.
-/
import Theory.BandFromAxioms

namespace RelExist.CanonicalEigenform

open Theory.RotatingSpectrum Theory.BandCoincidence Theory.BandFromAxioms
open Matrix

variable {A : Type*}

/-- **Sustained** — the state-half of a self. `M` is sustained when the co-directed attention channel
`Φ_c = schur μ` returns it unchanged: `schur μ M = M`. This is exactly the state condition of the canonical
A3-process fixed point `Theory.Axioms.IsSelf` (`MutualCoupling.JointFixed`) — the strict fixed point `νΦ_c`,
the looped relations returned identically. -/
def Sustained (μ : A → A → ℂ) (M : Matrix A A ℂ) : Prop := ∀ i j, schur μ M i j = M i j

/-- **The eigenform is derived, not posited.** A sustained state lies in A3's sustainable field
`Peri(Φ_c)`: returned unchanged ⟹ returned unchanged *in magnitude*. Paper one's "self `:= Peri`" (the `C1`
reading) is thus a **theorem** of the A3 process, mirroring `Theory.Axioms.eigenform_of_fixed` in paper
one's own namespace. -/
theorem eigenform_of_sustained {μ : A → A → ℂ} {M : Matrix A A ℂ} (h : Sustained μ M) :
    Peri μ M :=
  fun i j => by rw [h i j]

/-- **The sustained self sits in the conserved band.** Combining `eigenform_of_sustained` with
`peri_iff_mem_conservedBand`: a sustained state lives in the conserved (modulus-one) band — the
undifferentiated ground that carries the rotating (energy) band beside the fixed (`νΦ_c`, knowing) record.
The paper-one eigenform structure, derived from the process. -/
theorem sustained_mem_conservedBand {μ : A → A → ℂ} {M : Matrix A A ℂ} (h : Sustained μ M) :
    M ∈ conservedBand μ :=
  (peri_iff_mem_conservedBand μ M).1 (eigenform_of_sustained h)

/-- **The energy band is inside the self** (the phase-bearing reading, recorded locally). The rotating
(energy) band lies inside the conserved band `Peri(Φ_c)`, so the self carries energy beside the knowing
record — `νΦ_c` is one half, the rotating band the other. (Mirrors `Theory.Axioms.energy_in_self`; the same
fact `PhaseBearing.rotating_mem_peri` already uses.) -/
theorem energy_in_self (μ : A → A → ℂ) : rotatingBand μ ≤ conservedBand μ :=
  bandOn_mono (fun _ _ hr => hr.1)

end RelExist.CanonicalEigenform
