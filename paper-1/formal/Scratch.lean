/-
# Scratch — the mathlib-dependent half of paper one

Mathlib-backed formalization, kept out of the default build so the dependency-free core (`RelExist`)
stays fast. Compiling this is what triggers the mathlib build.

This aggregator imports **only the transitive import-closure of paper one's headline theorems**
(see [`docs/spec/paper-one.md`](../docs/spec/paper-one.md)). Everything else — the cosmos/conservation
development (paper two), the sparsity development (paper three), the functorial-semantics layer, and the
route-1 reflexive-object scaffolding — has been moved to [`Archive/`](Archive) (quarantined, not built).
The keep set was computed mechanically as the import closure of the anchor modules, not chosen by hand.

The headline: *the arrow of time is the orientation active self-relating cannot escape; and the
conserved remainder of self-relating — what never becomes known — is exactly energy.*

The kept closure (15 Scratch modules over 5 `RelExist` core modules):

* `Scratch.Trace`            — `σ = Tr` as `gfp` (D1; 03.1).
* `Scratch.We`               — `≈ := νΘ`, the bisimulation gfp (03.2 foundation, imported by knowing).
* `Scratch.KnowingFeeling`   — knowing is the lossy σ-move `E`; the remainder `(1−E)` (03.3).
* `Scratch.MatrixModel` / `Scratch.PartialTrace` / `Scratch.Decoherence` — the ℝ matrix instance and `E`.
* `Scratch.Attending` / `Scratch.SeamForcing` — directed attention and the seam's protection (03.5).
* `Scratch.QuantumSeam` / `Scratch.Orientation` — the irreversible knower→known arrow (03.5).
* `Scratch.TimeFlow`         — knowing ⇒ the graded arrow; that arrow is time (03.8).
* `Scratch.KnowingFromArrow` — the instance converse: an arrow's limit is a knowing (03.10).
* `Scratch.RotatingSpectrum` — energy as the rotating band (03.9).
* `Scratch.BandCoincidence` / `Scratch.BandFromAxioms` — the conserved remainder coincides with energy,
  from A1–A3 (03.15).
* `Scratch.SeamForcingC` — clause A's operational seam re-exhibited over **ℂ**, so the seam, the arrow
  (`Orientation.dephaseKnowingC`), the flow (`TimeFlow.dephaseFlowC`), and the energy band share one
  ℂ model (03.8 two-models note).
* `Scratch.SeamConserved` — **step two, the bridge test**: the operational seam *is* the operationally
  conserved band, exactly and structurally (`offdiag_conserved_iff_seam`); the energy identification stays
  open, with the obstruction named (attention is a 0/1 channel, no rotating spectrum).
* `Scratch.PhaseBearing` — **A3 at the strength of its text**: the self as `Peri(Φ_c)` under a
  phase-bearing `Φ_c`. The phase experiment returns *earned* — the self-inclusion obstruction is
  phase-blind, so the un-attendable seam carries energy (`seam_carries_phase`), the 0/1 gate's
  phaselessness being its degeneracy. Clause B's joint upgraded under two named readings.
* `Scratch.CanonicalEigenform` — **handoff XX, Part D**: paper one's self `Peri(Φ_c)` as a *derived* theorem
  of the canonical A3 *process* (`Theory.Axioms`), not the posited `C1` reading. The state-half mirrored in
  paper one's own namespace from its (byte-identical) definitions; the full process cited + version-pinned
  ([`AXIOM-PROVENANCE.md`](../spec/AXIOM-PROVENANCE.md)). Purely additive — headline footprints untouched.
-/
import Scratch.Trace
import Scratch.KnowingFeeling
import Scratch.TimeFlow
import Scratch.KnowingFromArrow
import Theory.RotatingSpectrum
import Theory.BandFromAxioms
import Scratch.SeamForcingC
import Scratch.SeamConserved
import Scratch.PhaseBearing
import Scratch.CanonicalEigenform
