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
-/
import Scratch.Trace
import Scratch.KnowingFeeling
import Scratch.TimeFlow
import Scratch.KnowingFromArrow
import Scratch.RotatingSpectrum
import Scratch.BandFromAxioms
