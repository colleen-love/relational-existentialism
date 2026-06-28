# Paper one — the arrow of self-relating, and its conserved remainder

> **The result, in one sentence.** *The arrow of time is the orientation active self-relating cannot
> escape; and the conserved remainder of self-relating — what never becomes known — is exactly energy.*

This page is the single linear walk through that result: each step is tagged with its status and named by
the Lean theorem that carries it. A referee should be able to see the arc *and* its boundary in one read.
The supporting development lives in [`formal/`](../../formal) (libraries `RelExist` — the
dependency-free core — and `Scratch` — the mathlib-backed half); everything not load-bearing for this
result has been moved to [`Archive/`](../../formal/Archive) and [`docs/archive/`](../archive), referenced
below as future work, never as a load-bearing citation.

**Status legend.** `[proved]` — mechanized, `sorry`-free (footprint reported); `[proved, 0 ax]` — and
depending on *no* axioms; `[reading]` — an identification of the formal object with the lived/physical
one, asserted, not proved; `[open]` — named and not built. The foundation A1–A3 / D1 is in
[`02-axioms.md`](02-axioms.md); A1 (the traced symmetric monoidal arena) and A2 (relation primacy) are
structural, A3 (recursion constitutes the self) the one load-bearing posit.

---

## 1. Relation first; self-relation is the trace `[proved]`

The simplest relation is a system relating to itself: feedback, output returned to input. **D1** fixes
this as the trace, `σ := Tr` ([`02-axioms.md`](02-axioms.md)). Over the order-theoretic arena it is the
greatest fixed point of the self-relating map — *relating produces an eigenform*, theorem **3.1**:
`Trace.selfTrace_fixed` / `Trace.Tr_fixed` (`Scratch/Trace.lean`, the `gfp` of an `OrderHom`). Identity
itself is the greatest bisimulation `≈ := νΘ` (theorem **3.2**, `We.bisim`, `Scratch/We.lean`): you are
your lived relating, not a bare carrier beneath it.

→ detail: [`03.1-to-relate-is-to-create.md`](03.1-to-relate-is-to-create.md),
[`03.2-lived-identity.md`](03.2-lived-identity.md).

## 2. Knowing is the σ-move: a lossy projection, leaving a remainder `[proved]`

To *know* a relation is to objectify it — the σ-move. Mechanized as **Lawvere's diagonal**: no system
carries a complete self-model whose every row is a fixed-point-free map, `Mirror.lawvere` /
`Mirror.no_complete_selfModel` (`RelExist/Mirror.lean`), and what escapes the model is a genuine
**remainder**, `Mirror.selfModel_remainder`. On the matrix instance knowing is the decoherence projection
`E = dephase`: it keeps the classical diagonal and kills off-diagonal coherence, splitting every relation
into a **known** part `E M` and a **felt** remainder `(1−E) M` (`Scratch/Decoherence.lean`,
`Scratch/KnowingFeeling.lean`; `feeling_is_reflexive`, `no_complete_boolModel`). **Throughout, "feeling"
means exactly this `(1−E)` remainder of self-relating** — nothing phenomenal is claimed of it.

→ detail: [`03.3-knowing-vs-feeling.md`](03.3-knowing-vs-feeling.md).

## 3. The seam: the remainder is structural, not incidental `[proved, 0 ax]`

The remainder is not an artefact of a weak model — it is forced. A self **cannot completely trace what
includes it**: the account it would need is a fixed-point-free self-map of its own view, which Lawvere
bars. `Seam.self_cannot_trace_relation` (`RelExist/Seam.lean`) **depends on no axioms**;
`SeamBridge.no_faithful_self_trace` / `seam_on_forgetting` (`RelExist/SeamBridge.lean`) tie it to the
lossy forgetting, and `Relating.self_inclusive_unmodelable` / `related_other_unmodelable`
(`RelExist/Relating.lean`) locate the un-knowable block: the part of you that is the relating itself. On
the matrix instance this block is **un-attendable** — directed attention cannot aim at the aimer — so its
coherence survives every available knowing and the copy-defect never reaches zero
(`Attending.defectSq_attend_shared_pos`, `SeamForcing.self_cannot_fully_decohere`). This block is the
**seam**.

→ detail: [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md),
[`03.5-decoherence.md`](03.5-decoherence.md).

## 4. The arrow: knowing orders felt-before-known and cannot run back `[proved]`

Because knowing is a *lossy* projection, it imposes a direction. `E` orders states felt-before-known
antisymmetrically (`Orientation.Knowing.knows_antisymm`); the induced arrow strictly lowers coherence
(`Orientation.Knowing.arrow_strictAnti`) and, once lossy, **cannot be recovered** —
`Orientation.Knowing.no_recovery` (`Scratch/Orientation.lean`). Iterated, this is a graded geometric
monovariant: coherence is antitone along the orbit and tends to zero off the fixed set
(`TimeFlow.coh_orbit_antitone`, `coh_orbit_strictAnti`, `coh_orbit_tendsto_zero`, `Scratch/TimeFlow.lean`).
**That arrow is time** `[reading]`. On the genuine instance it runs *both ways*: an arrow's limit *is* a
knowing — an idempotent conditional expectation onto the seam subalgebra
(`KnowingFromArrow.arrow_limit_is_knowing`, `limit_is_seam_CE`, `Scratch/KnowingFromArrow.lean`).

→ detail: [`03.6-time-flow.md`](03.6-time-flow.md),
[`03.7-knowing-from-arrow.md`](03.7-knowing-from-arrow.md).

## 5. The conserved remainder is exactly energy `[proved]`

Not all of the remainder behaves alike. Over ℂ the dynamics is the phase-damping channel `schur μ`, and
each off-diagonal coherence falls in one of two bands by `‖μ i j‖`:

- **transient** (`‖μ i j‖ < 1`) — it **decays to zero**; it *becomes known*, dissipated by the arrow
  (`RotatingSpectrum.schur_transient_tendsto`, `BandFromAxioms.transient_decays`). This is neither knowing
  nor energy.
- **conserved / rotating** (`‖μ i j‖ = 1, μ i j ≠ 1`) — its magnitude is **exactly sustained** at every
  depth; it rotates forever and never collapses into the known
  (`RotatingSpectrum.schur_sustained`, `phaseChannel_eigen`; `BandFromAxioms.conservedBand_sustained`).
  This sustained, never-known remainder **is energy** `[reading]` — the conserved oscillating charge,
  `energy_arrow_spectrum` reading it off one generator's spectrum.

That the conserved remainder coincides with the rotating/energy band is a **theorem of A1–A3**, not a
fourth posit: taking the seam to be A3's own "decoherence-free subalgebra" gloss, and given only that the
channel is contractive (attention never amplifies) and nondegenerate, the alignment is forced
(`BandFromAxioms.align_of_contractive`, `band_coincidence_from_axioms`), and the protection is
phase-blind — it covers the energy band exactly as it covers the known record
(`BandFromAxioms.seam_energy_sustained`).

→ detail: [`03.8-space-energy.md`](03.8-space-energy.md),
[`03.9-band-coincidence.md`](03.9-band-coincidence.md).

## 6. The headline

> **The arrow of time is the orientation active self-relating cannot escape (§3–4); and what
> self-relating *conserves* beyond the known — the sustained, never-collapsing remainder — is exactly
> energy (§5).** The transient remainder decays into the known (the arrow); the conserved remainder does
> not, and that conserved remainder is the energy band.

All steps are `[proved]`, `sorry`-free; the headline footprints sit at the corpus norm
`[propext, Classical.choice, Quot.sound]`, with the seam (`Seam.self_cannot_trace_relation`) depending on
**no axioms**.

---

## Honest scope

Three frontiers stay open, stated plainly rather than buried:

1. **Conjecture R — the general converse `arrow ⇒ knowing`.** Paper one uses the *instance* converse
   (`arrow_limit_is_knowing`, §4). The general mean-ergodic lift is `[open]`
   (archived `Scratch/MeanErgodic.lean`); the headline does not depend on it.
2. **The general-CPTP placement of `Φ_c`'s spectrum.** That an arbitrary primitive channel places its
   modulus-1 spectrum into a commutative decoherence-free subalgebra is `[open]`; §5 discharges the
   coincidence on the finite-dim ℂ witness, not in general.
3. **C1 — that the self is `Peri(Φ_c)`.** The coincidence reads the seam as A3's "decoherence-free
   subalgebra" gloss. This is A3 *taken literally*, asserted — **not a fourth axiom**, but a `[reading]`
   of A3, not a derivation of it (see [`03.9`](03.9-band-coincidence.md) postscript).

And three standing **readings** — identifications the development asserts but does not prove: *flow =
physical time* (§4), *the conserved modulus-1 band = energy* (§5), and *`Φ_c` = the actual decohering
physics*. Strip the readings and what remains is the proved skeleton: a lossy self-relating projection
forces a structural remainder, orders an irreversible arrow, and conserves exactly its rotating band.

## What is not in this paper

The conservation law as a *whole* (`undifferentiated = knowing + energy`, the internal direct sum), the
cosmos / distributed-self readings, the sparsity of selfhood, and the functorial-semantics layer are all
mechanized but belong to later papers; they are archived (see
[`formal/Archive/README.md`](../../formal/Archive/README.md)) and **not** load-bearing here. This paper
says one thing and shows its work.

---

→ Foundation: [`00-doctrine.md`](00-doctrine.md) · [`01-signature.md`](01-signature.md) ·
[`02-axioms.md`](02-axioms.md). Provenance: [`04-provenance.md`](04-provenance.md).
