# Paper one — the arrow of self-relating, and its conserved remainder

> **The result, in one sentence.** *The arrow of time is the orientation active self-relating cannot
> escape; and the conserved remainder of self-relating — what never becomes known — is exactly energy.*
>
> *Status of that sentence.* It is **not** itself one `[proved]` badge. The proved skeleton (below) is
> `[proved]`; the *time* and *energy* identifications are `[reading]`s; the **operational-seam ↔
> energy-band joint** is `[open]`.

> **Proved skeleton `[proved]`.** A lossy self-relating projection forces a structural remainder, orders
> an irreversible arrow, and conserves exactly its `genReal = 0` band — on a genuine CPTP witness. That
> much is mechanized, `sorry`-free; everything the headline says *beyond* it is a named reading or a named
> open joint, below.

> **The headline rests on:** **A1–A3**, **B1** (the preferred/"classical" basis; einselection `[open]`),
> **C1** (self = `Peri(Φ_c)`, §5 — an identification *beyond* A3's formalized `νΦ_c`), and the readings
> *flow = physical time* / *`Φ_c` = the actual decohering physics*; with the operational-seam ↔
> energy-band joint `[open]`. Only A1–A3 are foregrounded as the doctrine's wager (`02`); **B1 and C1 are
> load-bearing for the energy half (§5) specifically**, and are named here so the premise count sits beside
> the claim rather than three files away.

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
structural, A3 (recursion constitutes the self) the one load-bearing posit. The matrix model also makes one
standing **assumption**, **B1** — a *preferred ("classical") basis* fixing what counts as diagonal/known vs
off-diagonal/felt; the arrow, the knowing/feeling split, and the bands are all relative to it (deriving it
by einselection is `[open]`). A note on the `[proved, 0 ax]` badge: the axiom-free results below (the seam,
the limits of knowing) *are* Lawvere's diagonal and nothing more — their **force as claims about selves**
rests on the `[reading]`s of their hypotheses (that the lossy restriction *is* self-inclusion, that the
trace agent *is* the actual forgetting). The badge certifies the mathematics; the readings carry the
philosophy.

---

## 1. Relation first; self-relation is the trace `[proved]`

The simplest relation is a system relating to itself: feedback, output returned to input. **D1** fixes
this as the trace, `σ := Tr` ([`02-axioms.md`](02-axioms.md)). Over the order-theoretic arena it is the
greatest fixed point of the self-relating map — *relating produces an eigenform*, theorem **3.1**:
`Trace.selfTrace_fixed` / `Trace.Tr_fixed` (`Scratch/Trace.lean`, the `gfp` of an `OrderHom`). What is
mechanized here is exactly **gfp-existence** (Knaster–Tarski) — generic to any monotone map; that the
created selves are *rare* (the discriminating content that keeps this from being a universal solvent) is
paper three's sparsity, **not** claimed in this step. Identity itself is the greatest bisimulation
`≈ := νΘ` (theorem **3.2**, `We.bisim`, `Scratch/We.lean`): you are your lived relating, not a bare carrier
beneath it. (What the headline path actually uses is *only* this `≈ = νΘ` — the kept `We.bisim`. The
soundness/strictness inversion `≈ ⊆ ≅ ⊊` is **not** load-bearing here: it is mechanized only in archived
`Identity.lean`, as paper-two material, and the seam→arrow→energy spine references no `obsEq` at all. An
earlier draft called the soundness `≈ ⊆ ≅` load-bearing here; that was a mis-scoping, corrected.)

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
**That arrow is time** `[reading]`. On the genuine instance the converse also holds — an arrow's limit
*is* a knowing, an idempotent conditional expectation onto the seam subalgebra
(`KnowingFromArrow.arrow_limit_is_knowing`, `limit_is_seam_CE`, `Scratch/KnowingFromArrow.lean`). This is
the *instance* converse (a re-export of the forward `partialDephase` limit); the **general** lift
(arrow ⇒ knowing for any contractive arrow) is Conjecture R, `[open]` — see [Honest scope](#honest-scope) ¶1.

→ detail: [`03.6-time-flow.md`](03.6-time-flow.md),
[`03.7-knowing-from-arrow.md`](03.7-knowing-from-arrow.md).

## 5. The conserved remainder is exactly energy — `[proved]` (`genReal = 0`, on the witness) · `[reading]` (= energy) · `[open]` (the joint)

> **What carries which tag here.** `[proved]`: that the `genReal = 0` band is conserved *exactly* (magnitude
> held), on the genuine CPTP witness. `[reading]`: that this conserved band *is* energy (the unitary
> spectrum of the time generator, given flow = time). `[open]`: that the conserved band is the **operational**
> seam of §3 — the un-attendable, self-inclusion-forced block — i.e. the operational-seam ↔ energy-band
> joint. The bare `[proved]` that once tagged this whole section overreached; this is the split.

Not all of the remainder behaves alike. Over ℂ the dynamics is the phase-damping channel `schur μ`, and
each off-diagonal coherence falls in one of two bands by `‖μ i j‖`:

- **transient** (`‖μ i j‖ < 1`) — it **decays to zero**; it *becomes known*, dissipated by the arrow
  (`RotatingSpectrum.schur_transient_tendsto`, `BandFromAxioms.transient_decays`). This is neither knowing
  nor energy.
- **conserved / rotating** (`‖μ i j‖ = 1, μ i j ≠ 1`) — its magnitude is **exactly sustained** at every
  depth; it rotates forever and never collapses into the known
  (`RotatingSpectrum.schur_sustained`, `phaseChannel_eigen`; `BandFromAxioms.conservedBand_sustained`).
  This sustained, never-known remainder **is energy** — and energy here is **not a second analogy**. The
  dynamics carries one generator `L = log Φ_c`, split entrywise into `genReal = Re(log μ) = log‖μ‖` (the
  decay rate) and `genImag = Im(log μ) = arg μ` (the frequency). The single iterate-magnitude law
  `‖Φ^n M i j‖ = exp(n · genReal)·‖M i j‖` (`RotatingSpectrum.schur_iterate_norm_exp`) makes the split
  **exact**: the **arrow** is `genReal < 0` (decay, clause A; `arrow_of_genReal_neg`), the **conserved
  band** is `genReal = 0` — magnitude held *exactly*, not merely floored
  (`conserved_of_genReal_zero`, `genReal_eq_zero_iff`) — and on that band `L` is purely imaginary, so
  **energy is its imaginary spectrum** `energy := genImag` on `ker(genReal)` (`energyEdge`, `energy`;
  `energy_quarterMul_01 = π/2`). Arrow and energy are the real and imaginary parts of *one* generator, so
  energy is **downstream of the single time reading** (flow = the generator of time-translation), not an
  independent posit — its name is Noether/Stone, the conserved charge of the unitary part, not the `i^n`
  winding. On the witness the generator band is exactly the rotating/energy band
  (`BandFromAxioms.energyBand_eq_rotating_quarterMul`).

That the conserved remainder coincides with the rotating/energy band turns on **one identification, C1**:
that the self *is* A3's *"greatest sustainable field"* `Peri(Φ_c) = { X : ‖Φ_c X‖ = ‖X‖ }`, not the strict
`νΦ_c` the axiom formalizes. That field is now mechanized as **exactly** the conserved (modulus-one) band
(`BandFromAxioms.peri_iff_mem_conservedBand`), *including* the rotating band, with the seam its off-diagonal
part (`decoherenceFreeSeam_iff_offdiag_conserved`) and `νΦ_c` (the known/diagonal record) its `μ = 1`
sub-band (`fixedBand_le_conservedBand`). With the seam *so read*, and given only that the channel is
contractive (attention never amplifies) and nondegenerate, the alignment is a one-line consequence
(`BandFromAxioms.align_of_contractive`, `band_coincidence_from_axioms`) and the seam-protection is
phase-blind — it covers the energy band exactly as the known record (`BandFromAxioms.seam_energy_sustained`).
But note what carries the weight: `align_of_contractive` is a near-tautology once the seam is *defined* as
the modulus-one off-diagonal block; **all** the content sits in C1. **C1 is a disclosed `[reading]`/posit** —
the self = `Peri(Φ_c)`, an identification *beyond* A3's formalized `νΦ_c` (which carries only the fixed
band). We read it as A3's "decoherence-free subalgebra" gloss made precise; a reader may instead count it as
a fourth posit. Either way it is named and tagged here, and the reader judges. The further identification of
this conserved band with **energy** is itself a standing `[reading]` (below).

**What clause B rests on — and what it does not.** Clause B rests on **A3-read-as-`Peri`** (exact
magnitude conservation, `genReal = 0`) plus the generator split — **not** on the operational seam.
`band_coincidence` relates the *spectral* seam `decoherenceFreeSeam` (defined by `‖μ‖ = 1`) to the
rotating band; it does **not** connect the *operational*, un-attendable seam of
`SeamForcing.self_cannot_fully_decohere` to the energy band. Those are two kinds of "conserved":
`Peri`/`genReal = 0` is **exact** (the magnitude is held), while the operational seam gives only a
**positive floor** (the coherence never fully vanishes — a clause-A fact, the arrow never completing).
The identification *operational seam = energy band* is the **open unifier**, stated and not proved; the
energy clause does not borrow the seam's `[proved, 0 ax]` weight.

**A model note — the mismatch removed, the joint still open.** The operational seam was first exhibited
over `Matrix A A ℝ` (`SeamForcing.self_cannot_fully_decohere`), while the energy/rotating band lives over
ℂ — and the real self-adjoint model *provably carries no rotating band*
(`RotatingSpectrum`/`dephase_no_rotating_peripheral`); energy appears only after extending to ℂ. So the
two clauses once sat in **different, at-the-relevant-point mutually exclusive** models, joined across an
unmechanized gap. That mismatch is now gone: `SeamForcing.self_cannot_fully_decohereC`
(`Scratch/SeamForcingC.lean`) re-exhibits the operational seam **over ℂ** (the same positivity argument —
attention cannot aim at the aimer — with the squared modulus `‖·‖²` in place of the square), so **both
clauses now live in one ℂ model**. This does **not** prove the joint — whether that un-attendable block
*is* the rotating band is still the open unifier — it only **co-locates** the two, leaving the joint as the
single remaining gap rather than a gap-plus-a-model-mismatch.

→ detail: [`03.8-space-energy.md`](03.8-space-energy.md),
[`03.9-band-coincidence.md`](03.9-band-coincidence.md).

## 6. The headline

> **The arrow of time is the orientation active self-relating cannot escape (§3–4); and what
> self-relating *conserves* beyond the known — the sustained, never-collapsing remainder — is exactly
> energy (§5).** The transient remainder decays into the known (the arrow); the conserved remainder does
> not, and that conserved remainder is the energy band.

Every *mechanized* step is `[proved]`, `sorry`-free; the headline footprints sit at the corpus norm
`[propext, Classical.choice, Quot.sound]`, with the seam (`Seam.self_cannot_trace_relation`) depending on
**no axioms**. What is **not** `[proved]` is named, not buried: the *energy* identification and *flow =
time* are `[reading]`s, and the operational-seam ↔ energy-band joint is `[open]` (§5, Honest scope). The
proved skeleton stated under the headline is the part that carries the badge.

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
   subalgebra" gloss — the self = `Peri(Φ_c)`, an identification *beyond* A3's formalized `νΦ_c` (which
   carries only the fixed band). This is a **disclosed `[reading]`/posit**, asserted, not derived: we read
   it as A3's gloss made precise; a reader may count it as a fourth posit. Either way it is named and tagged
   (see [`03.9`](03.9-band-coincidence.md) postscript). We no longer argue it "adds no fourth axiom" — we
   disclose it and let the reader judge.

And **one standing reading-cluster** — *flow = physical time / `Φ_c` = the actual decohering physics*. With
it, **energy is not a second reading**: the generator of the flow is the Hamiltonian, the arrow is its
dissipative part (`genReal < 0`) and energy its unitary spectrum (`genImag` on `ker genReal`), so "the
conserved band = energy" follows by the definition of energy as the conserved charge of time-translation
(Noether/Stone), not by a fresh analogy. What stays genuinely open beside it is the **unifier** —
*operational seam = energy band* — relating the un-attendable seam (`SeamForcing`, a positive floor) to the
exactly-conserved generator band (`genReal = 0`); these are two senses of "conserved," kept apart. (The two
were also exhibited in *different models* — the operational seam over `Matrix A A ℝ`, the energy band over
ℂ, with the real self-adjoint model carrying **no** rotating band; `SeamForcing.self_cannot_fully_decohereC`
now re-exhibits the operational seam over ℂ, so the unifier is the **only** remaining gap, not a gap plus a
model mismatch.) Strip the reading and what remains is the proved skeleton: a lossy self-relating projection
forces a structural remainder, orders an irreversible arrow, and conserves exactly its rotating
(`genReal = 0`) band, whose imaginary spectrum is energy.

## What is not in this paper

The conservation law as a *whole* (`undifferentiated = knowing + energy`, the internal direct sum), the
cosmos / distributed-self readings, the sparsity of selfhood, and the functorial-semantics layer are all
mechanized but belong to later papers; they are archived (see
[`formal/Archive/README.md`](../../formal/Archive/README.md)) and **not** load-bearing here. This paper
says one thing and shows its work.

---

→ Foundation: [`00-doctrine.md`](00-doctrine.md) · [`01-signature.md`](01-signature.md) ·
[`02-axioms.md`](02-axioms.md). Provenance: [`04-provenance.md`](04-provenance.md).
