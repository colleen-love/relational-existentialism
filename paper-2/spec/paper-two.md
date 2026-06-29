# Paper two — self-relation is modular flow, and time's two faces are one generator

> **The result, in one sentence.** *The intrinsic dynamics a state induces on its own relations is the
> modular flow; the trace `σ = Tr` is its infinite-temperature (timeless) limit; energy is the modular
> Hamiltonian; and the reversible modular clock and the irreversible dissipative arrow are — at equilibrium —
> **two faces of one generator**, from which a conserved **presence** splits into knowing and energy.*
>
> *Status of that sentence.* It is **not** one `[proved]` badge. The modular skeleton (flow, trace-limit,
> energy = `spec(K)`, KMS, reversibility) is `[proved]`; the *thermal time* identification is a `[reading]`;
> **"two faces of one generator"** and **"presence = knowing + energy"** are `[proved, at equilibrium]` under
> two named conditions — **KMS-equilibrium** and the **alignment** `B1 = eigenbasis(ρ)` (itself now *derived*
> from a rest-state principle, not assumed); the *out-of-equilibrium* identification (modular time = physical
> time in general) stays the inherited Connes–Rovelli `[open]`.

> **Proved skeleton `[proved]`.** For a matrix algebra `Mₙ(ℂ)` with a faithful state `ρ`: the modular flow is
> a one-parameter group of \*-automorphisms with self-adjoint generator `K = -log ρ`; the trace is its
> maximally-mixed limit; the flow is reversible (no arrow); at Gibbs equilibrium the modular and dissipative
> parts assemble into a single GKLS generator whose faces commute, and the conserved-band weight (presence) is
> invariant and splits Pythagoreanly. All `sorry`-free; footprints `[propext, Classical.choice, Quot.sound]`.

> **The headline rests on:** the **modular reading of A1** (the finite, type I, maximally-traceable arena of
> [`02-axioms.md`](../../theory/spec/AXIOMS.md) read at its deep end — the intrinsic dynamics a state
> induces); the **equilibrium / KMS** condition (`ρ = e^{-βH}/Z`); the **alignment** `B1 = eigenbasis(ρ)` —
> the decoherence/pointer basis is the state's eigenbasis, now **derived** from "the clock-state is the
> rest-state" (§6), not posited; and the **cited** arrow result of paper one (the seam as the
> un-decohereable floor that *orders* the arrow — `SeamForcing`, honored in prose, §3, not imported). Only the
> first is the doctrine's wager; the KMS and alignment conditions are load-bearing for the equilibrium
> headline specifically, named here so the premises sit beside the claim.

This page is the single linear walk through that result: each step is tagged with its status and named by the
Lean theorem that carries it; a referee should see the arc *and* its boundary in one read. The development is
the frozen fork [`paper-2/formal/`](../formal) (library `Paper2`, six modules, forked from `theory/` at
`fca792d` — [`04-provenance.md`](04-provenance.md)). The type III program the finite core stops short of
is scoped in [`theory/spec/modular-frontier.md`](../../theory/spec/modular-frontier.md).

**Status legend.** `[proved]` — mechanized, `sorry`-free (footprint reported); `[proved, at equilibrium]` —
mechanized, under the named KMS + alignment conditions; `[reading]` — an identification of the formal object
with the lived/physical one, asserted, not proved; `[open]` — named and not built.

---

## 1. Relation induces a flow; the trace is its timeless degeneracy `[proved]`

Paper one fixed self-relation as the trace `σ := Tr` (**D1**), the regime where internal time is *off*. Read
at the strength of A1's text, self-relation is the **intrinsic dynamics a state `ρ` induces** — at the deep
end the **modular flow** of Tomita–Takesaki. For `Mₙ(ℂ)` with a faithful density matrix this exists now,
finite-dimensionally and `sorry`-free: `σ_t(M) = ρ^{it} M ρ^{-it}` is a one-parameter group of unital
\*-automorphisms (`modularFlow`, with `modularFlow_add`, `modularFlow_mul`, `modularFlow_star`), and `ρ^{it}`
is the spectral exponential (`modPow`, group law `modPow_mul`). **D1 is its timeless limit:** at the
maximally-mixed `ρ = c·I` the flow is the identity for all `t` (`modularFlow_maximally_mixed`) — *internal
time is off*. So `σ = Tr` is the infinite-temperature limit of modular self-relation; departing from
maximally-mixed turns the flow on.

→ [`Paper2.ModularFlow`](../../theory/formal/Theory/ModularFlow.lean).

## 2. The trace as infinite-temperature time — the bridge to paper one `[proved]`

This is the clean retroactive justification of paper one's choice. Paper one worked at `σ = Tr`; here that is
exactly the `β → 0` (infinite-temperature) face of the modular flow (`modularFlow_maximally_mixed`,
`modPow_scalar`). Paper one was not making an arbitrary modelling choice — it was working at the timeless
degeneracy of a structure whose general form *is* time. Lead with this: the modular paper does not overturn
paper one, it locates it.

→ [`Paper2.ModularFlow`](../../theory/formal/Theory/ModularFlow.lean).

## 3. Energy is the modular Hamiltonian; the arrow is what the flow cannot supply `[proved]` / `[reading]`

The Stone generator of the modular flow is the **modular Hamiltonian** `K = -log ρ`, Hermitian
(`modularHamiltonian_isHermitian`), with `ρ^{it} = e^{-itK}` (`modPow_eq_generator`,
`modPow_eq_energy`). **Energy = `spectrum(K)`** = the modular energies `{-log dᵢ}` (`modularEnergy`); at a
Gibbs state `dᵢ = e^{-βEᵢ}/Z` this is the physical energy scaled, `modularEnergy = β·E + log Z` — the
finite-dimensional **KMS** identity (`gibbs_kms`). `[proved]` for the spectrum; `[reading]` that this spectrum
*is* energy.

But the modular flow is **unitary, hence exactly reversible**: `σ₋ₜ ∘ σₜ = id` (`modular_reversible`). It
carries time's *flow*, not its *arrow*. The arrow is the **dissipative complement** the unitary flow cannot
supply — paper one's coherence-lowering result, the seam as the un-decohereable floor that *orders*
irreversibility (`SeamForcing.self_cannot_fully_decohere`, **cited from paper one, not forked**). The
quantitative half of that arrow is the conserved-band layer carried here: `genReal = Re log μ ≤ 0` and the
rotating/conserved spectral bands (`Paper2.RotatingSpectrum`, the forked interface — `energy_arrow_spectrum`,
`genReal_neg_iff`, the PSD witness `quarterMul_posSemidef`).

→ [`Paper2.ModularFlow`](../../theory/formal/Theory/ModularFlow.lean),
[`Paper2.RotatingSpectrum`](../../theory/formal/Theory/RotatingSpectrum.lean).

## 4. The conserved band: knowing ⊕ energy `[proved]`

The undissipated ground — the modes the dynamics holds — is the conserved band `Peri` (A3's "greatest
sustainable field", `peri_iff_mem_conservedBand`), and it splits **into two**, disjointly: the **fixed**
sub-band (`μ = 1`, the classical diagonal record — *knowing*) and the **rotating** sub-band (`‖μ‖ = 1, μ ≠ 1`,
the conserved oscillating coherence — *energy*). The band coincidence makes this an internal direct sum
`conservedBand = fixedBand ⊕ rotatingBand` (`band_coincidence`, `undifferentiated_two_term`), and — read with
A3 at the strength of its text — the alignment of the seam band with the rotating band is forced by
contractivity + nondegeneracy, no fourth posit (`band_coincidence_from_axioms`).

→ [`Paper2.BandCoincidence`](../../theory/formal/Theory/BandCoincidence.lean),
[`Paper2.BandFromAxioms`](../../theory/formal/Theory/BandFromAxioms.lean).

## 5. Two faces of one generator — at equilibrium `[proved, at equilibrium]`

The capstone. The modular clock (`K`, from the *state* `ρ`) and paper one's dissipative arrow (`𝒟 = schur μ`,
the *dephasing*) assemble into a **single** open-system (GKLS) generator
`𝓛 = -i[(1/β)K, ·] + 𝒟`. Two independent facts make it *one* object, not two glued:

- **The unitary face *is* the modular flow at rate `1/β`.** At Gibbs equilibrium the KMS bridge gives
  `K = β·H + (log Z)·I` (`modularHamiltonian_eq_gibbs`), so the unitary generator `-i[K,·] = β·(-i[H,·])`
  (`commGen_modular_eq_beta`): the reversible face runs the modular clock, energy `= spec(H) = spec(K)/β`.

- **The two faces commute — *derived*, not imposed.** In the preferred basis B1, *both* maps are Schur
  multipliers: the dephasing by `μᵢⱼ`, and — when `ρ = diag(d)` in B1 — the modular flow by `(dᵢ/dⱼ)^{is}`
  (`modularFlow_diagonal_eq_schur`, anchored on the genuine modular operator `modPow_diagonal`, so `K` really
  comes from `ρ`). Schur multipliers in a common basis commute (`schur_comm`), giving `[σ_s, 𝒟] = 0`
  (`modular_dephaseFlow_commute`) and the generator-level `[𝓛_unitary, 𝒟] = 0` (`liouville_dephase_commute`).
  The joint flow `combinedFlow t = σ_{t/β} ∘ e^{t𝒟}` is then a one-parameter semigroup whose law
  `combinedFlow_add` **consumes** that commutation — drop it and `Φ_s ∘ Φ_t ≠ Φ_{s+t}`.

So at equilibrium the reversible and dissipative structures share one generator and one time `t` (with
`s = t/β`). The headline upgrades from "located as the unitary and dissipative parts" to **"proved one
generator"** — under the named alignment `B1 = eigenbasis(ρ)`, whose derivation is the next step.

→ [`Paper2.OneGenerator`](../formal/Paper2/OneGenerator.lean).

## 6. The alignment is forced; presence is defined `[proved, at equilibrium]`

Step 5 *assumed* `B1 = eigenbasis(ρ)`. It is in fact **derived** from a selection principle internal to the
dynamics: the modular state `ρ` (whose flow is the clock) must be the **rest-state** of the dissipator. From
`𝒟(ρ) = 0`, under the live/nondegenerate baseline, `ρ` is forced **diagonal in B1**
(`stationary_forces_offdiag_zero`, `stationary_eq_diagonal`), and for Hermitian `ρ` into exactly the
eigenbasis-diagonal shape step 5 needed (`stationary_eq_diagonal_real`). *The clock-state is the rest-state.*

The robust modes of `𝓛` (`genReal = 0`) are exactly the conserved band (`genReal_zero_iff_conservedEdge`),
the einselected structure (§4) `= fixed ⊕ rotating` (`conservedEdge_iff_fixed_or_rotating`). Define
**presence** as the Hilbert–Schmidt weight that band carries (`presenceSq`/`presence`), with `knowing` and
`energy` its fixed/rotating halves. Then:

- **Presence is conserved** — exactly (ℂ-exact, not a floor): both faces are modulus-one Schur multipliers on
  the conserved band (`presence_conserved`, `presence_conserved_norm`).
- **Presence = knowing + energy** — Pythagorean, exactly: `presence² = knowing² + energy²` (`pythagorean`,
  `pythagorean_norm`), the orthogonality checked to survive the modular rotation.

So `presence = knowing + energy` is a **theorem**, not a name — paper three's foundational definition, derived
from the einselection principle rather than posited.

→ [`Paper2.Einselection`](../formal/Paper2/Einselection.lean).

---

## The boundary — paper two's honest residue

Stated plainly, in the same read:

- **The arrow is loss, not relocation `[open]`.** The candidate conservation law for paper three is that
  decoherence *relocates* the attendable coherence into the record (knowing grows at constant presence). For
  the minimal one generator this is **refuted**: `knowing` is exactly constant while the transient weight
  tends to zero (`knowing_conserved`, `transient_tendsto_zero`, `arrow_is_loss_not_relocation`; total weight
  `= presence² + transient²`, `full_split`). Pure phase-damping *erases* the transient rather than feeding the
  record — so paper three's conservation law is a **continuity equation with population transfer**, not pure
  conservation, and needs a dissipator beyond pure dephasing. Named here as paper three's open work.

- **Out-of-equilibrium thermal time `[open]`.** The full identification (modular time = physical time with no
  equilibrium assumption) is the 30-year Connes–Rovelli problem; this paper claims only the equilibrium case.
  The type III program the finite core stops short of is mapped in
  [`modular-frontier.md`](../../theory/spec/modular-frontier.md).

- **Whether the framework *forces* einselection `[open]`.** §6 derives `B1 = eigenbasis(ρ)` from stationarity
  *given* a single rest-state; whether the framework forces einselection onto the modular eigenbasis in the
  first place (degenerate `ρ` leaves the eigenbasis under-determined within a block) is not settled here.

## Positioning — thermal time, and the division of labor

Engage Connes–Rovelli directly. Their thermal-time hypothesis identifies physical time with the modular flow
of the state; their own disclaimer is that this carries time's *flow*, not its *arrow*. This paper makes the
division of labor precise on a concrete finite witness: **flow is modular** (§1–3, reversible by
construction), **the arrow is the dissipative obstruction** the flow cannot supply (§3, paper one's seam), and
**at equilibrium the two are one generator** (§5) — with the modular eigenbasis alignment *derived* from a
rest-state principle (§6), not assumed. The contribution is threefold: the arrow **located** precisely as the
non-modular part; the **trace bridge** (paper one's `σ = Tr` as infinite-temperature modular time); and
**presence defined** as a conserved invariant splitting into knowing and energy. What stays open is named, not
hidden: the out-of-equilibrium identification, and the relocation/conservation law that would need population
transfer.

**Reading to flag, not assert `[reading]`.** Trace / infinite-temperature ↔ *universe* (atemporal); a definite
state with nontrivial modular flow ↔ *cosmos* (temporal). A candidate operator-algebra backbone for the
conservation paper; kept a `[reading]`.

## Cross-paper citation

Paper two depends on paper one's arrow as a **cited** prior result, never an import. The **quantitative**
interface — `genReal`, the conserved band — is the band layer forked frozen into `Paper2.RotatingSpectrum` /
`Paper2.BandFromAxioms` (the original hoist already factored it out). The **conceptual** result — that the
lossy self-relating projection *orders* the arrow, the seam as the un-decohereable floor
(`SeamForcing.self_cannot_fully_decohere`) — is honored here in prose, **"by the arrow result of paper
one"**, and not forked. So `paper-2/` imports no `paper-1/` path; the citation carries the meaning (see
[`04-provenance.md`](04-provenance.md), [`../../STRUCTURE.md`](../../STRUCTURE.md)).
