# Deriving space, the rotating peripheral spectrum, and energy

**Status tags.** Four states, tracked per item:

| Tag | Meaning |
| --- | --- |
| `[written]` | Lean mechanization authored; **compilation/sorry-freeness not yet confirmed** on this branch. |
| `[proved]` | Mechanized and verified sorry-free against mathlib v4.15.0 (axioms `[propext, Classical.choice, Quot.sound]` only). |
| `[reading]` | An interpretation laid over proved structure — held as a reading, not a derivation of physics. |
| `[open]` | Not yet established. |

Companion modules: [`formal/Scratch/Space.lean`](../../formal/Scratch/Space.lean) (Part 1),
[`formal/Scratch/RotatingSpectrum.lean`](../../formal/Scratch/RotatingSpectrum.lean) (Parts 2–3).
Sequel to [`time-flow.md`](time-flow.md).

**Branch:** `claude/space-energy-rotating-spectrum-re9ct1`.

> **Verification note.** The two new modules are authored and self-reviewed against the vendored
> mathlib API; they are tagged `[written]` until the mathlib build completes and `lake build` confirms
> them sorry-free, at which point each `[written]` item below is promoted to `[proved]`. The
> **Progress ledger** at the foot of this page is the single source of truth for current state.

---

**Abstract.** This plan extends the framework's derivation of time to space, energy, and the rotating
spectral structure that gates them. The organizing claim is that time, space, and energy are not three
separate constructions but three aspects of a single generator `L` acting on the relational coupling:
space is the geometry of `L`'s coupling graph; the irreversible arrow of time is the
strictly-negative-real part of its spectrum (mechanized in `TimeFlow`/`TimeArrow`/`SeamForcing`);
conserved energy is the modulus-one rotating part; and matter is the fixed band the seam forces `L` to
protect. The pieces differ sharply in reach, and the plan is ordered by it: space is mechanizable now
in the present real model; the rotating spectrum that carries energy lives in a sector the current
self-adjoint dynamics provably exclude, so reaching it is a model extension to ℂ (the keystone), not a
lemma; and matter is a reading laid over both. Throughout, the discipline is the framework's usual one
— prove the structural skeleton, identify the physics as a reading, and never confuse the two.

**Primacy guard:** relation is primary throughout. Space, time, and energy are read off the structure
of the coupling/generator; none is a background the relations sit inside.

## 0. Orientation — where the branch stands

**Done (time).**
- `Orientation.lean` — the endpoints of relational time. Over the `Knowing` interface (idempotent `E`,
  coherence potential `coh` vanishing exactly on `E`-fixed points) a lossy idempotent yields a directed,
  asymmetric, strictly-`coh`-decreasing, irreversible arrow; instance `dephaseKnowing` (`E = dephase`,
  `coh = defectSq`). `[proved]`
- `TimeFlow.lean` — the flow under the arrow. `Flow`/`GeometricFlow` interfaces; orbit potential
  antitone and strictly decreasing off `Fix`; the non-idempotent `partialDephase p` is a
  `GeometricFlow` at rate `(1−p)²`, converging entrywise to `dephase`. `[proved]`
- `TimeArrow.lean` — acyclicity from the monovariant; the sign locked to contractivity; a knowing's
  only inverse is an anti-physical coherence-amplifier; genuine collapse only at the idempotent limit.
  `[proved]`
- `SeamForcing.lean` — the seam fixes which subalgebra `E` projects onto. The seam survives every
  available knowing; the maximal available knowing `knowSeam J` is a conditional expectation whose
  fixed subalgebra is exactly `SeamAlgebra J`; the self can never fully decohere itself while the seam
  carries coherence. Aim vs orientation as two theorems (`direction_uniform_in_seam`,
  `target_depends_on_seam`). `[proved]` core; the `J`↔genuine-seam identification is the standing
  `[reading]`.

**Existing spectral infrastructure (on `main`).** `SpectralDecay.lean` (`P + N` split),
`Peripheral.lean` (`idempotent_eigenvalue`, `dephase_no_rotating_peripheral`), `PeripheralAlgebra.lean`
(`fix_comm`), `PerronFrobenius.lean`.

**Key structural fact governing this plan.** The current model is real (`Matrix A A ℝ`) and its
dynamics are self-adjoint with spectrum in `[0,1]`. By `idempotent_eigenvalue` /
`dephase_no_rotating_peripheral`, there is **no rotating peripheral spectrum** anywhere in this model:
peripheral = fixed, and the fixed/rotating/transient split collapses to fixed + transient. A rotating
eigenvalue requires non-self-adjoint dynamics over ℂ. So `TimeFlow` captured the purely **dissipative**
extreme; energy lives in a sector this model excludes, and reaching it is a model extension, not a
lemma. Two facts are settled *within* the present model and don't wait on that extension: the arrow's
direction (`TimeArrow`) and the identity of the fixed subalgebra it descends to (`SeamForcing`). Space
is likewise independent of the extension.

**Unifying frame.** Everything sits in the spectrum of one generator `L` over the relational coupling:
- **space** = the coupling-graph geometry of `L`;
- **arrow / dissipation / time** = `Re(spec L) < 0`, the transient band — *done* (`TimeFlow`), with
  its target subalgebra seam-fixed (`SeamForcing`);
- **energy / reversible time** = `Im(spec L)`, the rotating peripheral band;
- **matter** = the fixed band as a stable bound eigenform — `SeamForcing` supplies its reason for
  stability: the fixed band the self cannot decohere is exactly the seam `SeamAlgebra J`;
- **feeling** = the off-diagonal `(1−E)` mass, with **two distinct permanences**: seam-permanent
  (operational, real-model, proved) and spectrally-permanent (rotating, open).

## Part 1 — Space (present model; near-term) — companion `Space.lean`

**Construction** (relation-primary): from the coupling graph implicit in `Φ_c` / `copyDefect` — sites
`A`, directed edge weights `w_{ij}` = coupling strength. Distance is `−log` of the strongest
multiplicative coupling path, mechanized **additively** by taking edge *lengths*
`len i j = −log w_{ij} ∈ [0,∞]` as primitive (`∞` = zero coupling); then the distance is a genuine
shortest-path infimum and the `−log` is absorbed into the edge length. Asymmetric `c` ⇒ a quasi-metric
(a feature to state, not smooth away).

**Targets.**
- `[written]` `d` is a quasi-pseudometric: `d(i,i)=0` (`Coupling.dist_self`), triangle inequality from
  path concatenation (`Coupling.dist_triangle`, via `walkLen_concat`), and a direct edge bounds it
  (`Coupling.dist_le_len`). Asymmetry is proved, not assumed: `dist_asymmetric` exhibits a two-site
  coupling with `d(a,b) ≠ d(b,a)`. So `dist` is genuinely a *quasi*-pseudometric.
- `[written]` separability ⟺ infinite distance: `Coupling.dist_eq_top_iff` (`d = ∞` iff every
  connecting walk crosses a zero-coupling edge); witness `couplingSep_dist` (⊗-coexisting relata with
  zero coupling are at `d = ∞`). With `dist_le_len` this makes "space = coexistence minus connection" a
  theorem.
- `[written]` influence bound (the payoff): a weighted dephasing flow `wDephase w` (the edge-resolved
  refinement of `TimeFlow.partialDephase`) gives `copyDefect_wDephase_iterate`
  (`(i,j)` coherence after `n` steps `= (w i j)^n · M i j`). Taking `w i j = exp(−len i j)`,
  `influence_bound` shows `|coherence_n(i,j)| ≤ exp(−n · d(i,j)) · |M i j|`: influence propagates no
  faster than the coupling distance permits. A finite-propagation bound, reusing the `TimeFlow` decay
  engine and the path-metric edge bound.

**Scope.** A weighted quasi-metric pre-geometry. Not dimension, smoothness, a manifold, or signature;
the "lightcone" is a propagation bound only. The effective-resistance / graph-Laplacian distance is the
richer `[open]` refinement; that Laplacian is the same generator Parts 2–3 use. That the quasi-metric
*is* space is the standing `[reading]`.

## Part 2 — The rotating peripheral spectrum (keystone) — companion `RotatingSpectrum.lean`

**R0 — model decision.** Move from `Matrix A A ℝ` to `Matrix A A ℂ`. Only here can modulus-1, non-1
eigenvalues exist. The mechanization realizes this not as a full CPTP/Lindblad framework (mathlib has
none) but, per the `TimeFlow` discipline, as **one genuine instance**.

**R1/R2 — the witness.** `schur μ` is the **phase-damping channel**, `M i j ↦ μ i j · M i j` — the
ℂ-lift of `Space.wDephase` / `TimeFlow.partialDephase`. Its matrix units are eigen-operators with
eigenvalue `μ i j`, so `schur_iterate` gives the per-edge geometric law, and the band of an edge is
read off `‖μ i j‖`:
- `[written]` **fixed** (`μ i i = 1`): coherence held exactly (`schur_fixed`) — the known/classical/self
  band (diagonal);
- `[written]` **rotating** (`‖μ i j‖ = 1`): magnitude exactly conserved for all `n` (`schur_sustained`)
  — sustained oscillating coherence;
- `[written]` **transient** (`‖μ i j‖ < 1`): magnitude `→ 0` (`schur_transient_tendsto`) — the
  `TimeFlow` arrow.

The concrete witness `quarterMul` on `Matrix (Fin 3) ℂ` carries all three at once: diagonal `1`
(fixed); `μ_{01} = i = e^{iπ/2}` (rotating — `‖i‖ = 1`, `i ≠ 1`); `μ_{02} = 1/2` (transient). The
coherence `U = E₀₁` is a **genuine rotating eigen-operator**: `phaseChannel_eigen` (`Φ U = i · U`),
sustained (`rotating_sustained`: `‖Φ^n U‖ = ‖U‖`) while `transient_decays` shows the `(0,2)` coherence
decays. `[written]`

**Veto-checks (narrated).** A primitive `Φ` has peripheral spectrum exactly `{1}` — rotation requires a
symmetry/degeneracy (rotating spectrum ⟺ a coupling symmetry ⟺ a conserved quantity, Noether,
structurally). `|λ|=1` exactly is non-generic; perturbation pushes it inside the disk. The general
peripheral **structure theorem** for CPTP maps (the rotating unitaries normalize `Fix`, a
crossed-product structure) and that `quarterMul` is a bona fide CPTP map for a positive-semidefinite
multiplier remain `[open]`.

**Two permanences, kept distinct.** Seam coherence is permanent because **un-attendable** (operational,
real-model, proved in `SeamForcing`). The rotating band is permanent because **non-decaying under the
flow** (spectral, `‖μ‖ = 1`). Orthogonal protections; "fully permanent feeling" is the intersection.
Whether the seam-protected and rotating-protected bands coincide, intersect, or are independent is
`[open]`.

## Part 3 — Energy (reading over the witness) — in `RotatingSpectrum.lean`

- `[reading over R]` Write each eigenvalue `μ = exp(s)`. The rotating band has `‖μ‖ = 1`, i.e.
  `Re s = 0`: pure phase, `s = iθ`, `θ` the **frequency/energy**, conserved (`energy_conserved`). The
  transient band has `‖μ‖ < 1`, i.e. `Re s < 0`: the gap, the decay, the **arrow**
  (`arrow_dissipates`). `energy_arrow_split` shows both in one channel's spectrum: **energy = the
  conserved (modulus-one) band; arrow = the decaying band** — two halves of one generator's spectrum.
- `[reading]` **Two conservations, not conflated.** *Dynamical* (a coupling symmetry → rotating
  spectrum → a conserved charge — this is energy) and *operational* (self-inclusion → the un-attendable
  seam → permanent feeling — this is the self/matter substrate, **not** energy). Keeping them separate
  keeps space/time/energy/matter cleanly distinguished.

**Scope.** Energy as the conserved spectral data of the generator, with the energy/arrow split. Not
units, ℏ, or any specific spectrum. The `⊗`-additivity sub-question (`H_total = H_1⊗1 + 1⊗H_2` only
when the coupling factors across `⊗`, linking energy's additivity to Part 1's separability) is `[open]`.

## Part 4 — Matter (reading)

The fixed band is a bound eigenform; `SeamForcing` supplies its reason for stability (it is the seam,
the un-attendable protected subalgebra `SeamAlgebra J`). Binding/persistence can be read from the seam
(operational protection) and/or the spectral gap (dynamical protection); the relation between the two
protections is itself `[open]`. `[reading]`

## Ordering and dependencies

1. **Space** — present real model, independent of R, influence-bound reuses `TimeFlow`. Shipped first
   (`Space.lean`).
2. **R0 + one rotating instance** — the keystone; unlocks energy, reversible time, and
   spectrally-permanent feeling as readings over a single decomposition (`RotatingSpectrum.lean`).
3. **Energy** — read off the R instance as the conserved (dynamical) half of `L`'s spectrum
   (`RotatingSpectrum.lean`, §3).
4. **Matter** — a reading, supported by `SeamForcing`.

## Progress ledger

The single source of truth for current state. `[written]` items are authored and pending the
`lake build` confirmation that promotes them to `[proved]`.

| Item | Lean name(s) | State |
| --- | --- | --- |
| **Space** — `d(i,i)=0` | `Coupling.dist_self` | `[written]` |
| Space — triangle inequality | `Coupling.dist_triangle`, `walkLen_concat` | `[written]` |
| Space — direct-edge bound | `Coupling.dist_le_len` | `[written]` |
| Space — asymmetry (quasi-metric) | `dist_asymmetric` | `[written]` |
| Space — separability ⟺ `d=∞` | `Coupling.dist_eq_top_iff`, `couplingSep_dist` | `[written]` |
| Space — influence/propagation bound | `influence_bound`, `copyDefect_wDephase_iterate` | `[written]` |
| Space — graph-Laplacian / resistance distance | — | `[open]` |
| Space — "the quasi-metric *is* space" | — | `[reading]` |
| **Rotating** — ℂ phase-damping channel | `schur`, `schur_iterate` | `[written]` |
| Rotating — fixed band | `schur_fixed`, `fixed_held` | `[written]` |
| Rotating — sustained rotating band | `schur_sustained`, `rotating_sustained` | `[written]` |
| Rotating — transient band decays | `schur_transient_tendsto`, `transient_decays` | `[written]` |
| Rotating — genuine rotating eigen-operator | `phaseChannel_eigen`, `quarterMul_01_ne_one` | `[written]` |
| Rotating — CPTP peripheral structure theorem | — | `[open]` |
| Rotating — `quarterMul` is bona fide CPTP | — | `[open]` |
| Rotating — seam-band ∩ rotating-band question | — | `[open]` |
| **Energy** — conserved (modulus-one) band | `energy_conserved` | `[written]` |
| Energy — dissipative (arrow) band | `arrow_dissipates` | `[written]` |
| Energy — energy/arrow spectral split | `energy_arrow_split` | `[written]` |
| Energy — `L = −i[H,·]+D` generator split (full) | — | `[open]` |
| Energy — `⊗`-additivity of `H` | — | `[open]` |
| Energy — "rotating phases *are* energy" | — | `[reading]` |
| **Matter** — fixed band stability ← seam | `SeamForcing.*` | `[reading]` |
| Matter — operational vs dynamical protection | — | `[open]` |
| **Time** (prior branch) — orientation, flow, arrow, seam | `Orientation`, `TimeFlow`, `TimeArrow`, `SeamForcing` | `[proved]` |
