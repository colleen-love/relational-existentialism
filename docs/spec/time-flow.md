# From the orientation arrow to a derivation of time as flow

**Status tags.** `[proved]` mechanized sorry-free. `[written]` mechanized, sorry-free *by
construction*, pending a compile (mathlib egress was blocked in the authoring session — see
§7). `[reading]` interpretation over proved structure. `[open]` neither yet.

Companion module: [`formal/Scratch/TimeFlow.lean`](../../formal/Scratch/TimeFlow.lean).

## 0. Where we are

`Scratch/Orientation.lean` proves the *endpoints* of relational time. Over the `Knowing` interface (an
idempotent `E` with a coherence potential `coh` that vanishes exactly on `E`-fixed points), the lossy
idempotent yields a directed, asymmetric, strictly-`coh`-decreasing, irreversible arrow from a felt
state to its known shadow, instantiated on the genuine `dephase`/`defectSq`. `[proved]`

What it does **not** give is a *flow*. Because `E∘E = E`, every arrow is a single tick: `coh` takes
only two values along it, `coh a > 0` then `coh(E a) = 0`. There is no iteration, no sequence, no
graduation. So we have the two endpoints of time and the direction between them, not the line.
`[proved limitation, by inspection]`

`TimeFlow.lean` supplies the line: a graded monovariant taking many values along a trajectory, so that
"the arrow of relational time" has a flow under it rather than two points.

## 1. The one structural move

Time as flow cannot come from an idempotent. It must come from the **non-idempotent** dynamics, with
`E` recovered as the limit:

- one generator: the **attention flow** `Φ_c`, realized here by the **partial-dephasing semigroup**
  `partialDephase p M = (1−p)·M + p·dephase M` — directed attention dialled to strength `p`, the
  non-idempotent companion of `dephase` (`p = 0` is identity, `p = 1` is total `dephase`);
- **knowing** `E = dephase` is recovered as the `n → ∞` limit of `Φ_c^n` (`orbit_tendsto_knowing_entry`);
- **feeling** `coh = defectSq` is the off-diagonal mass that the flow bleeds off.

`Orientation.lean`'s `E` is then the limit of `Φ_c^n`, and its single strict drop is the *total* of
the flow's incremental decreases (`dephaseFlow_total_drop`). Orientation becomes the boundary case of
the flow.

**Relation-primacy guard (A2).** The flow parameter `n` is the **return-depth** of the orbit
(`Flow.orbit` = `step^[n]`), counting closures of the feedback loop, not a background clock the
relating sits inside. `n` is kept internal everywhere; nothing is indexed by an external `ℝ`-time.

## 2. The central theorem (T-flow / Lyapunov) — `[written]`

> For the attention flow, `coh(Φ_c^n a)` is **monotonically decreasing in `n`**, strictly while not
> yet fixed, and converges to `coh(E a) = 0`. On the genuine instance the decay is **exact and
> geometric**: `defectSq(Φ_c^n M) = γ^n · defectSq M` with `γ = (1−p)² < 1` the squared second
> eigenvalue modulus — the **spectral gap**, the clock rate.

Mechanized content (`TimeFlow.lean`):

- `Flow.coh_orbit_antitone` — the orbit potential is antitone in the return-depth `n`. `[written]`
- `Flow.coh_orbit_strictAnti` — and *strictly* drops at every not-yet-fixed step. `[written]`
- `Flow.coh_drops_telescope` / `Flow.total_drop` — the incremental drops telescope to the total fall
  of the potential. `[written]`
- `GeometricFlow.coh_orbit_eq` — `coh(step^[n] a) = γ^n · coh a`, exactly. `[written]`
- `GeometricFlow.coh_orbit_tendsto_zero` — geometric decay to `0` (convergence to the fixed
  subalgebra). `[written]`
- `defectSq_iterate` — on the genuine instance, `defectSq(partialDephase p ^[n] M) = ((1−p)²)^n ·
  defectSq M`, the *exact* graded monovariant. `[written]`
- `dephaseFlow` — assembles the above into a `GeometricFlow` at rate `γ = (1−p)²`. `[written]`

`coh` becomes a genuine potential decreasing through a continuum of intermediate values; relational
time is the value of that potential along the orbit; the spectral gap `(1−p)²` is the clock rate —
mixing time `≈ 1/(1−γ)` is the duration to be known.

**Axiom anchoring.** The gap is meaningful because attention is finite by constitution (A3, bounded
capacity); the fixed subalgebra the flow descends to is the self. "Time runs until the self is reached"
is `coh → 0`, and the rate is set by A3's finiteness, not bolted on.

## 3. The veto-check

A general CP map `Φ_c` can carry **rotating peripheral spectrum** — eigenvalues of modulus 1 that are
not 1, i.e. sustained, non-decaying coherence that `coh` never bleeds off. Decompose: fixed (eigenvalue
1), rotating-peripheral (modulus 1, ≠ 1), transient (modulus < 1).

- **3a `[open]`** The general decomposition; T-flow's monovariant is `coh` on the transient part.
- **3b `[reading]`** Rotating-peripheral coherence is a candidate for *permanent feeling constitutive
  of the self* — sustained, uncollapsed, never known. On that reading the self splits three ways: fixed
  = known, rotating-peripheral = permanent feeling, transient = passing feeling time bleeds off. Richer
  than the current binary, and the most interesting thing this derivation could surface. Left as spec
  prose; not committed to in the formalism.
- **3c `[written]`, discharged for the instance** `partialDephase p` is a real combination of the
  self-adjoint `id` and `dephase`, hence real-symmetric with eigenvalues in `[1−p, 1] ⊆ [0,1]` —
  **no rotation**. The transient (off-diagonal) part decays monotonically to `0` with no rotating
  remainder. This is the honest runnable instance where T-flow holds without caveat; `defectSq_iterate`
  is the exact statement that the felt mass decays cleanly, no peripheral residue. (Compare
  [`Scratch/Peripheral.lean`](../../formal/Scratch/Peripheral.lean)'s `dephase_no_rotating_peripheral`
  for the `p = 1` endpoint.)

## 4. Ordered build (interface-first)

1. **`Flow` interface — `[written]`.** A `step`, a potential `coh ≥ 0`, a `Fix` set with `coh = 0 ↔
   Fix`, `coh` non-increasing and strictly decreasing off `Fix`. Proved over it: orbit antitone, strict
   while unfixed, telescoping. The graded analogue of `Orientation.Knowing`.
2. **Recover Orientation as the boundary — `[written]`.** `orbit_tendsto_knowing_entry`: the orbit
   converges entrywise to `dephase M`, i.e. to `Orientation.dephaseKnowing`'s `E`. The flow *contains*
   the arrow; `dephaseFlow_total_drop` shows the single orientation drop is the flow's total.
3. **Finite-dim `dephase`-semigroup instance — `[written]`.** `partialDephase`, `copyDefect_partialDephase`
   (one step scales the felt mass by `(1−p)`), `defectSq_iterate` (exact geometric decay), `dephaseFlow`.
   Needs no rotation handling (3c). Runnable witness on the qubit `plus`: `defectSq_iterate_plus`,
   `defectSq_plus_strictAnti` (strict at every depth for `0<p<1`), `defectSq_plus_tendsto_zero`.
4. **Rate = gap — `[written]` (instance) / `[open]` (general).** The decay constant `γ = (1−p)²` *is*
   the squared second eigenvalue modulus of `partialDephase p` (eigenvalue `1−p` on each coherence).
   Identifying `γ` with the second eigenvalue modulus of an arbitrary `Φ_c`, tied to the
   Perron–Frobenius existence already proved ([`PerronFrobenius.lean`](../../formal/Scratch/PerronFrobenius.lean)),
   stays open in general.
5. **Spectral decomposition / rotation — `[open]` (3a) / `[reading]` (3b).** Discharged for the
   instance (3c), open in general; the three-way split of the self decided in prose only.

## 5. What is `[written]`/`[proved]` vs `[reading]` at the end

- `[written]` (finite dim, `dephase`-semigroup): `coh` is a strict graded monovariant decreasing
  through a continuum to `0` along the attention orbit, at exact geometric rate `(1−p)²`. Strictly more
  than `Orientation.lean`: a **time-shaped order** with many moments, not two endpoints. (`[written]`
  rather than `[proved]` only because the session's mathlib egress was blocked — see §7. The proofs are
  sorry-free and built from already-`[proved]` lemmas; they need a compile to earn the green check.)
- `[reading]`, reduced but not eliminated: that this time-shaped order **is** time. The reading is now
  *weaker/safer* than before — not "two points are an arrow of time" but "a graded potential with
  geometric decay and a definite rate is time," the standard shape of a physical clock. The gap between
  structure and time has narrowed to the same gap physics itself leaves.
- `[open]`: the rotating-peripheral case (3a/3b); the general rate-=-gap identification (§4.4); the
  infinite-dim / von Neumann standard-form version; and the frontier below.

## 6. The honest remaining frontier

T-flow gives the *direction and rate* of time's passage, not its **origin**. The flow's orientation is
inherited from `coh` decreasing, i.e. from decoherence; the decohering direction is fixed by which
subalgebra `E` projects onto, fixed by the seam (the self cannot trace out the factor it is part of).
The deepest claim — *the arrow's origin is the seam, not a stipulated `L`* — requires showing the
generator's dissipative direction is forced by the self-inclusive partial trace rather than chosen.
Sharpened: **does the seam fix the sign of `L`?** If yes, time's flow, direction, and origin all reduce
to relation-primacy plus the Lawvere obstruction, and nothing about time is primitive. That is the real
prize; T-flow is the rung directly beneath it. `[open]`

## 7. Verification status (this session)

The companion Lean module was authored against the existing, already-verified lemmas
(`Decoherence.dephase`/`copyDefect`/`defectSq`, `Orientation.Knowing`/`dephaseKnowing`,
`SpectralDecay`) and standard mathlib API, and is written to be sorry-free. It could **not** be
compiled in the authoring session: the environment's egress policy returns `403` for cloning
`mathlib4` (the `Scratch` library's sole heavy dependency), so `lake build Scratch` cannot fetch the
toolchain. Every theorem is therefore tagged `[written]` rather than `[proved]` until a session with
mathlib access runs the build. To verify:

```
cd formal
lake update          # fetch mathlib (needs github egress)
lake exe cache get    # mathlib build cache
lake build Scratch.TimeFlow
```

On a green build, promote the `[written]` tags to `[proved]` here and flip the `⏳` to `✅` in
`formal/Scratch.lean`.

---

*One line:* Orientation proved the endpoints of relational time; `TimeFlow` graduates them into a flow
by composing knowing with the attention dynamics, with the spectral gap `(1−p)²` as the clock — and the
prize beneath it is whether the seam fixes the direction of the flow, which would make time wholly
derived.
