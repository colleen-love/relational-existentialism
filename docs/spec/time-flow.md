# From the orientation arrow to a derivation of time as flow

**Status tags.** `[proved]` mechanized sorry-free. `[reading]` interpretation over proved structure.
`[open]` neither yet. Everything tagged `[proved]` below is verified: `Scratch.TimeFlow` builds
sorry-free against mathlib v4.15.0, and the central theorems depend only on the three standard axioms
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

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

## 2. The central theorem (T-flow / Lyapunov) — `[proved]`

> For the attention flow, `coh(Φ_c^n a)` is **monotonically decreasing in `n`**, strictly while not
> yet fixed, and converges to `coh(E a) = 0`. On the genuine instance the decay is **exact and
> geometric**: `defectSq(Φ_c^n M) = γ^n · defectSq M` with `γ = (1−p)² < 1` the squared second
> eigenvalue modulus — the **spectral gap**, the clock rate.

Mechanized content (`TimeFlow.lean`):

- `Flow.coh_orbit_antitone` — the orbit potential is antitone in the return-depth `n`. `[proved]`
- `Flow.coh_orbit_strictAnti` — and *strictly* drops at every not-yet-fixed step. `[proved]`
- `Flow.coh_drops_telescope` / `Flow.total_drop` — the incremental drops telescope to the total fall
  of the potential. `[proved]`
- `GeometricFlow.coh_orbit_eq` — `coh(step^[n] a) = γ^n · coh a`, exactly. `[proved]`
- `GeometricFlow.coh_orbit_tendsto_zero` — geometric decay to `0` (convergence to the fixed
  subalgebra). `[proved]`
- `defectSq_iterate` — on the genuine instance, `defectSq(partialDephase p ^[n] M) = ((1−p)²)^n ·
  defectSq M`, the *exact* graded monovariant. `[proved]`
- `dephaseFlow` — assembles the above into a `GeometricFlow` at rate `γ = (1−p)²`. `[proved]`

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
- **3c `[proved]`, discharged for the instance** `partialDephase p` is a real combination of the
  self-adjoint `id` and `dephase`, hence real-symmetric with eigenvalues in `[1−p, 1] ⊆ [0,1]` —
  **no rotation**. The transient (off-diagonal) part decays monotonically to `0` with no rotating
  remainder. This is the honest runnable instance where T-flow holds without caveat; `defectSq_iterate`
  is the exact statement that the felt mass decays cleanly, no peripheral residue. (Compare
  [`Scratch/Peripheral.lean`](../../formal/Scratch/Peripheral.lean)'s `dephase_no_rotating_peripheral`
  for the `p = 1` endpoint.)

## 4. Ordered build (interface-first)

1. **`Flow` interface — `[proved]`.** A `step`, a potential `coh ≥ 0`, a `Fix` set with `coh = 0 ↔
   Fix`, `coh` non-increasing and strictly decreasing off `Fix`. Proved over it: orbit antitone, strict
   while unfixed, telescoping. The graded analogue of `Orientation.Knowing`.
2. **Recover Orientation as the boundary — `[proved]`.** `orbit_tendsto_knowing_entry`: the orbit
   converges entrywise to `dephase M`, i.e. to `Orientation.dephaseKnowing`'s `E`. The flow *contains*
   the arrow; `dephaseFlow_total_drop` shows the single orientation drop is the flow's total.
3. **Finite-dim `dephase`-semigroup instance — `[proved]`.** `partialDephase`, `copyDefect_partialDephase`
   (one step scales the felt mass by `(1−p)`), `defectSq_iterate` (exact geometric decay), `dephaseFlow`.
   Needs no rotation handling (3c). Runnable witness on the qubit `plus`: `defectSq_iterate_plus`,
   `defectSq_plus_strictAnti` (strict at every depth for `0<p<1`), `defectSq_plus_tendsto_zero`.
4. **Rate = gap — `[proved]` (instance) / `[open]` (general).** The decay constant `γ = (1−p)²` *is*
   the squared second eigenvalue modulus of `partialDephase p` (eigenvalue `1−p` on each coherence).
   Identifying `γ` with the second eigenvalue modulus of an arbitrary `Φ_c`, tied to the
   Perron–Frobenius existence already proved ([`PerronFrobenius.lean`](../../formal/Scratch/PerronFrobenius.lean)),
   stays open in general.
5. **Spectral decomposition / rotation — `[open]` (3a) / `[reading]` (3b).** Discharged for the
   instance (3c), open in general; the three-way split of the self decided in prose only.

## 5. What is `[proved]` vs `[reading]` at the end

- `[proved]` (finite dim, `dephase`-semigroup): `coh` is a strict graded monovariant decreasing
  through a continuum to `0` along the attention orbit, at exact geometric rate `(1−p)²`. Strictly more
  than `Orientation.lean`: a **time-shaped order** with many moments, not two endpoints. Verified:
  `Scratch.TimeFlow` builds sorry-free against mathlib v4.15.0 (see §7).
- `[reading]`, reduced but not eliminated: that this time-shaped order **is** time. The reading is now
  *weaker/safer* than before — not "two points are an arrow of time" but "a graded potential with
  geometric decay and a definite rate is time," the standard shape of a physical clock. The gap between
  structure and time has narrowed to the same gap physics itself leaves.
- `[open]`: the rotating-peripheral case (3a/3b); the general rate-=-gap identification (§4.4); the
  infinite-dim / von Neumann standard-form version; and the frontier below.

## 6. The frontier — does the seam fix the sign? (partial progress)

T-flow gives the *direction and rate* of time's passage, not its **origin**. The flow's orientation is
inherited from `coh` decreasing, i.e. from decoherence; the decohering direction is fixed by which
subalgebra `E` projects onto, fixed by the seam (the self cannot trace out the factor it is part of).
The deepest claim — *the arrow's origin is the seam, not a stipulated `L`* — requires showing the
generator's dissipative direction is forced by the self-inclusive partial trace rather than chosen.
Sharpened: **does the seam fix the sign of `L`?**

[`TimeArrow.lean`](../../formal/Scratch/TimeArrow.lean) mechanizes how far this is reachable:

- **Acyclicity `[proved]`.** While still feeling, the orbit never returns to an earlier state
  (`flow_orbit_ne`) — the timeline is a strict order with no closed loops before the self, the
  order-theoretic face of irreversibility, from the monovariant alone.
- **Sign = contractivity `[proved]`.** One step scales the feeling by exactly `(1−p)²`
  (`defectSq_partialDephase`), so the flow contracts the feeling iff `0 ≤ p ≤ 2` (`contractive_iff`,
  `time_forward_regime`) and *expands* it — runs time backward — iff `p < 0 ∨ p > 2`
  (`expanding_regime`). The coh-decreasing (time-forward) sign is **exactly** the contractive regime:
  the direction is locked to contractivity, not chosen beside it.
- **A knowing's only inverse is an anti-knowing `[proved]`.** A genuine partial knowing `0 < p < 1` is
  linearly invertible, but its unique inverse is `partialDephase q` with `q < 0`, in the expanding
  regime `(1−q)² > 1` (`knowing_inverse_is_antiphysical`). Time-reversal exists as linear algebra but
  only as the non-physical amplification of coherence from nothing — the thing no contraction, no
  conditional expectation, no partial trace can do. The contractive seam admits the decreasing arrow
  alone; its sign is forced by the non-existence of a *contractive* inverse (the flow-graded
  strengthening of `Orientation.no_recovery`).
- **Irreversibility lives at the limit `[proved]`.** The interior `0 < p < 1` is *secretly* invertible
  (only anti-physically); genuine collapse — no inverse of any kind — appears at exactly one point. The
  flow is injective for every `p ≠ 1` (`partialDephase_injective`) and non-injective precisely at
  `p = 1 = dephase`, the idempotent knowing (`partialDephase_one_not_injective`,
  `Orientation.no_recovery`). The arrow stops being injective exactly when it stops being a flow and
  becomes the projection.

So **sign = contractivity = physicality of the seam** is now `[proved]`: the dissipative direction is
not an independent choice but is locked to the dynamics being a contraction (a partial trace /
conditional expectation). What stays **`[open]`** is the final step: that the seam **forces which
subalgebra** `E` projects onto — so that the contraction's direction is fixed by the self-inclusive
trace itself rather than by which side we called `p ≥ 0`. That is the self-reference / Lawvere bridge
([`Relating.self_inclusive_unmodelable`](../../formal/RelExist/Relating.lean)). If it closes, time's
flow, direction, and origin all reduce to relation-primacy plus the Lawvere obstruction, and nothing
about time is primitive. That remains the real prize; the sign↔contractivity lock is the rung now
underfoot.

## 7. Verification

The companion module builds **sorry-free** against mathlib v4.15.0, and the central theorems
(`defectSq_iterate`, `GeometricFlow.coh_orbit_tendsto_zero`, `orbit_tendsto_knowing_entry`,
`dephaseFlow_total_drop`, `Flow.coh_orbit_antitone`) depend only on the three standard axioms
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. To reproduce:

```
cd formal
lake build Scratch.TimeFlow
```

Note on this repo's remote (Claude Code on the web) sessions: the mathlib **olean cache**
(`mathlib4.lean-cache.cloud`, `*.blob.core.windows.net`) is egress-blocked, so the first build
compiles mathlib **from source** (slow, then cached in the container). Some task-launched sessions also
get a *scoped* git proxy that 403s the mathlib `git clone`; `formal/scripts/bootstrap.sh` step 0 works
around that by routing git through the agent HTTPS proxy. The fastest setup is to allowlist the olean
cache host in the environment's network policy, which makes `lake exe cache get` work (~minutes instead
of hours).

---

*One line:* Orientation proved the endpoints of relational time; `TimeFlow` graduates them into a flow
by composing knowing with the attention dynamics, with the spectral gap `(1−p)²` as the clock — and the
prize beneath it is whether the seam fixes the direction of the flow, which would make time wholly
derived.
