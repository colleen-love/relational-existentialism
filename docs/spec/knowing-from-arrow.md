# From the arrow back to the knowing — the converse direction

**Status tags.** `[proved]` mechanized sorry-free. `[reading]` interpretation over proved structure.
`[open]` neither yet. Everything tagged `[proved]` below is verified against mathlib v4.15.0 and
depends only on the three standard axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Companion module: [`formal/Scratch/KnowingFromArrow.lean`](../../formal/Scratch/KnowingFromArrow.lean).
Keystone module (the lift): [`formal/Scratch/MeanErgodic.lean`](../../formal/Scratch/MeanErgodic.lean).
Sequel to [`time-flow.md`](time-flow.md); dual to its §2 and §6.

## 0. What "the hypothesis" is, stated precisely

The forward chain proves **`knowing ⟹ arrow`**: over the `Knowing` interface, the lossy idempotent
`E` gives the endpoints (`Orientation`), `partialDephase p` graduates them into a flow at rate
`(1−p)²` (`TimeFlow`), the sign is locked to contractivity (`TimeArrow`), and the seam fixes the
target subalgebra (`SeamForcing`). Knowing is the *input*; the time-arrow is the *derived output*.

The hypothesis is the **converse**:

> **Take an arrow as given and recover the knowing.** From a dynamics exhibiting the
> arrow-properties alone — a positive contraction carrying a strict monovariant that runs to a
> floor — derive that its limit **is** a knowing: an idempotent conditional expectation onto a
> subalgebra, with the monovariant equal to the off-diagonal mass that limit annihilates.

This is the structural core of "wherever there is an arrow, there is a knowing under it." It is
**not** the cosmic-subject claim ("something has been knowing the cosmos for 13.8 Gyr"); that claim
is strictly downstream and is fenced off in §6, with the proofs showing exactly which of its steps
the converse does and does not supply. The discipline is the repo's usual one: prove the skeleton,
mark the physics as a reading, never confuse the two.

## 1. The one structural move

The forward direction *assumed* `E` and a coherence potential `coh`, and derived the flow. The
converse must run the implications backward: **assume the flow's conclusions as hypotheses, and
derive `E`.** Concretely, the data the forward chain *produced* —

- a `step` `T` that is a positive, identity-preserving contraction;
- a potential `V ≥ 0`, antitone along the orbit, strict off its zero set, with `V → 0`;

— become the *interface* `Arrow`, and the thing the forward chain *started from* (the idempotent
conditional expectation `E` and its fixed subalgebra) becomes the thing to **prove exists** as the
orbit's limit. `Arrow` carries the same fields as `TimeFlow.Flow`; the difference is direction of
inference. `Flow : E ⊢ V`. `Arrow : V ⊢ E`. (The *quantitative* hypotheses on `T` — positive, unital,
contractive — that the general lift needs are properties of the concrete `step`; the genuine instance
supplies them, the abstract lift is §4.4.)

**Relation-primacy guard (A2).** As in `TimeFlow`, the orbit index `n` is the return-depth of the
feedback loop, internal; nothing is indexed by an external `ℝ`-time. The recovered `E` is the
`n → ∞` limit *of the orbit*, not a knower sitting in a background interval. This guard is what
forecloses reading the recovered `E` as a persistent external subject (§6).

## 2. The central theorem (the limit is a knowing)

> For a positive contractive `Arrow` with **trivial peripheral spectrum** (modulus-1 eigenvalue only
> at `1`, no rotation), the orbit `T^n` converges, and its limit `E := lim_n T^n` is an **idempotent
> conditional expectation onto the fixed subalgebra** `Fix(T)`; moreover the monovariant `V` is
> equivalent to the off-diagonal mass `‖(1−E)·‖²` that `E` annihilates. The arrow's limit is a
> knowing in the exact sense of `Orientation`.

Mechanized content (`KnowingFromArrow.lean`), staged instance-first — every conjunct is an existing
theorem about `dephase`, so the instance closes by **re-export**, not new proof:

- `arrow_limit_is_knowing` — the orbit converges **entrywise** to `(dephaseKnowing A).E = dephase`:
  the recovered limit is literally `Orientation`'s knowing map `E`. **`[proved]` for the instance**
  (this *is* `TimeFlow.orbit_tendsto_knowing_entry`). **`[open]` in general** (the lift — see §4.4).
- `limit_idempotent` — `E ∘ E = E`. **`[proved]` for the instance** (`Decoherence.dephase_idem`,
  through the `Orientation.Knowing` interface).
- `limit_is_seam_CE` — `E` is the **seam-forced conditional expectation** `SeamForcing.knowSeam ∅`,
  the maximal available knowing at the empty seam: an idempotent conditional expectation onto the
  (diagonal) classical subalgebra. **`[proved]` for the instance** (`SeamForcing.knowSeam_empty` —
  exactly the `J = ∅` case the `knowSeam` machinery already certifies). **`[open]` in general** (§4.4).
- `limit_annihilates_potential` — `E` sends the arrow's potential `V = defectSq` to `0`:
  `defectSq (E M) = 0`. The off-diagonal mass that *defined* the arrow is precisely the mass its limit
  kills. **`[proved]` for the instance** (`Orientation.Knowing.coh_image`). The geometric law
  `defectSq (T^n M) = ((1−p)²)^n · defectSq M` (`potential_geometric`) and `V → 0`
  (`potential_tendsto_zero`) witness that the arrow is genuinely *dissipative*.

So **on the genuine instance the converse is already a theorem**: `partialDephase p` is an arrow
(`dephaseArrow`), and its limit `dephase` is a knowing whose annihilated mass is the very monovariant
that defined the arrow. The instance closes by re-export. The content of the spec is the **lift**.

## 3. The veto-check (dual of `TimeFlow` §3) — rotation is the obstruction, and it is *energy*

The forward direction's veto was rotating peripheral spectrum threatening the monovariant. The
converse inherits the **same** veto, now load-bearing in the opposite way:

- **3a `[open]`** If `T` carries modulus-1 non-`1` eigenvalues, `lim_n T^n` **need not exist** — the
  orbit oscillates and there is no single limit map to call `E`. The Cesàro mean `(1/N)Σ T^n` still
  converges (mean-ergodic, §4) to a projection onto `Fix(T)`, but the off-diagonal mass on the
  rotating band **does not vanish**: `V` does not run to `0` there.
- **3b `[reading]`** That non-vanishing rotating mass is precisely what [`space-energy.md`](space-energy.md)
  assigns to **conserved energy / reversible time** (`Im(spec L)`). So the converse's failure mode is
  not a defect — it is the statement that *the rotating band of an arrow is not reducible to a
  knowing; it is feeling that is conserved rather than known.* Dissipative arrow ⟹ knowing; rotating
  remainder ⟹ energy. The two readings interlock.
- **3c `[proved]`, discharged for the instance** The real self-adjoint model has spectrum in `[0,1]`
  and **no rotating peripheral spectrum** (`Peripheral.dephase_no_rotating_peripheral`,
  `idempotent_eigenvalue`). So on the runnable instance the veto is vacuous and the orbit converges
  without caveat — `potential_tendsto_zero` is the honest regime where the converse is clean.

**Net:** the converse holds exactly on the **dissipative** part of any arrow. The clause "an arrow
reduces to a knowing" is true precisely modulo the conserved (energy) band, and that band is exactly
the part `space-energy.md` already declines to call knowing.

## 4. Ordered build (interface-first)

1. **`Arrow` interface — `[proved]`.** A `step` `T`, a potential `V ≥ 0`, a `Fix` set with
   `V = 0 ↔ Fix`, `V` antitone and strict off `Fix`. The dual of `TimeFlow.Flow`: same fields,
   opposite inference direction. `Arrow.toFlow` coerces to `Flow` and re-exports its order lemmas now
   satisfied — `V_orbit_antitone`, `V_orbit_strictAnti`, `V_drops_telescope`.
2. **Recover the instance — `[proved]`.** `dephaseArrow p` (`0 < p ≤ 1`) packages `partialDephase p`
   (via `dephaseFlow'`) as an `Arrow`; `arrow_limit_is_knowing`, `limit_idempotent`,
   `limit_is_seam_CE`, `limit_annihilates_potential` discharge by re-export from
   `TimeFlow` / `Orientation` / `SeamForcing`. This is the base case and it is *done* the moment the
   interface is wired, because every conjunct is an existing theorem about `dephase`.
3. **Mean-ergodic projection — `[open]`, route clear (`MeanErgodic.lean`).** For a power-bounded `T`
   on a finite-dim space, `(1/N)Σ_{k<N} T^k → P`, the projection onto `Fix(T)` along `range(1−T)`
   (finite-dim mean ergodic theorem). This is the main mathlib lever and is the keystone's first
   half. Tie `P` to the Perron–Frobenius eigenprojection already proved
   ([`PerronFrobenius.lean`](../../formal/Scratch/PerronFrobenius.lean)) and to the `P + N` split in
   [`SpectralDecay.lean`](../../formal/Scratch/SpectralDecay.lean).
4. **The lift: limit = conditional expectation — `[open]`** (`MeanErgodic.conjecture_R`). State and
   prove:

   > **Conjecture R (mean-ergodic recovery).** Let `T` be UCP and contractive on a finite-dim
   > C\*-algebra, self-adjoint for the GNS inner product of a faithful invariant state, with trivial
   > peripheral spectrum. Then `lim_n T^n` exists, equals the mean-ergodic projection `P`, and `P` is
   > a conditional expectation onto the `*`-subalgebra `Fix(T)`.

   The two non-trivial steps: (i) trivial peripheral spectrum collapses the Cesàro limit to the power
   limit (`lim T^n = P`); (ii) under GNS-self-adjointness `Fix(T)` is a `*`-subalgebra and `P` is a
   conditional expectation onto it (the multiplicative-core / Lindblad-type argument). This is the
   converse's analogue of Conjecture 3.7.4: the instance is elementary and proved, the general
   statement is real but bounded work, and naming the two steps is the point.
5. **Seam-recovery — `[open]` / `[reading]`.** `limit_is_seam_CE` recovers a conditional expectation
   onto *some* subalgebra (the fixed band). Whether that band is the **seam** algebra —
   self-inclusive, un-attendable — is recovered only up to the same `J ↔ genuine-seam` reading that
   `SeamForcing` leaves standing. `seam_forces_subalgebra` runs `seam ⊢ subalgebra`; the
   converse-of-the-converse `subalgebra ⊢ seam` (that a fixed band of an arrow must be self-inclusive)
   is **open** and is probably false without an extra hypothesis — most fixed bands are not seams.
   State it as a non-target, not a gap to paper over.

## 5. What is `[proved]` vs `[reading]` vs `[open]` at the end

- `[proved]`: on the genuine instance, **an arrow's limit is a knowing** — `partialDephase p` is a
  positive contraction with a strict monovariant, and its limit `dephase` is an idempotent
  conditional expectation (the seam-forced `knowSeam ∅`) onto a subalgebra whose annihilated
  off-diagonal mass *is* that monovariant. The converse holds, full stop, in the dissipative
  real-symmetric regime — `KnowingFromArrow.lean`, footprint `[propext, Classical.choice, Quot.sound]`.
- `[open]`: the general lift (Conjecture R, §4.4) — that *every* contractive UCP arrow with trivial
  peripheral spectrum recovers a conditional expectation. Route: mean-ergodic + multiplicative core.
- `[reading]`, unchanged from the forward direction: that the recovered `E` deserves the name
  *knowing* in the lived sense, and (downstream) that the relevant arrow is *physical/cosmic* time —
  the same gap physics itself leaves.
- **Out of scope by construction** (not a gap — see §6): that the recovered `E` is a *subject*, and
  that it *persists across an external interval*.

## 6. Scope — what a fully-proved converse does and does **not** reach

Even with Conjecture R discharged, the converse delivers exactly: *an irreversible arrow forces a
knowing — a conditional expectation onto a subalgebra, internal to the dynamics.* It does **not**
deliver the cosmic-subject claim, and the proofs say precisely why each missing step is missing:

| Step the cosmic claim needs | Supplied by the converse? | The proved obstruction |
|---|---|---|
| Arrow recovers *a knowing* (a conditional expectation) | **Yes** (instance `[proved]`, general `[open]` w/ route) | §2, `arrow_limit_is_knowing` |
| The knowing is a *subject* that cognizes | **No** | `E` is a conditional expectation (a partial trace), not a cognizer; nothing in the proof produces a subject |
| A knower *persisting across 13.8 Gyr* | **No** | A2 guard: `n` is internal return-depth; the theory has no external interval for "across 13.8 Gyr" to denote |
| A *total* self knowing *itself* whole | **No** | `self_inclusive_unmodelable`; the recovered `E` fixes the seam and provably *cannot* decohere it (`SeamForcing.self_cannot_fully_decohere`) — it is constitutively partial |
| The arrow in question is *cosmic time* | **No** (stays `[reading]`) | the standing identification gap, the same one physics leaves |
| A cosmos-spanning self exists at all | **No** | sparsity: `stab_density_tendsto_zero` makes selves nowhere dense; a maximal one is the rare-then-barred case |

So the converse **upgrades** the honest residue from
*"where there is an arrow, relations are lost under a contraction"* to
*"...and that contraction's limit is literally a knowing — a conditional expectation onto a
subalgebra."* That is a real strengthening of the structural claim. It still stops short of a
subject, of a persistent external knower, and of the totality knowing itself — each blocked by a
theorem already in the repo. The cosmic question is reached only by adding the standing `[reading]`
(cosmic time = relational time) on top, and even then yields "there is a knowing-structure under the
arrow," never "something has been knowing the cosmos."

## 7. Verification

`KnowingFromArrow.lean` builds sorry-free against mathlib v4.15.0; its instance theorems
(`arrow_limit_is_knowing`, `limit_idempotent`, `limit_is_seam_CE`, `limit_annihilates_potential`,
`potential_geometric`, `potential_tendsto_zero` at `dephaseArrow p`) depend only on
`[propext, Classical.choice, Quot.sound]` — verified, since each is a re-export of an already-verified
`TimeFlow`/`Orientation`/`SeamForcing` lemma. It is wired into the `Scratch` aggregator, so the
default `lake build Scratch` stays clean. `MeanErgodic.lean` carries the `[open]` lift (Conjecture R)
and holds a `sorry` placeholder until it is discharged; it is **gated out** of the default build (not
imported by `Scratch.lean`), so it warns only on explicit `lake build Scratch.MeanErgodic`. To
reproduce the instance core:

```
cd formal
lake build Scratch.KnowingFromArrow
```

---

*One line:* the forward chain proved `knowing ⟹ arrow`; this spec proves the converse on the genuine
instance — an arrow's limit **is** a conditional expectation onto a subalgebra, with the monovariant
the mass it annihilates — lifts it to all dissipative contractive arrows via one mean-ergodic
keystone (`[open]`), shows the rotating remainder is energy rather than knowing rather than a defect,
and certifies that even fully proved it reaches *a knowing under the arrow* but neither a subject, a
persistent external knower, nor a totality knowing itself.
