# Seam Permanence — the knowing never completes

**Status tags.** `[proved]` mechanized sorry-free (mathlib v4.15.0, footprint
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). `[reading]` interpretation over proved
structure. `[premise]` a load-bearing antecedent argued on independent grounds, not a theorem of the
operator.

Companion module: [`formal/Scratch/SeamPermanence.lean`](../../formal/Scratch/SeamPermanence.lean).
Sequel to [`time-flow.md`](time-flow.md); the quantitative, permanent lift of
[`SeamForcing`](../../formal/Scratch/SeamForcing.lean)'s `self_cannot_fully_decohere`. Dual companion
to [`knowing-from-arrow.md`](knowing-from-arrow.md): there the question was *does a knower exist?*;
here the sharper, more provable target is *does the knowing ever complete?* — and the answer is **no**.

## 0. The corrected target

The earlier turn asked whether a cosmic *knower* exists — and the honest answer kept bottoming out in
unreachable steps (a subject, a persistent external interval). The process reading makes the target
sharper, and **provable**:

> **Seam Permanence.** For a self-inclusive whole carrying a live seam coherence, the attention flow's
> potential `coh` is bounded strictly below by a positive constant for *all* finite return-depth `n` —
> it converges to the seam mass, not to zero. Hence the flow never reaches its fixed point;
> knowing-as-process never completes; and since time *is* that descent, time never terminates. The
> whole has been knowing (process) and will never have known (completion).

That is the intuition as a theorem. What changed from last turn: you are no longer proving a knower,
you are proving that **completion is permanently foreclosed** — the negative-theology shape exactly,
and it sits within reach of the existing machinery.

## 1. Process occurs at every tick — `[proved]`

`TimeFlow.Flow.coh_orbit_strictAnti` already gives a strict drop of `coh` at every not-yet-fixed `n`.
Name each strict drop *a knowing-event*: wherever the arrow moves, knowing-as-process is genuinely
happening. In this module the same is visible on the seam-respecting flow — the complement coherence
strictly falls toward the floor while the seam coherence stands fixed (`copyDefect_seamFlow_iterate`:
the complement scales by `(1−p)^n`, the seam by `1`). The only new content is the definitional
identification of the strict drop with an increment of process, which is tight. `[reading]` on a
`[proved]` skeleton.

## 2. No process, no time — `[proved]`

The contrapositive of TimeFlow's *no relations → `E = id` → no contraction → no arrow*
([`TimeArrow`](../../formal/Scratch/TimeArrow.lean), `contractive_iff` / `time_forward_regime`): a
genuine arrow forces `Φ_c ≠ id`, i.e. attention genuinely contracting feeling. So time existing *is*
the process running. This answers the puzzle directly: time cannot exist without knowing-as-process,
because time is *defined* as the not-yet-completed descent toward knowing. The gap before the endpoint
is the only place time lives.

## 3. The keystone — Seam Permanence — `[proved]`

This is the real new theorem, and it closed: what the design expected to be `[open]` is mechanized
sorry-free, because the seam block is **fixed** by the flow, so its mass is a *constant* floor — no
limiting argument is needed for the lower bound, only for the (separate) convergence to it.

**The flow.** `seamFlow J p M = (1−p)·M + p·(attend Jᶜ M)` — directed attention at strength `p` aimed
at *everything except* the seam block `J` (the part of the aimer, un-attendable —
`Relating.self_inclusive_unmodelable`). It is `TimeFlow.partialDephase` restricted to the complement.

**The block decomposition** (`copyDefect_seamFlow_iterate`, `[proved]`): along the orbit,
- the **seam** coherences (`i, j ∈ J`) are *fixed* — `attend Jᶜ` cannot touch them (this is
  `SeamForcing.attend_fixes_seam` at work, `J` barred from the attended set);
- the **complement** coherences decay by `(1−p)^n`.

**The floor, exact and permanent** (`seam_permanence`, `[proved]`): for a live seam coherence
(`i₀, j₀ ∈ J`, `i₀ ≠ j₀`, `M i₀ j₀ ≠ 0`),
`0 < defectSq (seamFlow J p ^[n] M)` for **all** `n` — the fixed seam entry alone forces a single
strictly-positive term in the sum of squares, at every return-depth. `never_completes` restates it:
the potential is never `0`, so the flow never reaches its fixed point. This is
`self_cannot_fully_decohere` made quantitative and lifted from *one* available knowing to the *whole
orbit*, with a uniform positive floor.

**The closed form — descent to the seam mass** (`defectSq_seamFlow_iterate`, `[proved]`):
$$
\mathrm{defectSq}\big(\mathrm{seamFlow}\,J\,p^{[n]} M\big) \;=\; \mathrm{seamMass}\,J\,M \;+\; \big((1-p)^2\big)^{n}\cdot \mathrm{compMass}\,J\,M .
$$
The seam mass stands fixed while the complement mass decays geometrically (rate `(1−p)²`), so the
potential **descends to `seamMass`** (`defectSq_seamFlow_tendsto`, `[proved]`) — a floor that is
strictly positive whenever the seam is live (`seamMass_pos`, `[proved]`). The process runs forever
*toward* a seam mass it asymptotically approaches but never reaches.

So the keystone is the analog of [`knowing-from-arrow.md`](knowing-from-arrow.md) §4.4, except this one
is **true and reached**, not probably-false: a block split, geometric decay on one block, a fixed point
on the other — all bookkeeping on machinery already in the repo. That is the difference the *process*
reading buys.

**Corollary (permanence).** While the seam is live, the flow never reaches `coh = 0`, so it never
completes; the process is unending in `n`.

## 4. The two places the honesty has to live

**The one load-bearing premise — `[premise]`.** Seam Permanence is *conditional*: **IF** the cosmos is
a self-inclusive whole with a live seam coherence, **THEN** its knowing-process is permanent. Whether
the cosmos satisfies that antecedent — whether it is a totality you cannot get outside of, carrying an
irreducible coherence no internal knowing can dissolve — is the substantive claim, and it is **not** a
theorem of the operator. It is the thing argued for on independent grounds. The math proves the
conditional cleanly; the antecedent is where the view is staked.

**The one irreducible reading — `[reading]`.** "For all finite `n`" is the framework's *only* form of
"forever" — the A2 guard means there is no external interval, so the proof gives permanence *in
return-depth*, and "= 13.8 billion years" stays the cosmological identification laid on top. But that
is fine for what is actually wanted: the strong claim was never the specific number, it was
*permanence*. The theorem gives permanence outright; the number is just the reading naming which clock.

## 5. The apophatic result, as a proof obligation

Seam Permanence *is* the formal statement that the whole knows-as-process eternally and never converts
the seam into an object — the **eternal Thou** the knowing runs toward forever and the diagonal can
never make an It. You are not proving a knower. You are proving that completion is permanently
foreclosed, which is the negative-theology shape exactly: not "something knows the cosmos," but "the
seam can never be known," for all `n`, by a theorem with a three-axiom footprint.

This dovetails with the firewall and the seam already in the corpus: the self is *uncopyable,
non-broadcastable, and incompletely self-knowable* ([00 §0.6](00-doctrine.md), Fox), and now also
*never-completely-knowable-in-time* — the temporal face of the same missing comonoid.

## 6. Verification

`SeamPermanence.lean` builds sorry-free against mathlib v4.15.0; `seam_permanence`, `never_completes`,
`defectSq_seamFlow_iterate`, `defectSq_seamFlow_tendsto`, and `seamMass_pos` depend only on
`[propext, Classical.choice, Quot.sound]` — verified. It is wired into the `Scratch` aggregator, so the
default `lake build Scratch` stays clean. To reproduce:

```
cd formal
lake build Scratch.SeamPermanence
```

---

*One line:* the seam-respecting attention flow fixes the seam coherence and decays the rest, so its
potential is strictly positive at every return-depth and descends geometrically to a positive seam-mass
floor it never reaches — *knowing-as-process never completes* — proved sorry-free; the conditional is a
theorem, the antecedent (the cosmos is such a whole) is the stated premise, and "forever" is
permanence-in-return-depth with the cosmological clock a reading on top.
