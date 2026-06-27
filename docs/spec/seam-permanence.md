# Seam Permanence — the knowing never completes

> A derivation sequel to [03 — Theorems](03-theorems.md) (see the [spec index](README.md)), the
> quantitative lift of [`SeamForcing`](../../formal/Scratch/SeamForcing.lean)'s
> `self_cannot_fully_decohere`. Mechanized in
> [`Scratch/SeamPermanence.lean`](../../formal/Scratch/SeamPermanence.lean). Status tags as in
> [03](03-theorems.md); `[premise]` marks a load-bearing antecedent argued on independent grounds, not
> a theorem of the operator.

---

## The capstone

> **Theorem (Seam Permanence).** For a self-inclusive whole carrying a live seam coherence, the
> seam-respecting attention flow's potential `coh` is bounded strictly below by a positive constant for
> **all** finite return-depth `n`, and converges to the seam mass — not to zero. The flow never reaches
> its fixed point; knowing-as-process never completes. *The whole has been knowing and will never have
> known.*

What made this provable (where the cosmic *knower* question kept bottoming out): the seam block is
**fixed** by the flow, so its mass is a *constant* floor — the lower bound needs no limiting argument,
only the (separate) convergence to it. The flow is `seamFlow J p = (1−p)·id + p·(attend Jᶜ)` — directed
attention aimed at everything *except* the un-attendable seam `J` (you cannot aim at the aimer).

## What is proved

`[proved]` (footprint `[propext, Classical.choice, Quot.sound]`):

- `copyDefect_seamFlow_iterate` — the **block decomposition**: along the orbit the seam coherences
  (`i, j ∈ J`) are *fixed* while the complement decays by `(1−p)^n`.
- `seam_permanence` / `never_completes` — for a live seam coherence (`i₀, j₀ ∈ J`, `i₀ ≠ j₀`,
  `M i₀ j₀ ≠ 0`), `0 < defectSq(seamFlow J p ^[n] M)` for **every** `n`; the potential is never `0`, so
  the flow never reaches its fixed point.
- `defectSq_seamFlow_iterate` — the closed form `defectSq = seamMass + ((1−p)²)^n · compMass`: the seam
  mass stands fixed while the complement mass decays geometrically.
- `defectSq_seamFlow_tendsto` / `seamMass_pos` — the potential descends to a floor `seamMass`, strictly
  positive whenever the seam is live. The process runs forever *toward* a seam it never dissolves.

This is the all-`n`, uniform-floor lift of `self_cannot_fully_decohere` (which gave one available
knowing; this gives the whole orbit a positive floor).

## Honest scope

- `[premise]` Seam Permanence is **conditional**: *if* the whole is self-inclusive with a live seam
  coherence, *then* its knowing-process is permanent. Whether a given whole (e.g. the cosmos) satisfies
  that antecedent is the substantive claim, argued on independent grounds — not a theorem of the
  operator.
- `[reading]` "For all finite `n`" is the framework's only form of "forever" — the A2 guard means there
  is no external interval, so the proof gives permanence *in return-depth*, with any external-clock
  identification laid on top. The theorem gives permanence outright; the number is just the clock named.

The apophatic shape: this is not "something knows the cosmos" but "the seam can never be **known**," for
all `n` — completion is permanently foreclosed, the eternal Thou the diagonal can never make an It. It
is the temporal face of the same missing comonoid that makes the self uncopyable and non-broadcastable
([00 §0.6](00-doctrine.md), Fox).

**Provenance.** `R / S` — geometric decay and conditional-expectation theory rederived; the synthesis
is the permanent positive floor of self-knowing. See [05 — Provenance](05-provenance.md).

---

→ Back to [03 — Theorems](03-theorems.md) · the seam machinery is [3.5](03.5-decoherence.md) and
[`time-flow.md`](time-flow.md) §"the seam fixes the target" · the distributed reading is
[`distributed-self.md`](distributed-self.md).
