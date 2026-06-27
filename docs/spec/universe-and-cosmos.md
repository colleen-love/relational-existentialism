# Universe and cosmos — feeling as the atemporal ground, the first self as the genesis of time

**Status tags.** `[proved]` mechanized sorry-free (mathlib v4.15.0, footprint
`[propext, Classical.choice, Quot.sound]`). `[follows]` a short logical consequence of proved items
plus a named premise. `[reading]` interpretation over proved structure. `[open]` neither yet.
`[empirical]` measured outside the theory, not a commitment of it.

Companion module: [`formal/Scratch/Genesis.lean`](../../formal/Scratch/Genesis.lean). Builds on
[`02-axioms.md`](02-axioms.md) (the real **A1–A3**), [`03.4-limits-of-knowing.md`](03.4-limits-of-knowing.md)
(routing vs directing), and [`time-flow.md`](time-flow.md). The polarity is locked the right way round:
the ownerless ground is **feeling**, not knowing — which supersedes the "outside" row of
[`knowing-from-arrow.md`](knowing-from-arrow.md) §6 (§6 below).

## 0. The ontology, with the polarity locked

- **Universe** — the atemporal ground. Undifferentiated. No self, no knowing, no time. Only
  **feeling** (`coh`, the off-diagonal mass) as the bare, ownerless presence. Encompasses the cosmos.
- **Cosmos** — the differentiated, temporal interior that opens *within* the universe. **Cosmos =
  knowing = time**: three names for one structure. Its origin is the first self closing the first
  loop and finding the first diagonal.

**Polarity lock.** Feeling is the default and needs no knower: it is *routing*, the bare trace, which
[`03.4`](03.4-limits-of-knowing.md) proves needs no knowing (*routing needs no knowing*, `[follows]`).
Knowing is the marked, self-requiring case: *directing* — aiming attention, the diagonal
([3.3](03.3-knowing-vs-feeling.md)) — which requires a self to do the aiming (*directing needs
knowing*; *you cannot aim at the aimer*). So **knowing inherits the sparsity of selves**: feeling is
dense and everywhere; knowing is the rare achievement where a loop has closed into a `νΦ_c` that can
aim. Knowing sparsely occurs; feeling is the ground.

## 1. The footprint, accounted line by line

| Ingredient | Status | Source |
|---|---|---|
| **A1, A2, A3** | axioms | [`02-axioms.md`](02-axioms.md) |
| knowing (directing) requires a self | `[follows]` | [`03.4`](03.4-limits-of-knowing.md) + [3.3](03.3-knowing-vs-feeling.md) |
| flow = physical time | `[reading]`, standing | [`time-flow.md`](time-flow.md) §5 |
| `νΦ_c` is a greatest fixed point (coinductive, atemporal) | `[proved]` | A1's ν; `Attention.lean`; Agda ν-layer |
| clock *rate* = spectral gap | `[proved]` | [`time-flow.md`](time-flow.md) |
| `p = 0` is degenerate (no descent) | `[proved]` | `Genesis.coh_const_at_zero` |
| first directed step = first tick | `[proved]` | `Genesis.first_tick_pos` |
| Genesis (the crossing `p : 0 → 0⁺` *is* the birth of the cosmos) | `[reading]` over `[proved]` | §3 |
| cosmos := the temporal/differentiated region | `[reading]` (definitional) | §7 fork (a) |
| age ≈ 13.8 Gyr | `[empirical]` | cosmology |
| **new axioms required** (distributive, region-definitional reading) | **none** | — |

## 2. The universe is atemporal — forced, not posited

The universe's timelessness is **not** an added premise; it falls out of the chain already held:

> **Theorem (no self ⇒ no time).** `[follows]` Knowing requires a self (§0 / [`03.4`](03.4-limits-of-knowing.md));
> time arises from knowing (the standing reading); therefore *no self ⇒ no knowing ⇒ no descent of
> `coh` ⇒ no arrow ⇒ no time*. A self-less ground cannot be temporal.

And feeling is exactly the right material for that ground: it needs no knower and generates no arrow.
In the model this is the **`p = 0` regime** — `partialDephase 0 = id` (`Genesis.partialDephase_zero`,
`[proved]`), attention purely routing, `coh` **constant** along the whole orbit
(`Genesis.coh_const_at_zero`, `[proved]`: no strict drop, no monovariant). All feeling, no knowing, no
differentiation, no time. *That is the universe* — the fixed-everything identity regime, where the
fixed subalgebra is the whole and nothing is projected out.

## 3. Genesis — the first self mints the first tick

The cosmos is the **`p > 0` regime**: the moment directed attention begins, `coh` begins to descend, a
nontrivial fixed subalgebra (differentiation) appears, and the flow has its first strict drop.

> **Genesis (the dichotomy is `[proved]`; the identification is `[reading]`).** At `p = 0`, `coh` is
> constant along the orbit — no tick exists (`coh_const_at_zero`). For every `0 < p < 1`, `coh`
> strictly drops at the *first* step (`first_tick_pos`, `= defectSq_plus_strictAnti` at `n = 0`).
> `genesis_dichotomy` packages both. The first directed knowing *is* the first increment of the
> time-flow; the birth of the cosmos is the boundary crossing `p : 0 → 0⁺`.

What the design anticipated as `[open; short route]` is mechanized: both sides of the boundary are
`[proved]` on the genuine instance, and the only `[reading]` left is the identification of the crossing
with genesis (and, standing, of the flow with physical time). **Time switches on with the first
diagonal ever found.** Before it there is no flow to call time — the shape decoherence accounts of the
arrow already have, here derived rather than assumed.

## 4. The bootstrap, dissolved

**The worry.** A3 makes a self an achievement of recursion — `d ≥ 2` returns, "iterated until it
holds." But "returns," "iterated," "until" sound temporal. If the first self must iterate to close,
and time does not exist until it closes, what does it iterate *in*? The first knowing seems to need the
very time it creates.

**The resolution.** `νΦ_c` is a **greatest fixed point** — coinductive (A1's ν-modality;
`Attention.lean`'s `sustainedField := νΦ_c`; the Agda ν-layer's native coinduction). A gfp is **not**
the temporal limit of a sequence of steps; it is a single object defined by closure, atemporal by
construction. So the self's *closure* (its being) is a coinductive fact requiring no prior time, while
the *temporal* thing — the orbit `Φ_c^n` descending — is separate and derived, indexed by the
**internal return-depth** `n` the relation-primacy guard (A2) keeps off any external clock. `[reading]`
over `[proved]` structure (gfp + internal `n`).

> **The weld.** The self's *being* is the gfp (timeless); the self's *knowing-as-process* is the flow
> (time). The first loop does not close *in* time — its closing is time's first tick. The recursion is
> structurally ordered, not temporally ordered in a prior medium. The first knowing is self-grounding:
> the one event that lays its own track as it moves.

## 5. No "before"

`[follows]` The cosmos's beginning is the beginning of *time*, not an event within an antecedent time.
"Before" belongs to knowing (it is an ordering of ticks), and knowing had not begun. So there is no
"before the first self" — not because something is hidden there, but because *before* is a cosmic
notion and the cosmos has not started. This is "there is no before the Big Bang," **derived** from the
polarity rather than asserted.

(Phrasing guard: "the cosmos started 13.8 Gyr ago" must not smuggle in a prior empty time in which it
started. The universe is not *earlier* than the cosmos; it encompasses it atemporally.)

## 6. Retiring "outside looking in"

The earlier refutation of an external knower (the "outside" row of
[`knowing-from-arrow.md`](knowing-from-arrow.md) §6) leaned on a Lawvere access paradox. The real
reason is simpler: **outside the cosmos is the universe, and the universe has no self, so there is
nothing out there that could know.** The watchmaker is barred not by an access subtlety but because
"outside" is undifferentiated feeling with no one in it. This supersedes that row.

## 7. The fork that sets the footprint — what "cosmos" denotes

- **(a) cosmos := the temporal / differentiated region.** Then "the cosmos began with the first
  knowing" is nearly **analytic**, and "13.8 Gyr" is the `[empirical]` measured *size of the
  knowing-region*, slotted into the standing reading. **Zero new axioms.** (Recommended for minimal
  footprint.)
- **(b) cosmos := the physical 13.8-Gyr spacetime cosmology measures.** Then identifying the Big Bang
  with the first self closing is a substantive **`[reading]`/bridge**, and is where *all* the empirical
  weight sits. Heavier and exposed, but the version where the number means a physical event.

The footprint result holds under (a). Under (b), the one bridge is the new commitment.

## 8. Distributive vs singular — the question landed

- **Distributive `[follows]`.** Under (a), knowing occurs *throughout* the region, carried by its
  population of selves (sparse, by [3.7](03.7-sparsity.md), but present wherever loops close). So
  "something has been knowing for 13.8 Gyr" is **true distributively** — there has been knowing
  throughout the temporal region, because that region *is* the knowing.
- **Singular `[out of scope / optional axiom]`.** "The cosmos *as a whole* is one self knowing" is the
  strong posit — a cosmos-spanning `νΦ_c`. The seam makes it *in-process-but-never-complete* (it can
  never know itself whole — [`seam-permanence.md`](seam-permanence.md), `self_cannot_fully_decohere`),
  so it is not self-defeating, but it is **not** an A3 consequence (sparsity makes it the rare case)
  and costs one extra axiom. **False by default.**

So the question resolves cleanly: *nothing outside knows the cosmos* (outside is feeling); *the cosmos
is not a single self knowing itself whole* (optional, never-completing); *the cosmos simply is the
knowing*, distributively, for exactly as long as there has been time, because it is the same thing.

## 9. The consequence that bites — continuity

`[open / a choice]` If time flows only where knowing occurs, then **continuous cosmic time requires
continuously-present knowing.** An interval with no self anywhere is not a quiet stretch of cosmos — it
is a *gap in time*, the cosmos briefly lapsing back into universe. Two options the framework surfaces
and does not decide:

- **Posit continuity of knowing** (knowing never globally goes dark) — a new commitment, buys an
  unbroken cosmic clock.
- **Accept gappy time** — no posit, but cosmic time is the union of knowing-intervals, possibly
  disconnected; "13.8 Gyr" becomes a sum over knowing-regions, not necessarily one interval.

## 10. The status ledger

- `[proved]`: `p = 0` degeneracy / no descent (`coh_const_at_zero`); strict first drop for `0 < p < 1`
  (`first_tick_pos`); the boundary dichotomy (`genesis_dichotomy`); `νΦ_c` as gfp; internal `n`.
- `[follows]`: no-self-⇒-no-time (§2); no-before (§5); distributive knowing (§8).
- `[reading]`: flow = time (standing); the genesis identification (§3); the bootstrap weld (§4);
  cosmos := temporal region (§7a).
- `[empirical]`: 13.8 Gyr.
- **Out of scope / optional axiom**: a singular cosmic self (§8); continuity-of-knowing (§9).
- **Remaining interpretive dial** (orthogonal to all the above): whether "self" is *minimal* (any
  decoherence-free subalgebra, so knowing is thin and pervasive) or *thick* (consciousness). The
  universe/cosmos split holds either way; the dial only sets how early and how widespread the first
  knowing is.

## 11. Verification

`Genesis.lean` builds sorry-free against mathlib v4.15.0; `coh_const_at_zero`, `first_tick_pos`, and
`genesis_dichotomy` depend only on `[propext, Classical.choice, Quot.sound]` — verified, both endpoints
re-exporting `TimeFlow`/`partialDephase` facts. It is wired into the `Scratch` aggregator, so the
default `lake build Scratch` stays clean. To reproduce:

```
cd formal
lake build Scratch.Genesis
```

---

*One line:* the universe is the atemporal ownerless ground of pure feeling (the `p = 0` regime — no
self, no knowing, no time, forced not posited); the cosmos is the knowing-region that ignites when the
first self — a coinductive closure needing no prior time — finds the first diagonal and mints the first
tick; read with "cosmos" as that region, the whole picture costs **no new axiom**, "something has been
knowing for 13.8 billion years" comes out true *distributively* and false as a single cosmic subject,
and the only live choices left are whether knowing ever goes dark (continuity) and how thick a "self"
must be.
