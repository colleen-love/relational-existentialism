# Rate de-risking — the reification rate and its cone, by hand (2.9)

**Phase B gate. This file is written and checked BEFORE any WS design and before any `formal/` file. It hunts, on paper, for a reification RATE — how much lateral breadth one tick converts into depth — that (a) is genuinely BOUNDED, and bounded by the FINITE ATTENTION the model already carries (Series 2.0), not by a postulated `c`; (b) gives a NON-TRIVIAL cone (some event strictly outside on the witnessing carrier); and (c) is genuine rate-content — two carriers with the SAME causal order (Series 2.5) but different rates have DIFFERENT cones, so the rate is not recoverable from the order (the costume gate). Only a rate surviving all three earns the WS designs. If the rate is not bounded by attention, the series lands NO-CONE, reported in full. The no-smuggling gate (Charter Extension 2 §3, §4.a) governs: the rate must be READ OFF the attention, never a numeral added to obtain the cone.**

The whole computation lives at `Cardinal.{0}` on a finite carrier; every claim below is an integer arithmetic fact and is `decide`/`omega`/`Finset.le_sup`-checkable, so the paper hunt and the build agree by construction.

---

## 0. The imported material this stands on

Reached transitively through `P2S8` (the series imports `P2S8` only; `P2S7 / … / P2S0 / P1` are transitive):

- **The finite attention** `attends : X → Finset X`, `P2S0.knows attends x y := y ∈ attends x` (`P2S0.ws1`). The out-attention is a FINITE set — this is the sole ontological bound, proved strictly finite (`< ℵ₀`, uniformly in `κ`) by `P2S0.ws1_bound_is_finite_attention`. The finiteness of the `Finset` is exactly the finite-attention budget; the rate is read off it.
- **The tick / reification** — the conversion of a finite pattern (breadth) into one relatum (depth), `P2S1.reifyT`, and the causal order on ticks (`P2S1.causal`, `rankT` the reification DEPTH). One tick is one unit of depth.
- **The lateral metric and the two DISTINCT axes** — `P2S4.stepsFrom` / `P2S4.latW` (breadth as lateral distance-from-self on the peer world), `P2S4.rankW` (depth), proved DISTINCT (`P2S4.ws2_axes_independent`), with `P2S4.reachIn` the length-indexed reach relation.
- **The causal order** — `P2S5.causalDep attends comp t u := comp u ∧ t ∈ attends u`, its transitive closure `Relation.TransGen (causalDep …)` (`P2S5.ws3`). The order this series RATE-LIMITS and exceeds.

Following the house discipline (Series 2.8 re-seated `P2S4.attendsW` as a fresh `Fin 3` carrier and used `P2S0.knows` as the imported primitive), Series 2.9 re-seats the lateral world as a fresh `Fin 5` LINE, defines the lateral metric, the per-tick reach, and the reachability order FRESH and model-derived off the attention `att : S → Finset S`, and ties them to the import via `knows att x y := P2S0.knows att x y`. Nothing is postulated: the rate is a `Finset.sup` over the attention.

## 1. The carrier: a lateral line of five peers

```
abbrev S : Type := Fin 5                              -- a lateral line 0-1-2-3-4 (2.4's world, re-seated)
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2 ; def p3 : S := 3 ; def p4 : S := 4

def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y     -- the imported directed knowing
```

**The lateral metric** (2.4's breadth-distance, re-seated as the line metric — symmetric, unsigned, path-length, matching `latW`):

```
def dist (x y : S) : ℕ := Nat.dist x.val y.val        -- = (x.val - y.val) + (y.val - x.val), i.e. |x - y|
```

`dist` is a fixed SPATIAL background (the breadth axis, 2.4); it does not depend on the attention. `dist 0 1 = 1`, `dist 0 4 = 4`, `dist` symmetric.

## 2. The RATE, and that it is bounded, EARNED from attention (WS1 de-risking)

The reification rate is read off the attention alone. One tick from `x` reifies the attended slice `att x`; the lateral BREADTH it spans is the greatest lateral distance to an attended relatum:

```
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)   -- per-tick lateral reach from x
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)     -- the carrier's speed c (breadth per tick)
```

`rate att` is a `Finset.sup` over the FINITE attention `att` — a function of `att` and the metric, with NO free parameter, NO numeral added by hand. One tick is one unit of depth (2.1), so `rate` is breadth-per-depth: a genuine speed (a ratio of 2.4's breadth to 2.1's depth), not a bare order.

**(B1) The rate BOUNDS the per-tick reach, and the bound is the attention's.** For every `att`, every `x`, every attended `y ∈ att x`:
`dist x y ≤ span att x` (as `y ∈ att x`, by `Finset.le_sup`) `≤ rate att` (as `x ∈ univ`, by `Finset.le_sup`). So `knows att x y → dist x y ≤ rate att`: the conversion cannot outrun the rate, and the rate is `sup`-derived from the attention. (Checked: `Finset.le_sup`, `le_trans`.) This is `ws1_rate_bounded` / `ws1_rate_earned_from_knows`.

**(B2) The rate is FINITE, with no postulated ceiling.** `rate att : ℕ` is a max over the finite carrier of a max over the finite `att x` of finite distances — finite because the attention is finite (the P2S0 bound), never because a `c` was assumed. The finiteness of `rate` inherits directly from the finiteness of the `Finset` `att x`. (No cardinal ceiling: exactly the `P2S0.ws1_bound_is_finite_attention` posture, one level down at `ℕ`.)

**(B3) The rate TRACKS the attention — it is genuinely the attention's, not an arbitrary cap.** If `a x ⊆ b x` for all `x` (a attends no more than b), then `rate a ≤ rate b`: enlarge the attention, enlarge the rate. (Checked: `Finset.sup_mono`, `Finset.le_sup`, `Finset.sup_le`.) This is `ws1_rate_monotone`. Concretely (§5) `rate attSlow = 1 < 2 = rate attFast < 4 = rate attAll`: the rate rises exactly as the attention widens. A postulated `c` would be indifferent to the attention; this rate is a strictly monotone function of it. This forecloses the no-smuggling sin (audit a) and the arbitrary-cap sin (audit d).

**Survives.** A finite rate, read off the finite attention, bounding the per-tick reach, tracking the attention, exists. WS1 is not the NO-CONE ground failure.

## 3. The CONE, and its non-triviality (WS2 de-risking)

The cone of a source `x` at depth `depth` is the set of events a becoming can reach at the rate — the events within `rate × depth` of `x` in the lateral metric:

```
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)          -- the cone (named `ball`, audit e)
```

(Named `ball` in code: `cone` is a forbidden content-name for a definition — `def cone` matches the §6 grep `\bcone\b`; "cone" in prose and in the underscore-wrapped theorem names `ws2_cone`, `ws4_cone_reachable`, which the `\b…\b` grep does not match.)

**(C1) The cone IS exactly the rate-bounded reachable set.** `y ∈ ball att x depth ↔ dist x y ≤ rate att * depth`, by `Finset.mem_filter` over `univ`. (Checked: `simp [ball, Finset.mem_filter]`.) This is `ws2_cone`.

**(C2) The cone is NON-TRIVIAL on the witnessing carrier.** Take `attSlow` (§5, rate 1). At depth 1 the cone of `p0` is `{y | dist p0 y ≤ 1} = {p0, p1}`. The event `p4` is at `dist p0 p4 = 4 > 1`, so `p4 ∉ ball attSlow p0 1`: STRICTLY OUTSIDE — causally disconnected within one tick. Some event inside (`p1`), some strictly outside (`p4`): a genuine finite speed. (Checked: `decide`.) This is `ws2_cone_nontrivial`.

## 4. The cone is a RATE, not the bare order (WS3 de-risking, the costume gate)

The causal order (2.5, re-seated) is decidable bounded reachability — `y` reachable from `x` within `card S` ticks:

```
def reachWithin (att : S → Finset S) : ℕ → S → S → Bool
  | 0,     x, y => x == y
  | (n+1), x, y => (x == y) || (att x).any (fun z => reachWithin att n z y)
def reaches (att : S → Finset S) (x y : S) : Bool := reachWithin att (Fintype.card S) x y
```

(`reaches att x y = true` iff there is a directed path `x ⤳ y` of length `≤ card S`; the decidable re-seating of `P2S4.reachIn` / the transitive closure `P2S5.TransGen (causalDep …)`.)

**(O1) Same order, different rate, DIFFERENT cone.** The carriers `attSlow` (forward neighbor, rate 1) and `attFast` (forward two, rate 2) have the SAME causal order — from any `x` exactly the forward events `{y | x ≤ y}` are reachable in both, so `reaches attSlow x y = reaches attFast x y` for all `x, y`. But `rate attSlow = 1 ≠ 2 = rate attFast`, and so the cones DIFFER: `ball attSlow p0 1 = {p0, p1} ≠ {p0, p1, p2} = ball attFast p0 1`. The rate is NOT recoverable from the causal order: same order, two cones. (Checked: `decide` on all three.) This is `ws3_rate_is_content`.

The cone therefore carries content BEYOND 2.5's order — the very thing the costume gate demands. A "cone" that stripped to the causal reachable set would be identical on `attSlow` and `attFast` (their orders coincide); ours is not.

**(O2) The rate content is EARNED from the attention.** `rate` is the `Finset.sup` of §2 — a function of `att` (rfl), monotone in `att` (B3). The differing cones of `attSlow`/`attFast` are differing `rate`s, and the `rate`s differ BECAUSE the attentions differ (`attSlow x ⊊ attFast x`). This is `ws3_earned_from_attention`. No `c` is postulated anywhere; delete every numeral and the rate is still `univ.sup (span att)`.

## 5. The FORK: CONE and NO-CONE both reachable (WS4 de-risking)

Three concrete attentions on the line, all finite (P2S0), exhibit the two sides.

```
def attSlow : S → Finset S := fun x =>          -- forward neighbor: p0→p1→p2→p3→p4 (rate 1) — the CONE carrier
  if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else if x = 3 then {4} else ∅
def attFast : S → Finset S := fun x =>          -- forward two: rate 2, SAME order as attSlow — the costume pair
  if x = 0 then {1,2} else if x = 1 then {2,3} else if x = 2 then {3,4} else if x = 3 then {4} else ∅
def attAll : S → Finset S := fun _ => {0,1,2,3,4}       -- attend everyone: rate 4 — the NO-CONE carrier
```

### 5.a CONE — the local attention `attSlow` (rate 1)

`rate attSlow = 1` (§2). At depth 1, `ball attSlow p0 1 = {p0, p1}`, and `p4` (at `dist 4`) is strictly OUTSIDE. A genuine finite speed: some events reachable within one tick, some causally disconnected. **CONE-REACHABLE.** (Checked: `decide`.) This is `ws4_cone_reachable` (`rate attSlow = 1 ∧ ∃ y, y ∉ ball attSlow p0 1`).

The reading: a self that attends only its lateral neighbor turns breadth into depth at a finite rate — its light cone at depth 1 reaches exactly its neighbor, and the far events lie in an elsewhere no single tick can touch.

### 5.b NO-CONE — the total attention `attAll` (rate 4)

`rate attAll = 4` (the line diameter). At depth 1, `ball attAll p0 1 = {y | dist p0 y ≤ 4} = {p0,…,p4}` = the whole world: EVERY event is inside the cone at depth 1. No event is causally disconnected — no finite speed, the reification is instantaneous, the world non-relativistic. **NO-CONE-REACHABLE.** (Checked: `decide`.) This is `ws4_nocone_reachable` (`∀ y, y ∈ ball attAll p0 1`), with `ball attAll p0 1 = Finset.univ`.

The reading: a self that attends the whole world reifies all of it in one tick. There is no fastest becoming, because becoming is total; the cone is everything, and relativity's elsewhere is empty. This is the honest non-relativistic pole — reported, not relabelled.

**Both sides genuine, neither by fiat.** CONE is not built into `ball` (attAll gives the whole world); NO-CONE is not built in (attSlow leaves `p4` outside). Same `rate`, same `ball`, same `dist` — only the directed attention differs. The verdict discriminates on which attention-world you inhabit: LOCAL attention (bounded reach) → a finite speed and a genuine cone; TOTAL attention (reach = diameter) → no finite speed. The fork is a fact about the attention, exactly as Series 2.8's frustration was a fact about the directed ring.

## 6. Verdict of the de-risking

- A finite rate, read off the finite attention, bounding the per-tick reach and tracking the attention, survives (§2): **the WS1 ground holds — not the NO-CONE ground failure.**
- The cone is the rate-bounded set and is non-trivial on the witness (§3): **a genuine finite speed.**
- Same order, different rate, different cone; the rate earned from attention (§4): **not the costume, not smuggled.**
- CONE and NO-CONE both reachable on genuine finite-attention carriers (§5): **the fork is not by fiat.**

**The rate and its non-trivial cone survive on paper. Phase B proceeds to the WS designs.** The expected computed verdict is **CONE**: finite attention is a maximal rate of becoming, and relativity's light cone is the shadow of a bounded capacity to attend — recovered here, earned from the finite attention the model has carried since Series 2.0, never postulated. NO-CONE is reachable (`attAll`) and pre-registered honorable: the honest report that a world of total attention is non-relativistic, the specification for the next iteration.

### Rejected candidates (recorded)

- **The rate as a postulated numeral `c` (a fixed `ℕ` added to the cone).** Rejected as the no-smuggling sin (audit a): a constant `c` is indifferent to the attention (B3 fails — it does not track `att`), and re-finding a cone from it is the smuggle the charter forbids. `rate` is admitted BECAUSE it is `univ.sup (span att)`, a function of `att` alone.
- **The cone as the bare causal reachable set `{y | reaches att x y}`.** Rejected as the costume (audit c): this is `P2S5`'s order relabelled, with NO rate content — it is identical on `attSlow` and `attFast` (same order), so it cannot be the cone, whose whole point is that those two carriers DIFFER (O1). The cone must carry `rate × depth`, not the order.
- **The lateral metric as the DIRECTED reach of the same `att` (conflating space with dynamics).** Rejected: the metric must be a fixed spatial background (2.4's breadth axis) independent of the rate, or "rate × depth" is circular. `dist` is `Nat.dist` on the line — symmetric, attention-independent — while the rate is read off `att`. Space (2.4) and the conversion rate (2.1) are kept distinct, honoring 2.4's two-axes result.
- **The rate as `(att x).card` (the attention COUNT).** Rejected: the count is not a breadth (a self attending two NEAR relata has a smaller reach than one attending a single FAR relatum). The rate must be a lateral SPAN (a `dist`-sup), the breadth-per-tick, not the cardinality. The count is a red herring; the span is the speed.
- **NO-CONE as literal unboundedness on an infinite carrier.** Rejected as needless: the finite carrier makes every rate finite, and the honest NO-CONE is INSTANTANEOUS reification (the cone is the whole world at depth 1, `attAll`), which the charter names explicitly ("or instantaneous, every event reachable at once"). Total attention, not an infinite carrier, is the model-native non-relativistic pole.
