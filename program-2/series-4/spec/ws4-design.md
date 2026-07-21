# WS4 design — The two-axes fork (the knot) (2.4)

**Prove the two axes are DISTINCT: breadth is a genuine directed, granular, self-relative metric INDEPENDENT of
rank, with both a lateral-move-without-rank-change and a rank-move-without-lateral-change witnessed on the world.
The REDUCED alternative — breadth is accumulated depth, every attention step changes rank, same-rank peers
collapse, no world but a taller tower — must be GENUINELY REACHABLE (the fork not by fiat), and the verdict a
discriminating function reaching more than one value. This is the genuinely-uncertain knot.**

## 1. Candidate constructions

1. **DISTINCT asserted by typing (independence holds on every structure).** REJECTED: a fiat. If `lat` and
   `rank` were independent by construction on every carrier, REDUCED would be excluded and the fork empty
   (audit b).
2. **A concrete collapsed witness `T` where the axes coincide (CHOSEN).** Build a tower `T = Fin 3`
   (`tw0 → tw1 → tw2`, `attendsT` a reification line) where EVERY attention step is a reification step, so
   `latT = rankT` as functions: breadth IS accumulated depth, the two axes COINCIDE, and independence FAILS.
   `T` realizes REDUCED as a genuine structure. The fork is then: `W` in the DISTINCT zone (axes independent),
   `T` in the REDUCED zone (axes coincide), both built, the verdict discriminating. See `spec/README.md` §2.2.

## 2. Triage

- **Fork genuine, no fiat (audit b).** DISTINCT holds on `W`; REDUCED holds on `T` (`latT = rankT`). Both zones
  are witnessed by real carriers, so the distinctness does not hold by typing (it fails on `T`) and REDUCED is
  not excluded by construction. The verdict function reaches both values.
- **No costume (audit c).** The verdict rests on axis-INDEPENDENCE (the cross-pattern of separations, `W`) versus
  axis-COINCIDENCE (`latT = rankT`, `T`), NOT on the number of peers. `T` has a population too, yet lands
  REDUCED, precisely because its axes coincide. The multiplicity (Series 07) is the ground both share; the
  finding is which zone the axes fall in.
- **Both moves witnessed.** The lateral-move-without-rank (`w0,w2` same rank, `lat`-separated) and the
  rank-move-without-lateral (`r,w0` same `lat`, `rank`-separated) are the two moves, both on `W` (from WS2).
- **Strip test.** The payoff strips to "a discriminating function over axis-independence, reaching two values,
  both witnessed by a structure."

## 3. Winning construction — typed signatures

```
-- The collapsed (REDUCED) witness
abbrev T : Type := Fin 3
def tw0 : T := 0   def tw1 : T := 1   def tw2 : T := 2
def attendsT : T → Finset T          -- tw0↦{tw1}, tw1↦{tw2}, tw2↦{tw2}
def rankT : T → ℕ                    -- tw0↦0, tw1↦1, tw2↦2
def latT  : T → ℕ                    -- tw0↦0, tw1↦1, tw2↦2  (= rankT: breadth is accumulated depth)

-- (A) on T the axes COINCIDE: the lateral coordinate is the reification rank (REDUCED realized)
theorem ws4_reduced_reachable : latT = rankT
  ∧ ∀ x y : T, (latT x = latT y ↔ rankT x = rankT y)     -- same pairs identified: axes not independent

-- (B) on W the axes are INDEPENDENT with both moves witnessed (imported from WS2)
theorem ws4_distinct_witnessed (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ rankW w0 = rankW w2 )    -- lateral move, no rank change
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ latW r = latW w0 )       -- rank move, no lateral change

-- (C) the two-axes fork: DISTINCT on W and REDUCED reachable on T, both zones real (no fiat, no costume)
theorem ws4_two_axes (hinf : ℵ₀ ≤ κ) :
    -- DISTINCT zone: neither grading a function of the other, on W
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
      ∧ (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )
    -- REDUCED zone: the axes coincide, on T (genuinely reachable, not excluded by construction)
  ∧ ( latT = rankT )
```

## 4. Why REDUCED is genuinely reachable (not a flag flip)

`T` is a real carrier on which `latT = rankT` holds by `rfl`/`funext`: every attention step increments rank, so
breadth accumulates depth and the two gradings are the same function. That is the REDUCED world — "space is time
seen sideways" — built, not stipulated. The fork's two zones are thus both realized: had `W` collapsed to a
tower, it would look like `T`; that it does not (WS2) is the DISTINCT finding, and it is a finding precisely
because `T` shows the collapse is a real alternative.

## 5. Outcome classes

- **DISTINCT (expected):** `ws4_two_axes` holds — `W` independent, `T` the reachable REDUCED zone, verdict
  discriminates → the computed verdict is DISTINCT (WS5).
- **REDUCED (pre-registered, honest):** if `W` itself collapsed (WS2 unwitnessable), the verdict would be
  REDUCED, reported in its direction (space and time one axis), never relabeled.
- **SHAPE-DRAWN:** if the fork were drawn but neither zone forced on the witness.

## 6. Strip annotation

- `ws4_reduced_reachable` → "two gradings that coincide as functions." A bare equality-of-gradings fact.
- `ws4_distinct_witnessed` → "two pairs, each separated by one grading and identified by the other." Independence.
- `ws4_two_axes` → "a discriminating predicate over axis-independence, reaching both values on built structures."
