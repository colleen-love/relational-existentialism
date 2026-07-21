# WS2 design — The axes come apart (independence) (2.4)

**Prove BREADTH and DEPTH are INDEPENDENT on the witnessed world: a lateral step changes `lat` without changing
`rank`, and a reification step changes `rank` without lateral displacement, so neither grading is a function of
the other. This is the DISTINCT side made precise, and the new content on which the verdict rests (audit c).**

## 1. Candidate constructions

Independence must be witnessed on genuine moves, not asserted. Candidates for "the axes come apart":

1. **Numeric non-equality `latW ≠ rankW` as functions.** REJECTED as the whole story: a bare `∃ x, latW x ≠
   rankW x` is too weak — two gradings can differ pointwise yet still be functions of each other (e.g. `lat =
   rank + 1`). Independence needs that neither DETERMINES the other.
2. **Separation cross-pattern via the labelled lifts (CHOSEN).** Independence = `lat` and `rank` separate
   DIFFERENT pairs under `IsBisimL`: `lat` separates `(w0,w2)` where `rank` does not, and `rank` separates
   `(r,w0)` where `lat` does not. A lateral move (`w0 → w1 → w2`, changing `lat`, same `rank`) and a reification
   (`r`, changing `rank`, same `lat`) are the two witnessed moves. This is genuine functional independence read
   through the imported `IsBisimL`, not a numeric artifact. See `spec/README.md` §2.1.

## 2. Triage

- **Non-triviality.** Both separations are witnessed by explicit bisimulations / label-separation proofs, not
  posited. The lateral move and the reification move are genuine edges of the world.
- **Strip test.** Delete "axis," "lateral": the payoff is "the `lat` grading and the `rank` grading are not
  functions of each other — there is a pair separated by `lat` but not `rank`, and a pair separated by `rank`
  but not `lat`." A bare order-independence fact.
- **Costume gate (audit c).** The MULTIPLICITY of peers is NOT the content here; the content is the CROSS-PATTERN
  (each grading separating a pair the other does not). A world with many peers where `lat` and `rank` separated
  the SAME pairs would FAIL WS2 (that is the REDUCED zone, `T`). So WS2 rests on independence, not on "many."
- **Fork not by fiat (audit b).** The independence does NOT hold by typing: on `T` (`spec/README.md` §2.2) `latT
  = rankT`, so the SAME pairs are separated and independence FAILS. WS2's claim is structure-specific to `W`.

## 3. Winning construction — typed signatures

```
-- (A) a lateral step changes lat, keeps rank: w0,w2 are lat-separated but rank-identified (same rank 0)
theorem ws2_lateral_step_no_rank (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2)          -- lat SEPARATES (w0,w2)
  ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)           -- rank does NOT separate (w0,w2)
  ∧ rankW w0 = rankW w2                                     -- the lateral move keeps rank

-- (B) a reification step changes rank, no lateral displacement: r,w0 rank-separated but lat-identified
theorem ws2_reify_no_lateral (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0)           -- rank SEPARATES (r,w0)
  ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0)             -- lat does NOT separate (r,w0)
  ∧ latW r = latW w0                                        -- the reification has no lateral displacement

-- (C) the axes are independent: neither grading is a function of the other (the two moves together)
theorem ws2_axes_independent (hinf : ℵ₀ ≤ κ) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2) )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )
```

## 4. The two witnessing bisimulations (build sketch)

- **`rank` does not separate `(w0,w2)`:** `R_rank := fun x y => rankW x = 0 ∧ rankW y = 0` (all peers rank 0).
  It is an `IsBisimL (rankLiftW)`: every rank-0 node's out-edge is labelled `0` and lands on a rank-0 peer, so
  labels match and successors stay in `R_rank`. Relates `w0,w2`. (`r` is rank 1, excluded — stays closed.)
- **`lat` does not separate `(r,w0)`:** `R_lat := fun x y => x = y ∨ (x = r ∧ y = w0) ∨ (x = w0 ∧ y = r)`. It is
  an `IsBisimL (latLiftW)`: `r` and `w0` both carry `lat`-label `0` and both edge to `w1`, so labels match and
  successors are `R_lat`-related (`w1 = w1`); reflexive pairs are trivial.
- **`lat` separates `(w0,w2)`** and **`rank` separates `(r,w0)`:** the label-separation pattern of
  `P2S0.firstOther_label_sep` — the source labels differ (`lat w0 = 0 ≠ 2 = lat w2`; `rank r = 1 ≠ 0 = rank
  w0`), so no label-bisimulation can relate them.

## 5. Outcome classes

- **Built (expected):** independence witnessed both ways → the DISTINCT side of the fork holds on `W`.
- **REDUCED (pre-registered):** if one of the two separations could not be witnessed — if every `rank`-separated
  pair were `lat`-separated and vice versa — the axes would coincide (the `T` zone), reported as REDUCED, not
  relabeled.

## 6. Strip annotation

- `ws2_lateral_step_no_rank` → "a pair separated by grading L but not grading R." Order-independence, one side.
- `ws2_reify_no_lateral` → "a pair separated by grading R but not grading L." Order-independence, other side.
- `ws2_axes_independent` → "neither of two gradings is a function of the other." The bare independence fact.
