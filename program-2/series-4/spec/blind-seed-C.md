# Blind seed — Phase C (design review)

This is the ONLY file you may read. It is self-contained. Judge the DESIGN below (the signatures and the
construction) against the mechanical criteria in §3–§6. Do not seek any other file; do not consult motivating
prose. You are reviewing whether the proposed Lean signatures are coherent, non-vacuous, and satisfy the checks.

## 1. The setting (neutral)

All objects are built on an imported, already-verified library over a finite carrier `X : Type` with an
attention map `att : X → Finset X` (finite out-neighborhoods). The imported API (assume correct):

- `outDest hinf att : X → PkObj κ X` — the bare relating (label-forgetting successor map).
- `SHNE dest x` — every state reachable from `x` has a nonempty successor set.
- `ws1_atomless_bisim dest x y (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y` —
  ANY two `SHNE` states are plain-bisimilar (the plain relating is blind).
- `rankLift dest (g : X → ℕ) : X → LkObj κ (ULift ℕ) X` — a labelled lift: each edge out of `x` carries the
  integer label `g x`. `plainOf (rankLift dest g) = dest`.
- `IsBisimL destL R` — a label-respecting bisimulation.
- `Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R` — every plain bisimulation is
  already label-respecting.
- `AttentionDistinguishes destL x y := (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)`.

Two carriers are defined by the design:

### Carrier `W = Fin 4`: `w0=0, w1=1, w2=2, r=3`
- `attendsW`: `w0↦{w1}`, `w1↦{w2}`, `w2↦{w0}`, `r↦{w1}`.
- `rankW`: `w0,w1,w2 ↦ 0`; `r ↦ 1`.   (grading G1)
- `latW`: `w0↦0`, `w1↦1`, `w2↦2`, `r↦0`.   (grading G2)
- `rankLiftW hinf := rankLift (outDest hinf attendsW) rankW`;  `latLiftW hinf := rankLift (outDest hinf attendsW) latW`.
- `reachIn att : ℕ → W → W → Prop`: `reachIn att 0 x y := x = y`; `reachIn att (n+1) x y := ∃ z ∈ att x, reachIn att n z y`.

### Carrier `T = Fin 3`: `tw0=0, tw1=1, tw2=2`
- `attendsT`: `tw0↦{tw1}`, `tw1↦{tw2}`, `tw2↦{tw2}`.
- `rankT`: `tw0↦0, tw1↦1, tw2↦2`.   `latT`: `tw0↦0, tw1↦1, tw2↦2`.

## 2. The theorem signatures under review

```
-- WS1
lemma ws1_W_SHNE (hinf) (x : W) : SHNE (outDest hinf attendsW) x
theorem ws1_lateral_extent :
    rankW w0 = rankW w2 ∧ w0 ≠ w2
  ∧ reachIn attendsW 2 w0 w2 ∧ ¬ reachIn attendsW 1 w0 w2 ∧ ¬ reachIn attendsW 0 w0 w2
theorem ws1_peers_non_recoverable (hinf) : AttentionDistinguishes (latLiftW hinf) w0 w2
theorem ws1_not_collapsed (hinf) :
    (w2 ∉ attendsW w0 ∧ reachIn attendsW 2 w0 w2)
  ∧ (rankW w0 = rankW w2 ∧ w0 ≠ w2)
  ∧ (∀ x : W, Cardinal.mk (↥((outDest hinf attendsW x).1)) < Cardinal.aleph0)

-- WS2
theorem ws2_lateral_step_no_rank (hinf) :
    (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2)
  ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
  ∧ rankW w0 = rankW w2
theorem ws2_reify_no_lateral (hinf) :
    (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0)
  ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0)
  ∧ latW r = latW w0
theorem ws2_axes_independent (hinf) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2) )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )

-- WS3
theorem ws3_lateral_is_import (hinf) : ¬ Recoverable (latLiftW hinf)
theorem ws3_directed :
    reachIn attendsW 1 w0 w1 ∧ ¬ reachIn attendsW 1 w1 w0 ∧ reachIn attendsW 2 w1 w0
theorem ws3_granular :
    (∀ x y : W, reachIn attendsW 0 x y ↔ x = y) ∧ (∃ x y : W, reachIn attendsW 1 x y ∧ x ≠ y)
theorem ws3_metric_grounded :
    ∀ x : W, x ∈ ({w0,w1,w2} : Finset W) →
      reachIn attendsW (latW x) w0 x ∧ ∀ m, m < latW x → ¬ reachIn attendsW m w0 x

-- WS4
theorem ws4_reduced_reachable :
    latT = rankT ∧ ∀ x y : T, (latT x = latT y ↔ rankT x = rankT y)
theorem ws4_distinct_witnessed (hinf) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ rankW w0 = rankW w2 )
  ∧ ( (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ latW r = latW w0 )
theorem ws4_two_axes (hinf) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ (∃ R, IsBisimL (rankLiftW hinf) R ∧ R w0 w2)
      ∧ (¬ ∃ R, IsBisimL (rankLiftW hinf) R ∧ R r w0) ∧ (∃ R, IsBisimL (latLiftW hinf) R ∧ R r w0) )
  ∧ ( latT = rankT )

-- WS5
inductive Outcome | distinct | reduced | shapeDrawn | partial'  deriving DecidableEq
def verdict (lateral independent latImport bothMoves : Bool) : Outcome :=
  if !lateral then Outcome.partial'
  else if !latImport then Outcome.partial'
  else if independent && bothMoves then Outcome.distinct
  else if !independent then Outcome.reduced
  else Outcome.shapeDrawn
theorem ws5_verdict_eq : verdict true true true true = Outcome.distinct
theorem ws5_verdict_discriminates :
    verdict true false true true = Outcome.reduced
  ∧ verdict true true true false = Outcome.shapeDrawn
  ∧ verdict false true true true = Outcome.partial'
  ∧ verdict true true false true = Outcome.partial'
theorem ws5_flags_justified (hinf) : <conjunction of the WS1/WS2/WS3/WS4 headline props above>
theorem ws5_audit_no_absolute_frame : <= ws3_metric_grounded>
theorem ws5_audit_fork_genuine (hinf) :
    ( (¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2) ∧ latW r = latW w0 ) ∧ (latT = rankT)
theorem ws5_audit_knot_is_independence (hinf) : <= the cross-pattern of ws2_axes_independent>
theorem ws5_audit_lateral_import (hinf) : ¬ Recoverable (latLiftW hinf)
theorem ws5_audit_names_not_terms : True
```

## 3. Success criteria (restated mechanically)

1. G1 (`rankW`) and G2 (`latW`) are two integer gradings on `W`; there is a pair separated under `IsBisimL` by
   the G2-lift but not the G1-lift, AND a pair separated by the G1-lift but not the G2-lift.
2. `reachIn` is a genuine length-indexed reachability on `attendsW`; some pair has `reachIn 2` but not
   `reachIn 1` (real extent, non-adjacent), and the graph is non-complete.
3. `¬ Recoverable (latLiftW)` is a theorem (the G2-label is a genuine import), via `ws1_atomless_bisim` + a
   label separation.
4. The verdict is a total function of four Booleans, `= distinct` on `(true,true,true,true)`, and reaches at
   least two distinct outcomes on other inputs (non-constant).
5. `latT = rankT` on `T` (the two gradings coincide on the second carrier).

## 4. Audit checks (mechanical)

- (a) NO ABSOLUTE METRIC: no signature states a two-argument distance as a single frame-independent number; the
  grading `latW` used as a distance is tied to `reachIn … w0 …` (a fixed basepoint). Confirm no theorem asserts
  a symmetric/global distance.
- (b) THE FORK NOT BY FIAT: check that the DISTINCT-side separations (on `W`) and the COINCIDENCE `latT = rankT`
  (on `T`) are BOTH present, so the independence is NOT a typing artifact true on every carrier. If independence
  held by construction on all carriers (no `T` witness of coincidence), grade SERIOUS.
- (c) THE KNOT IS NOT THE MULTIPLICITY: check that the DISTINCT verdict rests on the CROSS-PATTERN (G1 separates
  a pair G2 does not, and G2 separates a pair G1 does not), NOT merely on "there exist ≥2 non-recoverable
  states." A payoff whose only content is `∃ x y, AttentionDistinguishes … x y` (non-recoverable multiplicity),
  with no statement that the two gradings separate DIFFERENT pairs, is a costume — grade SERIOUS.
- (d) DISTANCE NOT DISGUISED COUNTING: `reachIn` must be genuine path reachability on a NON-COMPLETE graph
  (`w2 ∉ attendsW w0`), and `ws3_metric_grounded` must tie `latW` to the shortest `reachIn` length. If the
  metric were the raw count of labels / a complete graph where every pair is adjacent, grade SERIOUS.
- (e) NAMES-NOT-TERMS: no proof-term/definition name embeds forbidden content (see §5). Neutral names (`W`,
  `w0`, `latW`, `rankW`, `reachIn`, `latLiftW`, `Outcome`, etc.) are fine. Interpretive words may appear only in
  docstring prose.

## 5. The strip test and the forbidden names

STRIP TEST: for each payoff, delete the words "space, distance, world, here, there, lateral, breadth" and check
the statement still reads as a bare graph-metric / order-independence / `Recoverable` fact. Report any payoff
that does NOT survive (i.e. whose content depends on the interpretive reading).

FORBIDDEN CONTENT-NAMES (as proof terms / defs, not docstrings): `space`, `distance`, `world`, `here`, `there`,
`self`, `time`, `god`, `choice`, `subjectivity`.

## 6. Grading rubric

- SERIOUS: the verdict rests on it; the knot rests on multiplicity rather than the cross-pattern (audit c); the
  fork is a fiat — independence true by typing on every carrier, or coincidence excluded by construction (audit
  b); a distance is asserted absolutely (audit a); the metric strips to bare label-counting / complete graph
  (audit d); a name is a proof term (audit e); an undisclosed narrowing.
- REAL: a genuine gap correctly labelled once fixed (an overclaimed signature, an assumed-and-returned
  hypothesis, an over-strong name, a vacuous/ill-typed obligation).
- COSMETIC/ACCEPTABLE: a nominal overclaim or naming nit.

## 7. What to produce

For each theorem signature: is the design coherent and NON-VACUOUS (would a proof of it be meaningful, not
trivially true or ill-typed)? Run the strip test. Run the names check. Confirm audit (a)–(e), pressing HARDEST
on (c) — does the DISTINCT verdict rest on the cross-pattern of separations (two gradings separating different
pairs), or only on the existence of many non-recoverable states? — and (b) — is `T` a genuine coincidence
witness making the fork real? Return a structured list of findings with stable IDs `C1-S1`, `C1-S2`, …, each
with a grade (SERIOUS / REAL / COSMETIC), the exact signature it concerns, and the defect.
