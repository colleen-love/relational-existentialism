# WS4, Mutual reading without collapse (the genuinely-uncertain obligation, the knot)

**Design doc. Series 2.2, the knot. Owns: the genuinely open question — when two perspectives each read the
other AND themselves, does the recursive mutual reading COLLAPSE them (recover one from the other, back to the
One), let one TOTALIZE the pair, or leave a RESIDUE the diagonal forbids either to close. The conjecture is
RESIDUE; ONE and TOTALIZED are pre-registered and reported in full. The sin (charter §4.c, PR1-S1, SERIOUS): the
fork decided by fiat — an unconstrained reading that decides it on every structure, or the diagonal assumed to
survive mutuality rather than tested on a witnessed mutual pair with a load-bearing structure.**

*Imports `P2S1`; the mutual reading is the JOINT attention of the two loci over the shared field; the residue is
that joint attention subtracting a bisimilar relatum `bnd` it does NOT jointly attend (the `ws2_composite_residue`
move lifted from one reader to the pair); the collapse arm is `ws2_other_non_recoverable`'s negation (foreclosed);
the totalize arm is the diagonal's negation (foreclosed). Both arms pre-registered, the verdict discriminating.*

## The object at stake

The charter's WS4 (§2): ask the genuinely open question. When two perspectives each read the other AND
themselves, does the recursive mutual reading (a) COLLAPSE — some reading recovers one perspective from the
other, the twoness recoverable, the world the One (Series 07); (b) TOTALIZE — some perspective or a composite is
a total reader of the pair, closing the opening; or (c) leave a RESIDUE — the diagonal, now under MUTUAL rather
than self-inspection, still forbids any total reading of the pair, so the two stay two and the otherness stays
non-recoverable. The conjecture is (c). But (a) and (b) are genuine, pre-registered, reported in full: it is NOT
assumed that mutual reading behaves like self-reading. The order on readings must carry a structural constraint,
and both arms must be tested on a witnessed pair with a real mutual-reading structure. The strip test applies.

## The mutual-reading structure (README §3, audit (d) non-vacuity, fixed first)

On `RCar`: the two loci `slf`, `oth` read the shared field `{slf, oth}` BETWEEN them — all four readings
witnessed (`ws3_four_readings`): `slf` reads `slf` and `oth`, `oth` reads `slf` and `oth` (`decide`). The
recursion is genuine: `oth` reads `slf`, which reads `oth`, which reads `slf`. The residue witness is `bnd`:
- **The residue (non-empty, load-bearing on MUTUALITY, the C3-S1 repair):** `bnd` is plain-bisimilar to the pair
  (the collapse engine, every node `SHNE`) yet JOINTLY UNATTENDED by two DISTINCT reaches — `bnd ∉ attendsR slf =
  {slf,oth}` AND `bnd ∉ attendsR oth = {slf,oth,sh}` (both `decide`), where the other's reach STRICTLY EXTENDS
  the self's. So the mutual reading, combining the self's reach and the other's WIDER reach, genuinely SUBTRACTS
  `bnd`: it is bisimilar to what they are yet in NEITHER's (different) attention, the joint blind spot the
  mutuality cannot close. This is the `ws2_composite_residue` move (bisimilar yet unattended = the finite
  attention subtracts) lifted from ONE reader to the JOINT attention of the pair — the mutuality is load-bearing
  because the two reaches DIFFER (Phase C flagged that coinciding reaches made "jointly" a single membership).
- **The reading order structurally constrained:** `∀ z ∈ attendsR bnd, rankR z < rankR bnd` (`bnd` reads only
  `oth`, `rankR oth = 1 < 2`, `decide`). The higher reader strictly outranks what it reads: the reading order is
  rank-constrained (a DAG on the constitution tower), NOT free or total by construction (PR1-S1 foreclosed).

Both on `RCar`, all four readings witnessed, the residue non-empty, the order constrained.

## Candidates

### C1, the mutual residue bundle (the lead, the honest fork)

```lean
theorem ws4_mutual_residue (hinf : ℵ₀ ≤ κ) :
    -- (0) the mutual-reading structure is witnessed (all four readings): non-vacuity, the recursion genuine
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))
    -- (1) RESIDUE (load-bearing on MUTUALITY): bnd is bisimilar to the pair yet JOINTLY unattended —
    --     the mutual reading between the pair subtracts it (neither perspective attends it)
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y)
        ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
    -- (2) the reading order is rank-constrained: not free/total (PR1-S1 foreclosed)
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd)
    -- (3) NOT COLLAPSE: the twoness stays non-recoverable under the mutual reading (not ONE)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
    -- (4) NOT TOTALIZED (disclosed companion): the diagonal survives mutual inspection —
    --     no inspection (no perspective, no composite of the two) totalizes the pair
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
```
- **Ambient:** `attendsR`, `rankR`, `outDest`, `ws1_atomless_bisim`, `ws1_rcar_SHNE`, `ws2_other_non_recoverable`
  (WS2, the same `rankLift` non-recoverability), `ws1_no_self_total_hold`.
- **Success condition:** (0) `decide`; (1) `⟨bnd, ws1_atomless_bisim … oth bnd, by decide, by decide⟩`; (2)
  `decide`; (3) `ws2_other_non_recoverable hinf`; (4) `fun insp => ws1_no_self_total_hold _ insp`.
- **Failure mode:** *the residue decided by fiat / the mutuality decorative (PR1-S1, SERIOUS).* Foreclosed: the
  residue (1) is read off the SPECIFIC witnessed structure — `bnd` bisimilar yet in NEITHER perspective's
  attention (`decide`, both conjuncts) — the JOINT attention subtracting, not the global diagonal. The diagonal
  (4) is DISCLOSED as a companion (labelled "not totalized"), never the whole payoff. Both arms pre-registered:
  (3) forecloses COLLAPSE, (4) forecloses TOTALIZED, on this witness. **Winner.**

**Why the mutuality is load-bearing (audit (d)).** The concern is that `ws1_no_self_total_hold` (4) holds on
EVERY structure regardless of mutuality — the PR1-S1 tautology. The load-bearing content is (1): `bnd` is
subtracted by the JOINT attention (`bnd ∉ attendsR slf ∧ bnd ∉ attendsR oth`, and since `attendsR slf ⊊ attendsR
oth` these are two DISTINCT reaches — the C3-S1 repair), a fact about the ACTUAL mutual structure on the witness,
not a global diagonal. (1) is what tests whether mutual reading leaves a residue; (4) is a disclosed companion
certifying no composite totalizes. Strip (1): *"there is a relatum bisimilar to `oth` yet in neither the self's
reach nor the other's wider reach"* — a bare bisim/membership fact, mutuality genuine (the DISCLOSED point: the
bisim `oth ~ bnd` is the collapse engine, Series 07, the honest import structure the residue rests on).

### C2, the residue as the bare global diagonal (the PR1-S1 tautology to avoid)

```lean
theorem ws4_residue_bad (hinf) :   -- the diagonal alone, mutuality decorative
    ∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t
```
- **Failure mode:** *this holds on EVERY coalgebra with NO mutual structure load-bearing — the diagonal assumed
  to survive mutuality rather than tested (PR1-S1, SERIOUS).* **Reject as the payoff.** Retained only as the
  DISCLOSED companion conjunct (4) of C1, explicitly labelled, with (1) carrying the mutual content.

### C3, deciding the coherence (Series 2.3's question, the charter §4.d sin to avoid)

```lean
theorem ws4_coherence_bad : Converges₂ slf oth ∨ ¬ Converges₂ slf oth   -- deciding whether the two readings cohere
```
- **Failure mode:** *any theorem or definition that decides the COHERENCE of the two readings does Series 2.3's
  work and forecloses its fork (SERIOUS).* **Reject.** No signature in WS4 (or anywhere in S2) references
  convergence/coherence; the faces are typed and non-evaluated, the coherence left open (README §4 grep, §6).

## Paper-decidable triage

| Cand | Claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | mutual residue: witnessed pair, joint-unattended residue, order constrained, ¬collapse, ¬totalize | engine, WS2, diagonal | yes | **win** |
| C2 | bare global diagonal | `ws1_no_self_total_hold` | trivially true, tautology | reject (SERIOUS as payoff) |
| C3 | decide coherence | `Converges₂` | Series 2.3's | reject (SERIOUS) |

## Winning candidate: C1

**Proof architecture.** C1 bundles: the witnessed mutual structure (all four readings, `decide`); the residue as
the JOINT attention subtracting the bisimilar `bnd` (`ws1_atomless_bisim` + `decide` on both non-membership
conjuncts) — the load-bearing mutual content; the rank-constrained reading order (`decide`); NOT COLLAPSE
(`ws2_other_non_recoverable`); and the DISCLOSED diagonal companion (NOT TOTALIZED, `ws1_no_self_total_hold`).
Lands `residue = true` for WS5. **Dependencies:** the carrier and `ws1_rcar_SHNE` (WS1); `ws2_other_non_recoverable`
(WS2); `ws1_atomless_bisim`, `ws1_no_self_total_hold` (imported).

## The fork is genuine (audit (d), both arms reachable)

The three arms are pre-registered outcomes the WS5 verdict computes, and BOTH the collapse and residue arms are
reachable inputs to the verdict (which discriminates, `ws5_verdict_discriminates`):
- **RESIDUE (c), witnessed here:** (3) `¬ Recoverable` (not collapse) and (4) no self-total hold (not totalized),
  on the genuine mutual structure with the joint-unattended residue (1). → `residue = true` → **twoFacing**.
- **COLLAPSE (a), reachable:** were the twoness `Recoverable` (some reading recovering one perspective from the
  other), (3) fails, `residue = false`, and the verdict computes **one** — the pre-registered ONE, reported in
  its direction. Foreclosed on this witness by (3), but a genuine verdict input.
- **TOTALIZE (b), reachable:** were some inspection self-total (a perspective or composite totalizing the pair),
  (4) fails, and the verdict computes **totalized** — reported in its direction. Foreclosed by (4), but genuine.

The reading order is rank-constrained (2), not total by construction, so the fork is not decided by fiat: the
concurrency of the arms is genuine, the PR1-S1 tautology foreclosed.

## Outcome classes (per charter §5)

- **residue = true (the expected WS4 payoff, twoFacing):** the mutual residue survives — the diagonal under
  mutual reading still forbids totalization, the twoness non-recoverable, on a witnessed pair with the
  joint-unattended residue and both arms reachable.
- **ONE (pre-registered, first-class):** if the mutual reading COLLAPSES them (`¬ Recoverable` refuted), reported
  ONE in its direction — the other recoverable from the self.
- **TOTALIZED (pre-registered, first-class):** if a perspective or composite TOTALIZES the pair (a self-total
  hold exists), reported TOTALIZED in its direction.
- **The deepest honest risk (charter §5):** that mutual reading does NOT behave like self-inspection — that the
  two perspectives reading each other recover or totalize what one reading itself cannot. Here the joint
  attention (1) genuinely leaves `bnd` a residue and no composite totalizes (4), so RESIDUE stands; but ONE and
  TOTALIZED are pre-registered and would be reported rather than defended.

## Strip test (charter §0.3)

`ws4_mutual_residue` strips (delete "mutual," "reading," "self," "other," "residue," "collapse," "totalize") to
*"all four `attendsR`-memberships hold; there is a relatum bisimilar to `oth` yet in neither `attendsR slf` nor
`attendsR oth`; `attendsR bnd` strictly lowers `rankR`; the `rankLift` over `outDest attendsR` is `¬ Recoverable`;
and no inspection has a self-total hold"* — a bare bisim / membership / rank / import / diagonal fact, exactly
the charter §0.3 SHOULD ("under the mutual-reading inspection, no self-total hold, by the diagonal"). It survives
the strip: no name is a term.

## Deliverable

`formal/P2S2/ws4.lean`: `ws4_mutual_residue`. The mutual structure witnessed (all four readings); the residue the
JOINT attention subtracting the bisimilar `bnd` (load-bearing on mutuality, not the bare diagonal); the reading
order rank-constrained (not PR1-S1); NOT COLLAPSE and NOT TOTALIZED discharged; the coherence NEVER decided
(charter §4.d). Axiom check reduces through the engine, the diagonal, and `decide` to the standard three.
