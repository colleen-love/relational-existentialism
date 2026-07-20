# Series 2.2, Design Index (`spec/README.md`)

**The shared carrier, the primitive decision (the other as a second attending locus), the discipline, the
cross-workstream triage, the outcomes, and the names-live-in-prose rule. Read once before the `wsNN-design.md`
docs; they cite this file for every shared object. This index and WS1-WS5 are committed as one batch before any
`formal/` file exists (Phase B gate).**

*Series 2.2 stands on the Series 2.1 ground (`P2S1`), imported. Every carrier piece below is either S1's own
API, an S0 piece reached transitively (`P2S0.*`), or a P1 piece reached transitively (`P1.*`). Nothing new is
added to the substance; the ONE addition (§2) is the OTHER AS A SECOND ATTENDING LOCUS, a construction over the
ground, not a new atom.*

---

## 1. What is imported, and from where

The build imports `P2S1` only (gate `^import (P2S1|P2S2)…`); S0 and the P1 prior art are reached transitively.

| Object | Origin (reached through S1) | Used by |
|---|---|---|
| `attends : X → Finset X`, `knows`, `sym`, `attendedBy`, `outDest`, `pkSingle` | `P2S0.ws1` | all |
| `finsetToPk`, `ws1_bound_is_finite_attention` (finite bound, no cardinal ceiling) | `P2S0.ws1` | WS1 |
| `FinReify`, `ws1_finreify_injective` | `P2S0.ws1` | WS1 |
| `ws1_first_other`, the `Fin 3` witness `attendsU`/`rankU`/`reifyU`, `plainOf_rankLift`, `rankLiftU_val`, `SHNE_U`, `firstOther_label_sep` | `P2S0.ws1` | the SEED pattern lifted to two loci |
| `ws3_direction_not_recoverable`, `ws3_passive_constitution`, `knowLiftD` (the asymmetry of knowing) | `P2S0.ws3` | WS3 (the facing) |
| `impLift`, `ws4_import_quantified` (the exogenous import, quantified) | `P2S0.ws4` | WS2/WS4 (the symmetry-breaker) |
| `PkObj`, `PkMap`, `LkObj`, `SReaches`, `SHNE`, `IsBisim`, `IsBisimL`, `plainOf`, `Recoverable` | `P1.Core` (via S1) | all |
| `ws1_atomless_bisim` (the collapse engine), `ws4_recoverable_not_import` | `P1.Core` (via S1) | WS2, WS4 |
| `Hold`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free` | `P1.Core` (via S1) | WS3, WS4 |
| `rankLift`, `FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `ws2_many_general` | `P1.Reader` (via S1) | WS2, WS4 |

**Deliberately NOT used** (the guardrails): `Many` as a payoff template (PR1-S2 — `RealFor` /
`AttentionDistinguishes` carry every reality/twoness payoff, never `Many`); any convergence/coherence machinery
(`Converges₂` is Series 2.3's, foreclosed here, charter §4.d); a cardinal ceiling or a new atom.

## 2. The primitive: the ONE addition over the ground

Series 2.2 adds exactly ONE thing over the S1 ground, not a new atom: **the OTHER AS A SECOND ATTENDING LOCUS**,
and with it the FOUR READINGS and the MUTUAL-READING structure. S0 reified the self-relation into the first
other (`ws1_first_other`), an attended OBJECT; S2 upgrades that first other into a PERSPECTIVE that reads back —
a second bounded reader (finite `attends`) over one shared field containing the self, the other, and the relata
they attend. The two now face each other in four readings (self of self, self of other, other of self, other of
other), asymmetric because knowing is directed, and partial because no reader totalizes itself (the diagonal).

## 3. The shared witness (`§WITNESS`, fixed here, built in WS1, used by WS2-WS4)

One monomorphic carrier at `Cardinal.{0}` carries every payoff, so WS4's residue and collapse arms and the
reader payoff are exercised on the SAME structure (audit (a), (d)). Carrier `RCar := Fin 5`.

| Node | def | role | `attendsR` | `rankR` |
|---|---|---|---|---|
| `slf` | `0` | the self (base of the constitution tower) | `{slf, oth, p}` | 0 |
| `oth` | `1` | the OTHER: the reified self-relation, upgraded to a locus reading back | `{slf, oth, q}` | 1 |
| `p`   | `2` | a relatum in the SELF's reach only (self reads it, the other does not) | `{p}` | 0 |
| `q`   | `3` | a relatum in the OTHER's reach only (the other reads it, the self does not) | `{q}` | 0 |
| `bnd` | `4` | a higher closure the pair does NOT jointly attend (the residue witness) | `{oth}` | 2 |

- **The other is seeded by reification.** `reifyR : Finset RCar → RCar` is pointwise: `{slf,oth,q} ↦ oth`,
  `{oth} ↦ bnd`, else `slf`. It sections `attendsR` at these patterns: `attendsR (reifyR {slf,oth,q}) =
  {slf,oth,q}` and `attendsR (reifyR {oth}) = {oth}` (the `FinReify` section, pointwise; total `FinReify` is
  unsatisfiable on the finite carrier, as in S0/S1). The other `oth` is the reified reach pattern `{slf,oth,q}`
  (which contains the self-relation `{slf}`), a relatum of the SAME field `RCar`, `rankR oth = 1 > 0 = rankR
  slf`. This GENERALIZES S0's `ws1_first_other` (the self-loop `{slf}` reified into the first other is the base
  case) by giving the reified relatum its OWN attention that reads back into the field.
- **The two reaches are INCOMPARABLE (the C2p2-R1 repair).** `attendsR slf = {slf,oth,p}` and `attendsR oth =
  {slf,oth,q}` with `p ∈ slf∖oth` and `q ∈ oth∖slf`: each perspective reads a relatum the other does not, so
  neither reach contains the other. This makes WS4's joint residue genuinely joint (both non-membership
  conjuncts load-bearing, `p` ruled out only by the self's, `q` only by the other's), not one effective
  membership.
- **The four readings, all four witnessed on the carrier.** self-of-self `slf ∈ attendsR slf`; self-of-other
  `oth ∈ attendsR slf`; other-of-self `slf ∈ attendsR oth`; other-of-other `oth ∈ attendsR oth`. All by `decide`.
- **The direction of the facing (WS3).** The self reads UP the constitution tower (`slf → oth`, `rankR slf = 0 <
  1 = rankR oth`), the other reads DOWN and FLAT (`oth → slf`, `oth → oth`, `oth → q`; no strictly-upward edge
  from `oth`). Knowing is directed: the up/down direction of a reading is non-recoverable from the symmetric
  relating, which forgets it (WS3, `faceLift`).
- **The residue witness (WS4, audit (d) non-vacuity).** `bnd` is plain-bisimilar to the pair (the collapse
  engine, every node `SHNE`) yet JOINTLY UNATTENDED by two INCOMPARABLE reaches: `bnd ∉ attendsR slf =
  {slf,oth,p}` AND `bnd ∉ attendsR oth = {slf,oth,q}`, with `p` ruled out only by the self's conjunct and `q`
  only by the other's. So the mutual reading, combining the self's reach and the other's, genuinely SUBTRACTS
  `bnd` — the joint blind spot the mutuality cannot close, load-bearing on the JOINT attention (the C2p2-R1
  repair: both conjuncts biting, neither implied by the other). The higher reader `bnd` is rank-constrained:
  `∀ x ∈ attendsR bnd, rankR x < rankR bnd` (`decide`), so the reading order is not free/total (PR1-S1
  foreclosed).
- **SHNE.** Every node's `attendsR` is a nonempty finite set, and every reachable node has nonempty `attends`,
  so every node is `SHNE (outDest hinf attendsR)`. Proved `ws1_rcar_SHNE` by reduction to `outDestR_ne_empty`
  (`decide`), so the collapse engine `ws1_atomless_bisim` applies to every pair.

All facts about the witness reduce by the kernel (`Fin 5` has computable `DecidableEq`), so `decide`/`rfl`
discharge the finite obligations, exactly as S0's `attendsU` and S1's `attendsT` witnesses do.

## 4. The discipline (the honesty invariants, applied)

- **The other is a READER, not a label (K1, the central sin, audit (a)).** WS2's `ws2_other_reader_wise` proves
  `RealFor` for a NAMED `def slfReader` (a fixed bounded attention, not an existential over readers — the C1-S1
  repair); the reader's `reads` membership is load-bearing. `Many` is not used, the reader is never quantified
  out. The other's own `attendsR` reads back into the field (all four readings witnessed), so it is a locus,
  never a point-tag.
- **The twoness is non-recoverable (audit (b)).** `ws2_other_non_recoverable` is a proof term: the self/other
  separation is `¬ Recoverable` (an import, Series 07), the collapse never smuggled shut.
- **The facing is asymmetric (audit (c)) and directed.** `ws3_facing_asymmetric` marks the up/down direction of
  the facing structurally (the self reads up, the other has no upward reading) and proves the direction
  `¬ Recoverable` from the symmetric relating — the S0 `ws3_direction_not_recoverable` pattern lifted to the two
  perspectives. Distinct from the twoness: WS2 separates WHICH perspective (source rank), WS3 separates the
  DIRECTION of the reading (source-vs-target rank).
- **The mutual residue is TESTED, not assumed (audit (d)).** WS4's residue is read off the JOINT attention
  subtracting the bisimilar `bnd` (load-bearing on mutuality), witnessed on the pair with all four readings and
  the rank-constrained higher reader; both the collapse arm (`¬ Recoverable` refuted ⇒ ONE) and the residue arm
  are reachable, and the verdict discriminates. The diagonal (`ws1_no_self_total_hold`) is carried as a
  DISCLOSED companion (no perspective totalizes the pair), never as the whole payoff — the mutuality does the
  work, not the global diagonal alone.
- **The coherence is UNTOUCHED (audit (d), charter §4.d).** No theorem, definition, or discharged obligation
  decides whether the two readings cohere (`Converges₂`, Series 2.3's question). No identifier names
  convergence/coherence; the faces are typed and non-evaluated. Verified by the §6 grep (the coherence-open
  check).
- **The import is quantified, no reading evaluated (audit (e)).** The symmetry-breaker is `impLift`, quantified
  over all import value-spaces; no proof term selects or evaluates a particular reading; every theorem is
  quantified over the perspectives' attentions.
- **Names are names.** No proof term, definition, or discharged obligation is named `self`, `other`, `I`, `you`,
  `perspective`, `love`, `loved`, `gaze`, `God`, `choice`, or `subjectivity` as content. The nodes are
  `slf`/`oth`/`bnd` (neutral Lean names for the carrier positions; the interpretive words live in prose only, as
  §6 notes), the lifts `rankLift`/`faceLift`, the reader a `FiniteAttention`. Verified by the §6 grep.

## 5. The two watch-points (protocol §0.8)

- **WS2 — is the other a genuine reader, or a label (K1)?** `ws2_other_reader_wise` is a `RealFor` on a NAMED
  `def slfReader` (a fixed bounded reader, not existential — the C1-S1 repair), the other's `attendsR` reading
  back into the field (all four readings, `decide`). The other is never the reader quantified out; the twoness
  is `¬ Recoverable` (`ws2_other_non_recoverable`), an import.
- **WS4 — is the mutual residue genuine, or the global diagonal in disguise (PR1-S1)?** `ws4_mutual_residue` is
  read off the JOINT attention subtracting the bisimilar `bnd` by two INCOMPARABLE reaches (`bnd ∉ attendsR slf =
  {slf,oth,p}` AND `bnd ∉ attendsR oth = {slf,oth,q}`, both by `decide`, `p ∈ slf∖oth`, `q ∈ oth∖slf` — the
  C2p2-R1 repair), on the witnessed pair with all four readings and the rank-constrained higher reader; the
  diagonal is a disclosed companion. Both arms reachable, the concurrency of the collapse arm exhibited by the
  verdict discriminating.

## 6. The mechanical checks (Phase E)

```
cd lake && lake build P2S2 P2S2.AxiomCheck
grep -rn "sorry" ../program-2/series-2/formal
lake build P2S2.AxiomCheck                       # standard three only
../scripts/gate.sh                               # P2S2 imports P2S1 + self + Mathlib only
grep -rniE "\b(self|other|perspective|love|loved|gaze|god|choice|subjectivity)\b" \
  ../program-2/series-2/formal                   # hits must be docstring prose only
grep -rniE "\b(converg|cohere|coheren)\w*" ../program-2/series-2/formal   # coherence-open: no hit as a term
```
Note: `self`/`other` appear in the SERIES' concept, so the carrier positions use neutral Lean names
(`slf`/`oth`/`bnd`); the grep guards that no proof term or headline is named for the interpretive content.
Docstring prose may use the words freely.

## 7. The outcomes (WS5, per charter §5)

`Outcome := twoFacing | one | totalized | partial' | disconnected`. The verdict is COMPUTED from the WS1-WS4
flags by `verdict` (WS5), never hand-set:

- **twoFacing** (expected): WS1 well-formed (the other a genuine second locus), WS2 the reader load-bearing and
  the twoness non-recoverable, WS3 the facing asymmetric and partial, WS4 the mutual residue survives.
- **one**: WS4 collapses — the other recoverable from the self (`¬ Recoverable` refuted), reported in its
  direction.
- **totalized**: WS4 a perspective (or a composite) totalizes the pair (the diagonal refuted, a self-total hold
  exists), reported in its direction.
- **partial'**: an obligation lands only per-instance / degenerate.
- **disconnected**: WS1's construction imports structure beyond the symmetry-breaker (`wf = false`).

The coherence of the two readings is LEFT OPEN for Series 2.3; no outcome decides it.

## 8. Names live in prose

Every headline mentions only the two loci `slf`/`oth`, the higher reader `bnd`, their `attendsR`, the readings,
`RealFor` / `AttentionDistinguishes`, `Recoverable`, `rankLift` / `faceLift`, the diagonal, the transcribed
machinery, and standard Lean/Mathlib. The motivating reading (the face, the gaze, "you are loved") lives here
and in `charter.md`, never in a proof term. The coherence (Series 2.3) is never named.
