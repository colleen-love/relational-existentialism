# Series 2.4 — Technical summary

**Verdict: DISTINCT** (computed by `P2S4.ws5_verdict_eq : verdict true true true true = Outcome.distinct`, the
four flags earned by `ws5_flags_justified`, none hand-set). The build is sorry-free, axiom-clean (Mathlib's
standard `propext` / `Classical.choice` / `Quot.sound`; the verdict computations depend on no axioms), and
gate-green (`P2S4` imports `P2S3` only, reaching the chain transitively). Namespace `P2S4`, built on the
attention carrier reached through `P2S3`.

## The construction

Two monomorphic carriers at `Cardinal.{0}`.

**The world `W = Fin 4`** (`ws1.lean`): a directed 3-ring of same-rank peers `w0 → w1 → w2 → w0` plus a reified
peer `r`.
- `attendsW`: `w0↦{w1}`, `w1↦{w2}`, `w2↦{w0}`, `r↦{w1}` (LOCAL: `w0` does not attend `w2`).
- `rankW` (the vertical grading): `w0,w1,w2 ↦ 0`; `r ↦ 1`.
- `latW` (the lateral coordinate): `w0↦0`, `w1↦1`, `w2↦2`, `r↦0`.
- `rankLiftW := rankLift (outDest hinf attendsW) rankW`, `latLiftW := rankLift (outDest hinf attendsW) latW` —
  the SAME imported labelling machine with the two gradings.
- `reachIn` — a length-indexed directed reach on `attendsW`, with a structural `Decidable` instance, so all
  metric facts fall to `decide`. The breadth metric is genuinely path-based, not a label count.
- Every node is `SHNE`, so `ws1_atomless_bisim` makes any two nodes plain-bisimilar: the plain relating is
  blind, and all content lives in the two labels.

**The tower `T = Fin 3`** (`ws4.lean`): a reification line `tw0 → tw1 → tw2` (`tw2` self-loops), with
`rankT = latT` — the REDUCED zone where breadth is accumulated depth.

## The payoffs

**WS1 — the world (`ws1.lean`).**
- `ws1_lateral_extent` — `rankW w0 = rankW w2`, `w0 ≠ w2`, `reachIn attendsW 2 w0 w2` and `¬ reachIn attendsW 1 /
  0 w0 w2`: two same-rank peers at path-distance exactly 2 (> 1), real extent.
- `ws1_peers_non_recoverable` — `AttentionDistinguishes (latLiftW hinf) w0 w2`: plain-bisimilar (collapse engine)
  yet not lat-bisimilar (the lateral separation is an import).
- `ws1_not_collapsed` — `w2 ∉ attendsW w0 ∧ reachIn attendsW 2 w0 w2` (non-complete graph) with same-rank
  multiplicity and finite out-neighborhoods (`ws1_bound_is_finite_attention`, no cardinal ceiling).

**WS2 — the axes come apart (`ws2.lean`).** The cross-pattern, via explicit bisimulations:
- `ws2_lateral_step_no_rank` — `latLiftW` separates `(w0,w2)` (`lat_sep_w0_w2`), `rankLiftW` does NOT
  (`rank_bisim_w0_w2`, the "both rank 0" relation is an `IsBisimL`), and `rankW w0 = rankW w2`.
- `ws2_reify_no_lateral` — `rankLiftW` separates `(r,w0)` (`rank_sep_r_w0`), `latLiftW` does NOT
  (`lat_bisim_r_w0`, the relation `id ∪ {(r,w0),(w0,r)}` is an `IsBisimL`), and `latW r = latW w0`.
- `ws2_axes_independent` — the two together: neither grading is a function of the other. THE FINDING.

**WS3 — space real-as-import; directed, granular, self-relative (`ws3.lean`).**
- `ws3_lateral_is_import` — `¬ Recoverable (latLiftW hinf)`, from `ws1_peers_non_recoverable` + the definition of
  `Recoverable` (Series 07's collapse engine).
- `ws3_directed` — `reachIn attendsW 1 w0 w1 ∧ ¬ reachIn attendsW 1 w1 w0 ∧ reachIn attendsW 2 w1 w0`: the path
  metric is asymmetric (the spatial face of the 2.0 knowing-asymmetry).
- `ws3_granular` — length-0 reach is identity, and a smallest positive step (length 1, distinct states) exists.
- `ws3_metric_grounded` — for each peer, `latW` equals the shortest `reachIn` length FROM `w0` (a path of that
  length exists, none shorter): self-relative, path-grounded, no absolute metric.

**WS4 — the two-axes fork (`ws4.lean`).**
- `ws4_reduced_reachable` — `latT = rankT` on `T`, so the two gradings identify the same pairs: REDUCED realized.
- `ws4_distinct_witnessed` — the lateral move keeps rank, the reification keeps `lat`, both on `W`.
- `ws4_two_axes` — DISTINCT on `W` (the cross-pattern) AND `latT = rankT` on `T`: both zones built, so the fork
  is genuine (no fiat) and rests on axis-independence (no costume).

**WS5 — the verdict and the audit (`ws5.lean`).**
- `verdict : Bool⁴ → Outcome` (`Outcome := distinct | reduced | shapeDrawn | partial'`).
- `ws5_verdict_eq : verdict true true true true = Outcome.distinct` (by `rfl`, no axioms).
- `ws5_verdict_discriminates` — reaches `reduced` (independence false, the `T` zone), `shapeDrawn`, and `partial'`
  (twice): non-constant, no axioms.
- `ws5_flags_justified` — the four `true` inputs earned by the WS1 laterality, the WS2/WS4 cross-pattern, the WS3
  import, and the WS4 both-moves-with-`T`-reachable.
- Audit: `ws5_audit_no_absolute_frame` (a, = `ws3_metric_grounded`), `ws5_audit_fork_genuine` (b),
  `ws5_audit_knot_is_independence` (c, = `ws2_axes_independent`), `ws5_audit_lateral_import` (d, =
  `ws3_lateral_is_import`), `ws5_audit_names_not_terms` (e, the grep-certified placeholder).

## Discipline discharged

- **No absolute frame (audit a):** the metric is `latW` = shortest `reachIn` from the fixed self `w0`; no
  two-argument absolute distance.
- **Fork not by fiat (audit b):** DISTINCT on `W`, REDUCED (`latT = rankT`) on `T`; the independence fails on
  `T`, so it is not a typing artifact.
- **Knot not the multiplicity (audit c, the costume gate):** the DISTINCT verdict's `independent` flag is the
  cross-pattern (`ws2_axes_independent`), not `∃ x y, AttentionDistinguishes`; verified across three blind design
  rounds and the blind code review.
- **Distance not disguised counting (audit d):** `reachIn` is path reachability on a non-complete graph;
  `ws3_metric_grounded` ties `latW` to the shortest path length.
- **Names-not-terms (audit e):** the §6 grep is clean (hits are docstring prose only); no proof term, definition,
  or bound parameter is named for the spatial content. (The two design-target renames and the `spaceImport →
  latImport` parameter rename are recorded in `charter-status.md`.)

## Provenance

Built on `P2S3` (reaching `P2S2` / `P2S1` / `P2S0` / `P1` transitively). The world and both gradings are built
FRESH on the imported attention carrier (`outDest`, `rankLift`, `Recoverable`, `AttentionDistinguishes`,
`ws1_atomless_bisim`, `ws1_bound_is_finite_attention`). Nothing below `P2S3` is imported directly; the closure
gate enforces `^import (P2S3|P2S4)…`. Program 1's permanent opens are carried untouched.
