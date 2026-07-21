# Blind seed — Phase F (code review)

You are reviewing BUILT Lean CODE. You may read:
- This file (`spec/blind-seed-F.md`), and
- The Lean sources under `program-2/series-4/formal/P2S4/` (`ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`,
  `ws5.lean`, `AxiomCheck.lean`) and `program-2/series-4/formal/P2S4.lean`.

STRICT BLINDNESS: Do NOT read `charter.md`, `charter-status.md`, `charter-extension.md`, `protocol.md`,
`spec/README.md`, any `spec/ws*-design.md`, any `summary*.md`, or `spec/blind-seed-C.md`. Judge the code ONLY
against the contracts in this seed. The code's own docstrings may use interpretive words; treat them as
non-authoritative commentary — judge the THEOREM STATEMENTS and their PROOFS, not the prose.

## 0. THIS PASS: the EXT-A1 re-review (load-bearing self-relativity)

The prior review of this build returned zero SERIOUS. Since then ONE payoff was ADDED to `ws3.lean` and audit
clause (a) in `ws5.lean` was STRENGTHENED (a bar-raise; nothing else changed — the verdict, the flags, the
cross-pattern, the fork, the world, the import are byte-for-byte the same). Focus your effort on the addition,
but still confirm the whole build is sorry-free and the names/strip checks still pass.

The addition (in `ws3.lean`):
- `stepsFrom (x y : W) : ℕ := sInf {n | reachIn attendsW n x y}` — the shortest directed attention-path length
  FROM the self `x` TO `y`.
- `stepsFrom_eq` — `stepsFrom x y = k` given a path of length `k` and none shorter.
- `ws3_metric_source_relative` — a 4-part conjunction: (1) `stepsFrom w0 w2 = 2 ∧ stepsFrom w1 w2 = 1 ∧
  stepsFrom w0 ≠ stepsFrom w1` (the metric VARIES by self); (2) `stepsFrom w0 w1 = 1 ∧ stepsFrom w1 w0 = 2 ∧
  stepsFrom w0 w1 ≠ stepsFrom w1 w0` (directed, no symmetric absolute metric); (3) `¬ ∃ g : W → ℕ, ∀ x,
  stepsFrom x = g` (no observer-independent metric); (4) `∀ x ∈ {w0,w1,w2}, stepsFrom w0 x = latW x` (grounds
  `latW`, so the old `ws3_metric_grounded` and the DISTINCT verdict are preserved).

The strengthening (in `ws5.lean`): `ws5_audit_no_absolute_frame` now conjoins the KEPT negation
(`ws3_metric_grounded`) with the ADDED positive (`stepsFrom w0 ≠ stepsFrom w1` and `¬ ∃ g, ∀ x, stepsFrom x = g`).

**Press HARDEST on this question:** is the self-relativity GENUINELY LOAD-BEARING — two distinct selves with
genuinely different distance functions and no reconciling frame — or is it a DRESSED-UP SINGLE BASEPOINT (e.g.
one self re-read, or a trivial/vacuous disagreement, or a `g` that does not exist for a typing reason rather than
a structural one)? Verify the finite facts by hand on the ring: distance from `w0` is `(w0,w1,w2)=(0,1,2)`,
distance from `w1` is `(w1,w2,w0)=(0,1,2)`, so `stepsFrom w0 w2 = 2` but `stepsFrom w1 w2 = 1`. Confirm `stepsFrom
w0 = latW` on the peers so nothing already proved is reopened. Grade SERIOUS if the self-relativity is not
load-bearing, if the verdict changed from DISTINCT, or if anything previously proved was weakened.

## 1. The setting (neutral)

The code builds on an imported, already-verified library. The relevant imported API:

- `outDest hinf att : X → PkObj κ X` — the bare (label-forgetting) successor map on a finite carrier with
  `att : X → Finset X`.
- `SHNE dest x`; `ws1_atomless_bisim dest x y (SHNE x) (SHNE y) : ∃ R, IsBisim dest R ∧ R x y` — any two `SHNE`
  states are plain-bisimilar.
- `rankLift dest (g : X → ℕ) : X → LkObj κ (ULift ℕ) X` — a labelled lift; each edge out of `x` carries `g x`.
  `plainOf (rankLift dest g) = dest`.
- `IsBisimL destL R` — a label-respecting bisimulation.
- `Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R`.
- `AttentionDistinguishes destL x y := (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)`.

The code defines two carriers:

### `W = Fin 4`: `w0=0, w1=1, w2=2, r=3`
- `attendsW`: `w0↦{w1}`, `w1↦{w2}`, `w2↦{w0}`, `r↦{w1}`.
- `rankW`: `w0,w1,w2 ↦ 0`; `r ↦ 1`.   (grading G1, the vertical)
- `latW`: `w0↦0`, `w1↦1`, `w2↦2`, `r↦0`.   (grading G2, the lateral coordinate)
- `rankLiftW hinf := rankLift (outDest hinf attendsW) rankW`; `latLiftW hinf := rankLift (outDest hinf attendsW) latW`.
- `reachIn att`: `reachIn att 0 x y := x = y`; `reachIn att (n+1) x y := ∃ z ∈ att x, reachIn att n z y`.

### `T = Fin 3`: `tw0=0, tw1=1, tw2=2`
- `attendsT`: `tw0↦{tw1}`, `tw1↦{tw2}`, `tw2↦{tw2}`. `rankT`, `latT`: both `tw0↦0, tw1↦1, tw2↦2`.

## 2. The claims the code must prove (verify each is actually discharged, sorry-free)

- `ws1_W_SHNE`, `ws1_lateral_extent`, `ws1_peers_non_recoverable`, `ws1_not_collapsed`.
- `ws2_lateral_step_no_rank`, `ws2_reify_no_lateral`, `ws2_axes_independent`.
- `ws3_lateral_is_import : ¬ Recoverable (latLiftW hinf)`, `ws3_directed`, `ws3_granular`, `ws3_metric_grounded`.
- `ws4_reduced_reachable : latT = rankT ∧ …`, `ws4_distinct_witnessed`, `ws4_two_axes`.
- `verdict : Bool⁴ → Outcome`; `ws5_verdict_eq : verdict true true true true = Outcome.distinct`;
  `ws5_verdict_discriminates` (reaches reduced / shapeDrawn / partial' / partial'); `ws5_flags_justified`;
  `ws5_audit_no_absolute_frame`, `ws5_audit_fork_genuine`, `ws5_audit_knot_is_independence`,
  `ws5_audit_lateral_import`, `ws5_audit_names_not_terms`.

The FULL statements are in the sources. Read them and confirm each PROOF discharges the claimed statement (no
`sorry`, no `admit`, no hidden `axiom`, no assumed-and-returned hypothesis, no vacuous/ill-typed obligation, no
statement weaker than or divergent from what its name claims).

## 3. Success criteria (mechanical)

1. G1 (`rankW`) and G2 (`latW`) separate DIFFERENT pairs under `IsBisimL`: `latLiftW` separates `(w0,w2)` but
   `rankLiftW` does not, AND `rankLiftW` separates `(r,w0)` but `latLiftW` does not. Confirm the four
   sub-claims are each genuinely proved (two negative `¬∃`, two positive `∃`), not stubbed.
2. `reachIn` is genuine length-indexed reachability; `ws1_lateral_extent` shows a pair with `reachIn 2` but not
   `reachIn 1` (real extent), and `ws1_not_collapsed`/`w2 ∉ attendsW w0` shows a non-complete graph.
3. `ws3_lateral_is_import` genuinely proves `¬ Recoverable (latLiftW)` (via `ws1_atomless_bisim` + a label
   separation), not by assuming it.
4. `verdict` is total; `ws5_verdict_eq` computes `distinct`; `ws5_verdict_discriminates` reaches ≥2 outcomes.
5. `latT = rankT` on `T`.

## 4. Audit checks (mechanical, on the code)

- (a) NO ABSOLUTE METRIC: no theorem states a two-argument / symmetric / frame-independent distance number. The
  metric appears only via `reachIn … w0 …` (a fixed basepoint) in `ws3_metric_grounded` /
  `ws5_audit_no_absolute_frame`. Confirm.
- (b) THE FORK NOT BY FIAT: the DISTINCT-side separations (on `W`) AND the coincidence `latT = rankT` (on `T`)
  are BOTH proved. If independence held on every carrier (no `T` coincidence witness), grade SERIOUS.
- (c) THE KNOT IS NOT THE MULTIPLICITY: the DISTINCT verdict must rest on the CROSS-PATTERN (two gradings
  separating DIFFERENT pairs — `ws2_axes_independent` / `ws4_two_axes`), NOT merely on `∃ x y,
  AttentionDistinguishes …` (non-recoverable multiplicity). Check that `ws5_flags_justified`'s `independent`
  conjunct is the cross-pattern, not the bare multiplicity. If the verdict's DISTINCT rests only on "there are
  many non-recoverable peers," grade SERIOUS.
- (d) DISTANCE NOT DISGUISED COUNTING: `reachIn` is path reachability on a NON-COMPLETE graph
  (`w2 ∉ attendsW w0`), and `ws3_metric_grounded` ties `latW` to the SHORTEST `reachIn` length. If the metric
  were raw label-counting / a complete graph, grade SERIOUS.
- (e) NAMES-NOT-TERMS: grep the sources — no proof-term / definition / bound-parameter NAME may embed a
  forbidden content-word (§5). Hits must be docstring/comment PROSE only. Report any code identifier that embeds
  one.

## 5. The strip test and forbidden names

STRIP TEST: for each theorem, delete "space, distance, world, here, there, lateral, breadth" from its NAME and
docstring and confirm the STATEMENT still reads as a bare graph-metric / order-independence / `Recoverable` /
`reachIn` / `verdict` fact. Report any theorem whose proven content depends on the interpretive reading.

FORBIDDEN CONTENT-NAMES (as code identifiers, not docstrings): `space`, `distance`, `world`, `here`, `there`,
`self`, `time`, `god`, `choice`, `subjectivity`. (Note: "lateral" and "breadth" are strip-words, NOT on this
list, so they are acceptable as identifiers.)

## 6. Grading rubric

- SERIOUS: a claim is not actually proved (sorry/admit/axiom/assumed-hypothesis); the verdict rests on
  multiplicity rather than the cross-pattern (audit c); the fork is a fiat — independence true by typing on every
  carrier, or coincidence excluded by construction (audit b); a distance is asserted absolutely (audit a); the
  metric strips to bare label-counting / a complete graph (audit d); a code identifier embeds a forbidden name
  (audit e); a proven statement is materially weaker than or divergent from what its name claims.
- REAL: a genuine gap correctly labelled once fixed (an overclaimed docstring, an over-strong name, a metric
  fact quietly assumed).
- COSMETIC/ACCEPTABLE: a nominal overclaim, a trivial conjunct, a naming nit.

## 7. What to produce

For each claim in §2: does the CODE prove the claimed statement (sorry-free, non-vacuous, matching its name)?
Run the strip test (§5) and the names grep (§5). Confirm audit (a)–(e) (§4), pressing HARDEST on (c) — does the
DISTINCT verdict rest on the axis-independence cross-pattern, or on the multiplicity (the costume)? — and (b) —
is `T` a genuine coincidence witness making the fork real? — and (a) — is no distance asserted absolutely?

Return a structured list of findings with stable IDs `F1-S1`, `F1-S2`, …, each with a grade (SERIOUS / REAL /
COSMETIC), the exact file+theorem, and the defect. If a criterion has no defect, say so explicitly. End with a
one-line count of SERIOUS findings, and CONFIRM which files you read (blindness certification).
