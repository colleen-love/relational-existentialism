# Program 2 Series 4 (2.4), Charter Extension 1

**This extension only RAISES the bar (protocol §0.1; honest under §0.2a). It strengthens audit clause (a) — the self-relative discipline — from SINGLE-BASEPOINT to LOAD-BEARING, and adds one WS3 payoff to carry it. Nothing already proved is weakened or reopened: the DISTINCT verdict, the axis-independence knot (WS2/WS4), the import grounding (WS3), and the world (WS1) all stand exactly as built. The series re-enters at Phase E (a small addition to WS3 and a restatement of audit (a)), then F and G. Findings from the re-run are tracked in `charter-status.md` with `EXT-` IDs alongside the original C/F findings.**

*Written by the persistent design conversation (Tier 1) after the independent landing review of the DISTINCT build. The build met the original charter cleanly (Phase F: zero SERIOUS, zero REAL). This is not a finding against the build; it is the charter's audit-(a) bar found too low on review, and raised — the same instrument as the Series 2.0 and 2.1 extensions.*

---

## 1. What the review caught

The landed audit (a) (`ws5_audit_no_absolute_frame` = `ws3_metric_grounded`) proves that `latW` is the shortest attention-path length FROM the fixed self `w0`, with no shorter path, and that no two-argument absolute metric `d(x,y)` is asserted. That is met, and it discharges the NEGATIVE content of the self-relative discipline: no view from nowhere.

But it is SINGLE-BASEPOINT. It never exhibits the POSITIVE content — that the metric genuinely VARIES by self, that a different self measures genuinely different distances, with no absolute frame reconciling them. And self-relativity is the DEFINING THESIS of Phase 2 (`charter-extension.md` §2): every physical quantity is a quantity for a self, no absolute frame. The first Phase-2 series should make that thesis a THEOREM, not an interpretation of a fixed grading read as "from `w0`." The bar was set at "no absolute distance" (a negation) without "the distance genuinely differs between selves" (the load-bearing positive). This is the exact shape of the Series 2.0 (inert reification) and Series 2.1 (non-directional arrow) catches: a payoff nominally present but not doing the work the thesis needs.

The world already built carries the strengthening for free. The ring is DIRECTED, so:

- distance from `w0`: `w0 = 0`, `w1 = 1`, `w2 = 2`
- distance from `w1`: `w1 = 0`, `w2 = 1`, `w0 = 2`

These are genuinely different functions — `w2` is FAR from `w0` (distance 2) but NEAR `w1` (distance 1) — and because the ring is one-way there is no symmetric `d(x,y)` both selves agree with. The observer-dependence of distance is a fact about the carrier already in the build, waiting to be stated.

## 2. The raise (EXT-A1)

Strengthen audit (a), and add one WS3 payoff to carry it, to LOAD-BEARING self-relativity.

**New WS3 target (provisional name `ws3_metric_self_relative`).** Define the self-relative distance `distFrom : W → W → ℕ` — the shortest directed attention-path length FROM the first argument (the self) TO the second — grounding `latW` as `distFrom w0` and reusing the `reachIn` path structure. Prove:

1. **The metric varies by self.** `distFrom w0 ≠ distFrom w1` as functions — exhibit a peer on which they disagree (`w2`: `distFrom w0 w2 = 2` while `distFrom w1 w2 = 1`, and/or `w0`: `distFrom w0 w0 = 0` while `distFrom w1 w0 = 2`). Two selves, genuinely different distance-orderings.
2. **No absolute frame reconciles them (load-bearing).** No single `g : W → ℕ` is the distance for every self — the family `distFrom x` indexed by the self `x` is non-constant in `x` — so there is no observer-independent metric. (The directedness makes this sharp: `distFrom` is not symmetric, so no undirected absolute `d(x,y)` exists either; `ws3_directed` already witnesses the asymmetry, now folded into the self-relative payoff.)

**Strengthened audit (a).** `ws5_audit_no_absolute_frame` is restated to include the two-self disagreement and the non-existence of an observer-independent metric, resting on `ws3_metric_self_relative` in addition to `ws3_metric_grounded`. The negation (no absolute `d(x,y)`) stays; the positive (varies by self) is added. The audit now certifies self-relativity as a proof term, not an interpretation.

Everything else is untouched. The verdict function, the flags, the cross-pattern, the fork, the import grounding, and the world are unchanged. `distFrom w0` must be defeq or proved equal to `latW` on the peers, so `ws3_metric_grounded` and the DISTINCT computation are preserved verbatim.

## 3. The discipline (protocol §0.2a)

EXT-A1 closes in exactly one of two ways, named in `charter-status.md`: **(Fixed)** `ws3_metric_self_relative` and the strengthened `ws5_audit_no_absolute_frame` are built (name the theorems), the self-relativity now load-bearing; or **(Relabeled)** the self-varying metric cannot be built (an obstruction, e.g. the directed ring turns out to force a reconcilable frame), recorded precisely, and audit (a) demoted to the single-basepoint form with the obstruction disclosed. A weaker adjacent theorem is neither and is prohibited; a target-avoiding closure is re-graded SERIOUS and marked RECURRING. Because the raise adds a payoff and restates one audit clause, the re-run is Phase E (build `ws3_metric_self_relative`, restate the audit, re-run the §6 mechanical checks and recompute the verdict — which must remain DISTINCT, unchanged), then Phase F (blind review of the strengthened audit, pressing on whether the self-relativity is genuinely load-bearing or a dressed-up single basepoint), then Phase G. If Phase B design is touched (the `distFrom` signature), commit the design note first.

## 4. What does NOT change

- The verdict: DISTINCT, computed, unchanged (the extension adds a property of the metric, not a new axis or a new fork).
- The knot: axis-independence (WS2/WS4), the cross-pattern, the W-vs-T fork — untouched.
- The costume gate (audit c): still passing; the self-relativity strengthening is orthogonal to it.
- The import grounding (WS3, audit d), the world (WS1), the names discipline (audit e), the granularity and directedness (WS3): all stand.
- Program 1's permanent opens: still four, still untouched. This extension draws the self-relativity of space sharper; it fills nothing.

---

*This extension raises the audit-(a) bar and nothing else, honest under §0.2a. It makes "space is self-relative" a theorem on the world already built — two selves, genuinely different metrics, no absolute frame — so the Phase-2 thesis is load-bearing from its first series. A forward-note for the population series (2.8): the RICH self-relativity — many selves, the general-relativity-like absence of any global reconciliation across a whole population — belongs there, on the world this series grounds; EXT-A1 establishes the two-self base case that 2.8 will generalize.*
