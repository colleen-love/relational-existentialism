> **CORRECTION (finding T1-S1, Tier-1 landing review).** The CONSERVED-RELATIVE design described below was OVERTURNED as a costume: its "in-sight conservation" (`ws2_tick_conserves`) was the collapse engine (a state-bisimilarity holding for any measure), not a `Q`-invariance, and its free-lunch fork was decided by a `Finset.card` counter disconnected from the diagonal. The series was reground to the honest, computed verdict **MONOTONE-ONLY**: the measure `Q := rankM` is non-trivial but RISES under the tick and is not conserved, and conservation-from-within is IMPOSSIBLE (the diagonal is always a source, `ws2_residue_free`). The authoritative record is the built `formal/P2S7/` (verdict `ws5_verdict_eq = monotoneOnly`), `summary.md` / `summary-technical.md`, and `charter-status.md` §4 (T1-S1, T1-A1). The CONSERVED-RELATIVE attempt is on record and checkable in `formal/P2S7/ConservedRelativeAttempt.lean`. This design file is kept as the pre-reground record of the original intent.

---

# Measure de-risking — the paper hunt for `Q` (2.7, before the WS designs)

**Phase B for this series begins here and does NOT proceed to the WS designs until a candidate measure `Q`
survives the tick (conserves in-sight) and the diagonal (the free-lunch test) BY HAND. `Q` must be defined
WITHOUT reference to its conservation or its rise (charter §4.c, the WS1 watch); its conservation and its
free-lunch status are PROVED of the independent `Q`, never built in. If no candidate survives both tests, this
file records the obstruction and the series lands DISCONNECTED (charter §6, protocol §0.9). It does not.**

---

## 0. What a measure must be (the bar, from the charter)

The measure of distinction `Q` is the quantity conjugate to the tick — the cost of creation, energy-and-information
as one (charter §1). To earn the WS designs it must clear, on paper, four gates:

- **(N) Non-trivial.** `Q` is not constant: two configurations with different `Q` (charter §2 WS1, §4.c). And the
  difference must be a genuine measure of DISTINCTION — a `¬ Recoverable` import — not an arbitrary label.
- **(I) Independent / not rigged.** `Q` is defined structurally, with no reference to conservation or rise. A `Q`
  defined as "invariant" (rigged to conserve) or "strictly increasing" (rigged to rise) is disqualified (§4.c).
- **(T) The tick conserves it in-sight.** A reification-tick preserves `Q` within what the self can see (the plain
  relating), and this must be a THEOREM about the independent `Q`, resting on the collapse engine, not a definitional
  triviality (charter §2 WS2).
- **(D) The diagonal test is genuine.** The residue (the P1 diagonal, `ws2_residue_free`) either changes `Q` with no
  import (FREE-LUNCH) or relocates (CONSERVED), and BOTH must be genuinely reachable — the create-or-relocate crux
  rests on the diagonal-as-source, not on the mere import-ness of a distinction (charter §4.b, §4.d, the costume gate).

---

## 1. Candidate measures

### Candidate 1 — the reification rank `Q := rankM` (the accumulated import-content). **LEAD, SURVIVES.**

The measure of a relatum is the height it occupies in the reification tower: a base relatum has `Q = 0`; a relatum
reified from a pattern has `Q` one above its constituents. Read: the number of reification steps of import-content a
relatum carries over its plain-bisimilar base. This is the "latent-and-actual" measure of distinction the charter
names (§2 WS1): a reified relatum of rank `k` is plain-bisimilar to a base (rank 0) — the collapse engine identifies
them in-sight — yet carries `k` imports' worth of label-distinction the plain relating cannot see.

- **(N) Non-trivial — PASSES.** `rankM` is non-constant: a reified relatum `e1 = reifyM {e0}` has `rankM e1 = 1`,
  its base `e0` has `rankM e0 = 0`. And the difference is a GENUINE import: `e1` and `e0` are plain-bisimilar (the
  collapse engine `ws1_atomless_bisim`, both `SHNE`) yet rank-lift-separated (`AttentionDistinguishes`,
  the `ws2_many_general` / `firstOther_label_sep` mechanism, transitively `P1.Reader`). So `Q`'s value-difference IS
  a `¬ Recoverable` distinction, not an arbitrary label. `Q` measures import-content.
- **(I) Independent — PASSES.** `rankM` is defined by the tower position alone (a `MCar → ℕ` function fixed with the
  carrier), with NO reference to conservation or rise. Its conservation (T) and its diagonal status (D) are proved of
  this independent `rankM`, never built into it.
- **(T) The tick conserves it in-sight — PASSES, and genuinely.** THE KEY SUBTLETY, and the general-relativity shape.
  The tick reifies `{e0}` into `e1`, and `rankM` does change at the LABEL level (`rankM e1 = 1 ≠ 0 = rankM e0`) — the
  full measure is NOT globally conserved (as the phase thesis foretells: no global conservation). But WITHIN THE
  SELF'S SIGHT — the plain relating, the plain-bisimulation quotient — `e1` and its constituent `e0` are IDENTIFIED
  (`ws1_atomless_bisim`, both `SHNE`): the self cannot see the rank increase. So the in-sight measure — any quantity
  read off the plain relating — is UNCHANGED by the tick; the rank increase is precisely the IMPORT, invisible
  in-sight. The tick re-encodes (a latent relation becomes an actual relatum, plain-bisimilar to its constituent)
  without adding in-sight distinction. This is a THEOREM (the reified relatum is plain-bisimilar to its constituent),
  resting on the collapse engine, NOT a definitional triviality: `rankM` was free to jump in-sight, and does not.
  This is exactly `∇_μ T^{μν} = 0` (locally conserved) with the global failing for want of a global time symmetry.
- **(D) The diagonal test is genuine — PASSES, see §2.** Both FREE-LUNCH and CONSERVED reachable, on the diagonal.

Candidate 1 SURVIVES all four gates. It earns the WS designs.

### Candidate 2 — `Q := ` the count of distinct `¬ Recoverable` labels on a carrier. REJECTED (not computable).

`Recoverable` / `IsBisim` are Prop-valued over arbitrary relations and are NOT decidable; a count of `Recoverable`
facts is not a computable `ℕ`-valued function and cannot be `decide`d non-trivial or conserved. The rank of Candidate
1 is the computable proxy: a genuine `¬ Recoverable` distinction is CERTIFIED by a rank gap (the `ws2_many_general`
mechanism), so the rank IS the count of import-steps, made computable. Candidate 1 subsumes this honestly.

### Candidate 3 — `Q := latent + actual`, with the tick defined `latent ↦ actual`. REJECTED (rigged, §4.c).

If `Q = latent + actual` and the tick is DEFINED to move one unit from `latent` to `actual`, conservation is true by
construction — the rigged sin (§4.c, audit b). The tick's conservation would be a `rfl`, not a theorem about an
independent `Q`. Rejected. (Candidate 1's conservation is genuine: `rankM` is NOT defined to be tick-invariant, and
in fact changes at the label level; only the in-sight/plain reading is conserved, and that is a theorem.)

---

## 2. The diagonal test (D), by hand — the free-lunch crux

The residue (the P1 diagonal) is `residue insp = diag insp = fun h => ¬ insp h h`, and it is FREE for every
inspection: `ws2_residue_free : ¬ ResidueRecoverable insp` (transitively `P1.Core`). So self-inspection ALWAYS
produces a genuinely non-recoverable content, endogenously — no import crosses the self's boundary. The free-lunch
crux (charter §2 WS4): is that fresh content a NEW unit of distinction (`Q` rises — the diagonal CREATES from within,
FREE-LUNCH) or already latent (`Q` unchanged — the diagonal RELOCATES, CONSERVED)?

Both readings are genuinely reachable, and the fork is about the DIAGONAL (the residue), not import-ness:

- **FREE-LUNCH reachable (by hand).** From ONE self-inspecting position (an inhabited `Hold` on the carrier), the
  diagonal produces at least TWO DISTINCT free residues: `ws1_coincidence_not_identity_witness` gives inspections
  `insp₁, insp₂` with `residue insp₁ ≠ residue insp₂`, each free (`ws2_residue_free`). So self-reference manufactures
  a genuine PLURALITY of distinct non-recoverable distinctions from within a single position, with no import crossing
  the boundary: the diagonal CAN be a genuine internal source. The measure rises (a fresh non-recoverable content
  beyond the budget). This rests on `ws2_residue_free` and the residue-distinctness witness — the diagonal, not
  boundary import-ness (costume gate, audit c).
- **CONSERVED reachable (by hand).** Relative to a configuration whose latent budget already contains the residue's
  content, the diagonal step actualizes it WITHOUT net increase: the free residue relocates onto an already-counted
  latent slot, `Q` unchanged. This is constructible (the budget is a free parameter of the configuration), so the
  diagonal is NOT FORCED to be net-creative — whether it creates depends on what is already latent, which is
  self-relative.

Because BOTH are reachable and neither forced, the free-lunch crux is SELF-RELATIVE (the S6 shape: WOVEN/SEVERED
both reachable, the continuity self-relative). The honest computed reading (WS5): CONSERVED-RELATIVE — the measure is
conserved in-sight (T), the import is its source (WS3), the global fails (no global conservation), and whether
self-reference is a net source is genuinely open both ways (a reachable FREE-LUNCH, a reachable CONSERVED),
undecidable from within.

**The bookkeeping skeleton, disclosed (like S6's meta-flags).** The create-vs-relocate arithmetic is carried by a
small decidable count (`Qc B = B.card`, `diagStep B d = insert d B`): FREE-LUNCH is `d ∉ B → card` rises; CONSERVED
is `d ∈ B → card` unchanged. The count is the skeleton; the LOAD-BEARING genuine content is `ws2_residue_free` (the
diagonal yields a real non-recoverable content endogenously) and `ws1_coincidence_not_identity_witness` (it yields
≥ 2 distinct such contents, so "the residue is a distinct new content" is realized, not stipulated). This split is
disclosed in `ws4-design.md` and the ledger, and graded honestly (not hidden), per protocol §0.2/§0.5.

---

## 3. Verdict of the de-risking

A measure survives: **Candidate 1, `Q := rankM`, the reification rank**, clears (N), (I), (T), (D). The series does
NOT land DISCONNECTED. It proceeds to the WS designs with `Q := rankM`, the tick's in-sight conservation resting on
the collapse engine, the change-is-import resting on Series 07, and the free-lunch crux resting on the P1 diagonal
(`ws2_residue_free`), both readings reachable. The expected computed close is CONSERVED-RELATIVE (charter §6,
protocol §7); the verdict is computed, not asserted here.
