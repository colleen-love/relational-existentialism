# Program 2 Series 1 (2.1), Charter Extension 1

**A clarification of the fixed charter, not an edit of it. The charter (`charter.md`) is the fixed bar and stays as written. This extension RAISES the bar on three obligations the first build met only to the letter, never lowers it. It is triggered by an independent post-exit review that re-graded three disclosed items to REAL: the arrow (WS2) is proved as NON-RECOVERABILITY, not directional irreversibility; the stream (WS3) is S0's generic `impLift` on `Bool`, disconnected from the actual tick machinery on `TCar`; and the residue (WS2) is a bare conjunction whose composite does no work. All three are the recurring "machinery genuine, tie-to-construction in prose" shape. This extension requires them rebuilt so the arrow is genuinely directional, the stream genuinely lives at the tick's choice-point on the real carrier, and the subtractivity is load-bearing. The CLOCK KNOT (WS4) — the two-zone fork, both witnessed pairs, the rank-constrained causal order, the quantified linearization import — is the series' best result and is UNTOUCHED. WS1 (the cycle reifies) is untouched. The verdict stays TWO-ZONE only if it now rests on the strengthened arrow and stream.**

*This extension is honest under protocol §0.2a because it only strengthens: it cannot launder a shortfall, since it makes each requirement harder, not easier. The findings close as (Fixed) — the originally intended target built at strength — except R3, which carries a pre-registered honest (Relabel) fallback if no genuine tie exists. Read it alongside `charter.md`; where they touch, the charter's intent governs and this extension says what discharging that intent requires.*

---

## 1. The findings this extension addresses

- **EXT-F1 (WS3, the stream — re-graded to REAL).** `ws3_stream_exogenous` is S0's `impLift` on `Bool`, reused verbatim; the tick's choice-point ("which of the available cycles closes") is *encoded as* `Bool` in prose, not tied to the actual `kA` / `kB` / `attendsT` machinery on `TCar`. The stream's exogeneity is genuine but GENERIC, not tick-specific. (Milder than it sounds: the verdict's load-bearing import is WS4's linearization `ord : TCar → ℕ`, which IS tick-specific and stands. But WS3, the workstream that claims the stream sits at the tick, does not deliver it there.)

- **EXT-F2 (WS2, the arrow — re-graded to REAL).** `ws2_tick_irreversible` proves `¬ Recoverable (rankLift … rankT)` — non-recoverability / distinction-freeness (the `ws2_distinction_free` pattern, disclosed), NOT directional irreversibility. The genuine directional arrow (the reification height strictly rises along causation) is actually WS4's `causal t u → rankT t < rankT u`. So "the tick does not invert" is carried by prose over a non-recoverability fact; the theorem named for the arrow is not the arrow.

- **EXT-F3 (WS2, the residue — re-graded to REAL).** `ws2_composite_residue` is an honest bare conjunction (disclosed): the subtractivity payoff IS the transcribed global diagonal `ws2_residue_free` (holding for every coalgebra, `kA` not mentioned), conjoined with a non-vacuity witness (`kA` has a hold) that does not interact with it. The composite's PARTIAL attention does no work; "partial attention is subtractive" is prose over a global fact.

## 2. The clarified requirements

**R1 — The arrow must be DIRECTIONAL (fixes EXT-F2).** Rebuild `ws2_tick_irreversible` as a genuine directional / acyclic statement: reification strictly raises the tower height from a tick's components to the composite — `∀ x ∈ attendsT kA, rankT x < rankT kA` (and generally, a reified cycle strictly outranks its members) — so the closure does NOT run backward (the composite is not a predecessor of its components; the tick relation is acyclic). This is what "the tick does not invert" means. Keep the `¬ Recoverable` fact as the COMPANION "the arrow is a genuine import" (Series 07: a genuine distinction is non-recoverable), but the DIRECTIONAL content must be the strict-order / acyclicity theorem, not `¬ Recoverable`. WS5's arrow flag must then rest on the directional theorem, not the reader.

**R2 — The stream must be TICK-SPECIFIC (fixes EXT-F1).** Rebuild WS3 so the stream's choice is an exogenous label on the ACTUAL tick carrier `TCar` — the choice among the tick's available closures / concurrent ticks (`kA`, `kB`) — with its non-recoverability proved ON `TCar` via the collapse engine (`ws1_atomless_bisim` on `outDest attendsT`), quantified over all such choice labels, never named. The stream IS the picker among concurrent closures on the real carrier (the WS4-linearization pattern, `ch : TCar → ℕ` distinguishing `kA`, `kB`), not a generic `Bool` disconnected from the tick. Rebuild `ws3_tick_needs_stream` likewise on `TCar`: the available closures are plain-identified there (the collapse), so without the stream the choice is indeterminate. The stream must stay NON-RECOVERABLE — tick-specific is not recoverable; a stream the plain relating could recover would collapse the dynamics to the One (Series 07).

**R3 — The subtractivity must be LOAD-BEARING (fixes EXT-F3).** Rebuild `ws2_composite_residue` so the composite's partial / finite attention DRIVES a genuine loss, not a bare conjunction of the global diagonal with a non-vacuity witness. Candidate: the composite is behaviorally related (the collapse engine) to relata it does NOT attend — attention is a proper part of relating (`∃ y, (∃ R, IsBisim (outDest hinf attendsT) R ∧ R kA y) ∧ y ∉ attendsT kA`), so the finite attention genuinely subtracts; or the diagonal residue tied to the composite's own holds as an implication. **Pre-registered honest fallback:** if no genuine tie is achievable, Relabel explicitly — present it as the transcribed global diagonal with the composite's subtractivity in prose, recorded in the ledger as (Relabel), NOT a bare conjunction dressed as an interaction. Either is honest; the current middle is the one flagged.

## 3. What must NOT change (the discipline preserved)

- **WS4 (the clock knot) is UNTOUCHED.** The two-zone fork, the witnessed causal pair and concurrent pair, the rank-constrained causal order, the quantified linearization import — the series' best result — all stand exactly. R2 reuses WS4's linearization *pattern* for the stream but must not alter WS4 itself.
- **WS1 (the cycle reifies) is untouched.**
- **TWO-ZONE is preserved, or the pre-registered alternative is reported honestly.** The verdict stays TWO-ZONE with the arrow flag re-pointed to R1's directional theorem and the stream flag to R2's tick-specific exogeneity. A rebuild that genuinely resists reports PARTIAL (or R3's Relabel), never a manufactured TWO-ZONE.
- **The stream stays non-recoverable (R2's teeth).** Tick-specific must not become recoverable-from-the-relating; that would collapse the dynamics and contradict the inherited Series 07 baseline.
- **No cardinal ceiling; names-not-terms; the reader load-bearing (K1, `ws2_composite_real_for`); the collapse inherited** — all stand.
- **Audit (e) stays grep-certified.** The `True` placeholder for names-not-terms is acceptable and inherent: the property is about identifiers, not a proposition, exactly as Program 1 established (`ws7_names_not_terms`). It is NOT part of this rebuild.

## 4. Concrete targets (guidance; exact signatures fixed at the re-run's design step)

- `ws2_tick_irreversible` (rebuilt, R1): `∀ x ∈ attendsT kA, rankT x < rankT kA` — the composite strictly outranks its components (the directional, acyclic arrow); the `¬ Recoverable` fact retained as the companion import.
- `ws3_stream_exogenous` (rebuilt, R2): `∀ ch : TCar → ℕ, ch kA ≠ ch kB → AttentionDistinguishes (rankLift (outDest hinf attendsT) ch) kA kB ∧ ¬ Recoverable (rankLift (outDest hinf attendsT) ch)` — on the real tick carrier, quantified, never named.
- `ws3_tick_needs_stream` (rebuilt, R2): on `TCar`, the available closures plain-identified (collapse engine), the stream's entry load-bearing.
- `ws2_composite_residue` (rebuilt, R3): a genuine subtractivity statement tied to the composite (attention ⊊ relating, or the diagonal as an implication), OR the honest (Relabel).
- `ws5_flags_justified` (re-pointed): the arrow flag ← R1's directional `ws2_tick_irreversible`; the stream flag ← R2's tick-specific `ws3_stream_exogenous`.

## 5. The re-run

Re-open WS2, WS3, WS5 (WS1 and WS4 are untouched). Run the affected workstreams through the protocol's phases again: design the strengthened signatures (Phase B for the re-opened workstreams), rebuild (Phase E), blind code review (Phase F), repair on any SERIOUS (Phase G), exit. In the ledger:

- Close **EXT-F1** and **EXT-F2** as **(Fixed)** — name the rebuilt tick-specific `ws3_stream_exogenous` and the directional `ws2_tick_irreversible`.
- Close **EXT-F3** as **(Fixed)** if the load-bearing subtractivity lands, or **(Relabel)** with the honest fallback recorded — never as a bare conjunction re-asserted.
- Re-run the §6 mechanical checks and re-confirm the audit clauses, with the arrow now directional and the stream now on `TCar`.
- Re-confirm the verdict computes TWO-ZONE from the strengthened flags, or report the pre-registered alternative honestly.

## 6. Why this is worth a pass before S2

S2 (the Other) leans on the tick's arrow and, for the symmetry-breaking that separates self from other, on the stream. Giving it a directional arrow (not non-recoverability relabeled) and a stream that genuinely lives on the tick's carrier (not a generic `Bool`) means S2 builds on what the prose says the ground delivers, rather than on a looser theorem underneath it. The clock knot already holds its weight; this pass makes the two supporting workstreams hold theirs, so the whole tick is clean before the second perspective arrives.
