# Program 2 Series 7 (2.7) — Design index (`spec/README.md`)

**THE LEDGER, the physics capstone. This is the design batch for Series 2.7: FIND a self-relative measure of
distinction `Q` (WS1, the risky ground; found — `measure-derisking.md`, `Q := rankM`), prove the tick conserves it
in-sight (WS2, conserved-relative), the import its sole source (WS3, Series 07, the general-relativity shape), and
at the knot fork the free-lunch crux — does the diagonal CREATE `Q` (FREE-LUNCH) or RELOCATE it (CONSERVED), both
reachable so the crux is self-relative (WS4) — the verdict computed (WS5), no global conservation asserted (the
phase thesis). It fixes the imported chain, the ONE new primitive (the measure `Q`, built fresh and de-risked), the
discipline, the cross-workstream triage, the outcome classes, and the names-in-prose rule. The measure was
de-risked ON PAPER first (`measure-derisking.md`, the Phase B gate for this series); this batch — that file plus
`ws1-design.md`…`ws5-design.md` and this README — is committed as one batch before any `formal/` file exists.**

---

## 1. The imported chain (reached, not rebuilt)

Series 2.7 imports **`P2S6` only** and reaches `P2S5` / `P2S4` / `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1`
transitively (the layered chain; the gate enforces `^import (P2S6|P2S7)…`). Its working material, reached through
the chain:

| Piece | Origin (transitive) |
|---|---|
| The recoverability / import test: `Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `ws4_recoverable_not_import`, `ws1_atomless_bisim` (the collapse engine), `ws3_atomless_distinct_is_import`, `LkObj`, `PkObj`, `SHNE` | `P1.Core` / `P2S0` |
| The rank-labelled lift and the attention-distinction: `rankLift`, `AttentionDistinguishes`, `ws2_many_general` | `P1.Reader` / `P2S0` |
| **The P1 diagonal (the free-lunch test object):** `Hold`, `HoldPred`, `diag`, `residue`, `ResidueRecoverable`, `ws2_residue_free`, `ws1_coincidence_not_identity_witness`, `Opening` | `P1.Core` (transitive) |
| The tick (reification-under-attention), `outDest`, `finsetToPk`, `FinReify` | `P2S1` / `P2S0` |
| **The measure `Q`** (a self-relative measure of distinction, the reification rank, the conjugate of the tick) | **built fresh at S7 WS1 — the risky ground, de-risked on paper first** |

## 2. The one new primitive: the measure `Q`

Series 2.7 adds exactly one thing, and it is the hard thing: the **measure `Q := rankM`**, a self-relative measure
of distinction on the witness carrier (the reification rank, the accumulated import-content). It is defined
STRUCTURALLY — the tower height, with no reference to conservation (WS2) or diagonal status (WS4), which are proved
of the independent `Q` (charter §4.c, audit b). It proves exactly three kinds of things: the measure is non-trivial
(WS1), the tick preserves it in-sight (WS2), and the import is its sole source (WS3), with the free-lunch crux the
genuinely-uncertain knot (WS4). No new structural machinery beyond the measure; no asserted global conservation;
the diagonal's status as a source is the crux, not an assumption.

## 3. The witness carrier (shared object)

`MCar := Fin 4`. `e0, e0' : MCar` two base relata (rank 0, rank NON-INJECTIVE); `e1 := reifyM {e0}` a reified
relatum (rank 1, an actualized tick-product); `e2 := reifyM {e1}` a reified relatum (rank 2) carrying `e1`.
`attendsM`: `e0`,`e0'` self-loop; `e1 → e0`; `e2 → e1` (pointwise sections `attendsM (reifyM {e0}) = {e0}`,
`attendsM (reifyM {e1}) = {e1}`). `rankM`: `e0,e0' ↦ 0`, `e1 ↦ 1`, `e2 ↦ 2` (THE MEASURE `Q`). The measure lift
`destML hinf := rankLift (outDest hinf attendsM) rankM`. All four states `SHNE` (the collapse engine applies). The
diagonal works on holds of the plain coalgebra `outDest hinf attendsM` (inhabited: `e0` self-loops).

## 4. The discipline (the honesty invariants, this series)

- **No global conservation (§4.a, audit a).** No proof term asserts a globally conserved `Q`; conservation is
  IN-SIGHT (the plain-bisim quotient), changed at the import (WS3). The full rank does change at the label level.
  A global invariant is claimed only if forced (then `global`, the finding); `globalForced` is honestly false.
- **The knot is the diagonal-as-source, not import-ness (§4.b, audit c, the costume gate).** WS4 rests on the
  residue (`ws2_residue_free`, `ws1_coincidence_not_identity_witness`) — the P1 diagonal — not on boundary
  import-ness. Import-ness alone (WS3) never decides the verdict (returns `partial'`).
- **The measure non-trivial and not rigged (§4.c, audit b).** `Q := rankM` is structural; non-triviality,
  conservation, and diagonal status are theorems about it, not built in.
- **The fork not by fiat (§4.d, audit d).** FREE-LUNCH and CONSERVED both reachable; the crux self-relative.
- **The import quantified, never named (§4.e, audit e).** No proof term is named "measure", "energy",
  "conservation", "information", "creation", "self", "import", "God", "choice", or "subjectivity" as content; the
  §6 grep guards it (docstring prose excepted).
- **DISCONNECTED is honorable (§0.9).** If no measure had survived the de-risking, the series would land
  DISCONNECTED. One survived (`rankM`); the series proceeds.

## 5. Cross-workstream triage

| WS | Payoff | Rests on | Strips to |
|----|--------|----------|-----------|
| WS1 | `ws1_measure_nontrivial` | collapse engine + rank gap | "a function on configs taking two distinct values, the difference an import" |
| WS2 | `ws2_tick_conserves` | `ws1_atomless_bisim` | "reify {e0} and e0 are plain-bisimilar (in-sight same)" |
| WS3 | `ws3_change_is_import` | Series 07 (`ws4_recoverable_not_import`) | "different rank + plain-bisimilar ⇒ ¬ Recoverable" |
| WS4 | `ws4_free_lunch_reachable` / `ws4_conserved_reachable` | `ws2_residue_free`, `ws1_coincidence_not_identity_witness` (+ decidable count skeleton, disclosed) | "self-inspection yields distinct free residues (create) / a residue within budget (relocate), both reachable" |
| WS5 | `verdict` = `conservedRel`, discriminating, flags justified, audit a–e | WS1–WS4 | "a discriminating `Bool⁶ → Outcome`" |

## 6. The outcome classes (WS5)

`conservedRel` (the expected close: Q conserved in-sight, import the source, free-lunch self-relative, global
fails); `monotoneOnly` (nothing conserved even in-sight); `freeLunch` (the diagonal a genuine source, creation
forced); `global` (a genuine absolute invariant forced — contradicts the phase thesis, positioning rewritten);
`disconnected` (no non-trivial measure); `partial'` (degenerate). The verdict is the residue of the process, not
its premise.

## 7. Module naming and registration (Phase E)

Namespace `P2S7`. Layout `formal/P2S7.lean` (imports `P2S7.ws1`…`P2S7.ws5`), `formal/P2S7/wsN.lean`,
`formal/P2S7/AxiomCheck.lean`. `ws1` imports `P2S6` (the chain); `ws2`/`ws3`/`ws4` import the prior `ws`;
`ws5` imports `ws1`…`ws4`. Registration in `lake/lakefile.toml` (`[[lean_lib]] name = "P2S7"`, appended to
`defaultTargets`) and `scripts/gate.sh` (`check program-2/series-7 "^import (P2S6|P2S7)(\.[A-Za-z0-9_]+)*$"`) at
Phase E, never earlier.

## 8. The names-in-prose rule

The concept-words ("measure", "energy", "conservation", "information", "creation", "self", "import", …) appear in
this series' subject and MAY appear freely in docstring prose. They may NOT name any proof term, definition, or
discharged obligation as content. The carrier-bearing objects use neutral Lean names (`MCar`, `rankM`, `destML`,
`Qc`, `diagStep`, `Outcome`, `verdict`). The §6 grep guards the content-names; hits must be docstring prose only.
