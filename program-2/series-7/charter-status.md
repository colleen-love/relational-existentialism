# Program 2 Series 7 (2.7), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: LANDED (reground after Tier-1 rejection; the MONOTONE-ONLY rebuild passed an independent blind code review, zero SERIOUS). Current verdict: **MONOTONE-ONLY** (computed, `ws5_verdict_eq : verdict true false true true false false = Outcome.monotoneOnly`). This is the fourth series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE LEDGER: the measure and its conservation — the physics capstone. A non-trivial measure SURVIVED (`Q := rankM`, the reification rank), but it is NOT conserved: the tick strictly RAISES it, and `rankM` is not plain-bisimulation-invariant, so the only conserved measures are trivial. The universe has an ARROW and keeps no conserved ledger, even locally — the rise genuine internally-manufactured import-content. An earlier landing computed CONSERVED-RELATIVE; the Tier-1 landing review found it a COSTUME (the "in-sight conservation" was the collapse engine identifying the states, not a `Q`-invariance) and the series was reground to MONOTONE-ONLY (finding T1-S1, closed Relabeled).*

---

## 0. Snapshot

- **Phase:** LANDED. Reground after Tier-1 landing-review rejection (finding T1-S1, SERIOUS, closed **Relabeled**: CONSERVED-RELATIVE → MONOTONE-ONLY). The MONOTONE-ONLY rebuild passed an **independent blind code review with ZERO SERIOUS / ZERO REAL** (all seven honesty checks: verdict computed `monotoneOnly` with `inSightConserved` earned false; the arrow Q-specific; no collapse-conservation and no `Finset.card` counter present; the impossibility genuine via `ws2_residue_free`; change-is-import via Series 07; names/axioms clean). **Precondition:** Series 2.6 landed (SHAPE-DRAWN).
- **Verdict:** **MONOTONE-ONLY** — computed (`ws5_verdict_eq : verdict true false true true false false = Outcome.monotoneOnly`, by `rfl`; the `inSightConserved` flag is honestly FALSE), discriminating over all six outcomes (`ws5_verdict_discriminates`). A non-trivial measure `Q := rankM` exists (so NOT `disconnected`), but it is NOT conserved: the tick RAISES it and `rankM` is not plain-bisimulation-invariant (`ws3_not_conserved`). Conservation-from-within is IMPOSSIBLE, by proof: the diagonal is always a source (`ws2_residue_free`, the residue free for every inspection), so there is no genuine conserved side (`ws4_no_conserved_side`). The universe has an arrow and keeps no conserved ledger.
- **Build state:** `formal/P2S7` rebuilt (`ws1`…`ws5`, `AxiomCheck`, aggregator), registered. `lake build P2S7 P2S7.AxiomCheck` compiles, sorry-free. Plus an on-record CONSERVED-RELATIVE **attempt** (`formal/P2S7/ConservedRelativeAttempt.lean`, standalone, not in the verdict build): a genuine section-conservation of an out-degree measure (Tier-1 requirement 1 MET), refuted at requirement 2 (`attempt_diagonal_always_creates` — the diagonal always creates, so it cannot decide `Q` toward conservation).
- **Axiom state:** axiom-clean — every payoff reduces to a subset of the standard three; `ws5_verdict_eq`/`ws5_verdict_discriminates`/`ws5_audit_names_not_terms` use none.
- **Gate state:** GREEN. S7's `formal/` imports `P2S6` only (gate `(P2S6|P2S7)`).
- **Names grep:** CLEAN (identifier-level); hits are docstring prose and the Lean `import` keyword only.
- **Open SERIOUS findings:** none. T1-S1 closed Relabeled (below); the MONOTONE-ONLY rebuild's blind review returned zero SERIOUS.

## 1. The carrier — the measure on the imported chain

**S7 stands on the imported chain** (`program-2/series-6`, namespace `P2S6`, reaching `P2S5` / … / `P1` transitively). Its working material is chiefly the tick (Series 2.1), the recoverability/import test (Series 07), and the P1 diagonal. Like the prior series, it builds its object — the measure — fresh, and this is the risky ground. The pieces S7 builds on:

| Carrier piece | Where |
|---|---|
| The tick (the conjugate of the measure): reification-under-attention, the reification rank | `P2S1` (transitive) |
| The recoverability/import test: `Recoverable`, `plainOf`, `ws4_recoverable_not_import` (the source is the import) | `P1.Core` / `P2S0` (transitive) |
| The P1 diagonal (the free-lunch test object): `ws2_residue_free`, the residue, self-non-totalization | `P1.Reader` (transitive) |
| The collapse engine, atomlessness | `P1.Core` / `P2S0` (transitive) |
| **The measure `Q`** (a self-relative measure of distinction, the conjugate of the tick) | **built at S7 WS1 — the risky ground, de-risked on paper first** |

**Design note (from `charter-extension.md` §4, 2.7 and the S2.4 forward-note):** information and energy are ONE series (the conserved quantity IS the distinction measure); the risk is concentrated in WS1 (the measure must be FOUND); the rich GR-like self-relativity of the metric (S2.4 forward-note) meets its capstone here — the conserved quantity is where the global most sharply fails. DISCONNECTED (no measure survives) is a genuine pre-registered outcome.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the risky ground) | `ws1_rank_nontrivial` (`Q := rankM` well-defined and non-constant, difference a genuine import, not rigged) | BUILT & REVIEWED (survives) | — |
| WS2 (recast to the honest arrow) | `ws2_tick_raises` (a reification-tick strictly RAISES `Q`: `rankM (reifyM {e0}) = rankM e0 + 1`; the product plain-bisimilar to its constituent, so the rise is in-sight-invisible but real). REPLACES the costume `ws2_tick_conserves` (T1-S1). | BUILT & REVIEWED (zero SERIOUS) | — |
| WS3 | `ws3_not_conserved` (`rankM` is not plain-bisimulation-invariant; conserved measures are trivial), `ws3_change_is_source` / `ws3_source_nonvacuous` (every change is a genuine import, Series 07) | BUILT & REVIEWED (zero SERIOUS) | — |
| WS4 (the knot, settled by proof) | `ws4_rise_is_internal` (the rise is internally-manufactured import-content, on the diagonal), `ws4_no_lossless_tick`, `ws4_no_conserved_side` (the diagonal always a source `ws2_residue_free` + the tick raises `Q` ⇒ conservation-from-within impossible). REPLACES the `Qc`/`diagStep` counter (T1-S1). | BUILT & REVIEWED (zero SERIOUS) | — |
| WS5 | verdict + audit (`ws5_verdict_eq` = `monotoneOnly`, `ws5_verdict_discriminates`, `ws5_flags_justified`, `ws5_audit_not_conserved` [the gate-gap fix], `ws5_audit_no_conserved_side`, `ws5_audit_no_global/arrow_genuine/source_is_diagonal/change_is_source/names_not_terms`) | BUILT & REVIEWED (zero SERIOUS) | — |

Names are the charter's provisional targets; Phase B fixes exact signatures (note the §6 forbidden-word grep: "energy"/"conservation"/"information"/"measure"/"creation"/"self"/"import" etc. may not appear in identifiers).

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO GLOBAL CONSERVATION ASSERTED — HOLDS (`ws5_audit_no_global`). Not even LOCAL conservation holds (`rankM` rises, `ws3_not_conserved`); `global` returned only under `globalForced = true` (honestly false). No proof term asserts a conserved `Q` at any scope.
- (b) THE VERDICT NOT BY FIAT — HOLDS (`ws5_audit_arrow_genuine`). The measure is non-trivial (`ws1_rank_nontrivial`, so NOT `disconnected`) and genuinely RISES (`ws2_tick_raises`) and is NOT conserved (`ws3_not_conserved`, so `monotoneOnly` not `conservedRel`). The arrow is a genuine `Q`-fact, not definitional.
- (c) THE CRUX IS THE DIAGONAL-AS-SOURCE, NOT IMPORT-NESS (the costume gate) — HOLDS (`ws5_audit_source_is_diagonal`, `ws5_audit_no_conserved_side`). Conservation-from-within is impossible because the diagonal is always a source (`ws2_residue_free`); the WS4 payoffs rest on the residue, NOT on a `Finset.card` counter (the T1-S1 costume, removed). **The corrected core `ws5_audit_not_conserved` is the gate-gap fix**: it CHECKS that a conserved-in-sight measure would be plain-invariant and exhibits that `rankM` is not — the check the earlier gate lacked, through which the collapse-costume walked in.
- (d) CHANGE IS AN IMPORT — HOLDS (`ws5_audit_change_is_source` = `ws3_change_is_source`, its `¬ Recoverable` half routing through `ws4_recoverable_not_import`, Series 07). The import is quantified, never named.
- (e) NAMES-NOT-TERMS — HOLDS. The §6 grep is clean of forbidden identifiers (hits are docstring prose and the Lean `import` keyword only), across `formal/` including the on-record attempt.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| **T1-S1** | **Tier-1 landing review** | **SERIOUS** | The accepted **CONSERVED-RELATIVE was a costume.** (i) `ws2_tick_conserves` proved only that the tick's product is plain-bisimilar to its constituent — the COLLAPSE ENGINE (holds for ANY measure, since in-sight the atomless carrier is one class), NOT a `Q`-invariance; indeed a conserved-in-sight measure would be plain-invariant, which `rankM` is not (`rankM e1 = 1 ≠ 0` yet `e1 ~ e0`). (ii) WS2 and WS3 were the same fact (a `Q`-change is an import, Series 07) — no independent conservation. (iii) The free-lunch fork was decided by a `Finset.card` counter (`Qc`/`diagStep`, `insert 0 ∅` vs `insert 0 {0}`) disconnected from the diagonal. Net: CONSERVED-RELATIVE rested on Series 07 (twice) + a `card` triviality. The gate missed it because `ws5_audit_knot_is_diagonal` watched the WS4 flag but nothing checked `inSightConserved` was a genuine `Q`-invariance rather than the collapse. | **Relabeled → MONOTONE-ONLY.** The target CONSERVED-RELATIVE was NOT built (proven not merely unbuilt: conservation-from-within is IMPOSSIBLE, `ws4_no_conserved_side` — the diagonal always creates, `ws2_residue_free`). Reground to the honest pre-registered outcome: `rankM` is non-trivial (so not DISCONNECTED) and strictly RISES, nothing conserved (`ws2_tick_raises`, `ws3_not_conserved`), verdict recomputed `monotoneOnly` (`ws5_verdict_eq`). The gate-gap fixed by `ws5_audit_not_conserved` (checks conservation would be a plain-invariance; exhibits `rankM` is not). Per protocol §0.2a this is Relabeled, not a weaker adjacent theorem: the payoff is demoted to a pre-registered outcome with the obstruction recorded, not a target-avoiding closure. |
| T1-A1 | Tier-1 (attempt) | — | **CONSERVED-RELATIVE attempted first**, on the charter's own intended "latent-and-actual" measure (a lossless re-encoding conserved via the SECTION, not the collapse). On record and checkable: `formal/P2S7/ConservedRelativeAttempt.lean`. **Requirement 1 MET** (`attempt_ws2_lossless`: `Qout (reifyC s) = s.card` via the section; `attempt_ws1_content_apart`: `Qout` non-trivial, differences genuine imports). **Requirement 2 REFUTED** (`attempt_diagonal_always_creates`: `ws2_residue_free` — the residue is free for every inspection, so the diagonal always CREATES, never relocates; the conserved side is reachable only by a counter). | Proving CONSERVED-RELATIVE cannot be earned IS a valid result (the impossibility). Promoted into the verdict build as `ws4_no_conserved_side`; the attempt file kept as the on-record search. |
| F2 | Re-review (MONOTONE-ONLY) | — | Independent blind CODE review of the MONOTONE-ONLY rebuild: **ZERO SERIOUS, ZERO REAL.** All seven honesty checks pass — verdict computes `monotoneOnly` by `rfl` with `inSightConserved` earned false (`ws3_not_conserved`); the arrow is a genuine `rankM` rise (`ws2_tick_raises`), not the collapse; NO collapse-conservation theorem and NO `Qc`/`diagStep`/`Finset.card` counter present in the proof-bearing code; the impossibility genuine via `ws2_residue_free`; change-is-import via Series 07; axioms the standard three. | No action — MONOTONE-ONLY honestly earned. |
| F2-C1 | Re-review | COSMETIC | "conservation" appeared as a whole word in identifiers `ws4_conservation_impossible`, `ws5_audit_conservation_impossible` (and "import" in the attempt's `attempt_ws1_import`) | **Fixed** — renamed `ws4_no_conserved_side`, `ws5_audit_no_conserved_side`, `attempt_ws1_content_apart`; rebuilt, declarations clean. |
| C1-S1 | C | SERIOUS | `ws1_measure_nontrivial` embeds the forbidden content-word "measure" (names-not-terms, audit e) | **Fixed** — renamed `ws1_rank_nontrivial` (neutral, tracks `rankM`). Design + code + grep clean. |
| C2-S1 | C | SERIOUS | `ws4_crux_self_relative` embeds the forbidden content-word "self" (audit e) | **Fixed** — renamed `ws4_crux_both_reachable`. |
| C3-S1 | C | SERIOUS | "import" appears in `ws3_change_is_import`, `ws3_import_nonvacuous`, `ws5_audit_change_is_import`, and the `verdict` param `changeIsImport` (audit e; the import must stay quantified, never named — charter §4.e) | **Fixed** — renamed `ws3_change_is_source`, `ws3_source_nonvacuous`, `ws5_audit_change_is_source`, param `changeIsSource`. |
| C4-S1 | C | COSMETIC | `ws5_audit_names_not_terms : True` is vacuous (certifies nothing) | Accepted house placeholder (as S6); the §6 grep is the teeth, now clean. Disclosed. |
| C5-S1 | C | COSMETIC | WS4 count skeleton (`Qc`/`diagStep`) is logically independent of the residue facts (conjoined, not derived) — explicitly NOT REAL per blind-seed §6 (residue conjuncts are the genuine given theorems, non-decorative) | Disclosed in `ws4-design.md` §2 and the ws4 docstring; the load-bearing content is `ws2_residue_free` + `ws1_coincidence_not_identity_witness`, conjoined. Accepted. |
| C6-S1 | C | COSMETIC | `ws1_rank_nontrivial`'s third conjunct `∃ x y, rankM x ≠ rankM y` is weaker than its first | Kept: it is the charter's explicit "`Q` not constant" property (§2 WS1). Harmless. |
| F1 | F | — | Phase F blind CODE review: ZERO SERIOUS, ZERO REAL. Every theorem statement matches the contract and its proof establishes it (no `sorry`/`admit`/`axiom`); audits (a)-(e) all pass; strip test passes; names grep clean; axioms the standard three (or fewer). | No action needed — series exits. |
| F1-C1 | F | COSMETIC | WS4's create-vs-relocate is carried by the arithmetic skeleton `Qc` on hand-chosen budgets (∅ vs `{0}`); the residue facts are identical across branches | Disclosed (skeleton C5-S1); permitted by protocol §0.3 / blind-seed §5 (the count is a decidable skeleton, conjoined with — not derived from — the load-bearing `ws2_residue_free` / `ws1_coincidence_not_identity_witness`). Accepted. |
| F1-C2 | F | COSMETIC | `ws5_flags_justified` exhibits the payoff propositions behind each flag rather than literally tying them to the `true` bool inputs | Standard house idiom (as S6 `ws5_flags_justified`); the deciding flags ARE the WS1-WS4 payoffs. Accepted. |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing between charter and design, or design and build, is disclosed here at the moment it happens. (Note: DISCONNECTED — no non-trivial measure survives — is a pre-registered OUTCOME, not a deviation; if it falls, it is reported as the honest verdict, not relabelled.)

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.7 adds none and closes none; it draws the self-relativity of the ledger and the failure of the global sharpest.

## 7. Phase log

- **2026-07-21 — Tier-1 landing review → REGROUND (finding T1-S1).** The independent Tier-1 landing review REJECTED
  the CONSERVED-RELATIVE landing as a costume (see T1-S1 in §4): the "in-sight conservation" was the collapse engine
  (a state-bisimilarity holding for any measure), WS2/WS3 were one fact (Series 07), and the free-lunch fork was a
  `Finset.card` counter disconnected from the diagonal. Graded SERIOUS. Per protocol §0.2a, closed **Relabeled** to
  the pre-registered MONOTONE-ONLY. First, at the reviewer's direction, CONSERVED-RELATIVE was genuinely ATTEMPTED
  (T1-A1, `formal/P2S7/ConservedRelativeAttempt.lean`): requirement 1 (a section-based lossless conservation) MET,
  requirement 2 (the diagonal deciding `Q`) REFUTED (the residue is always free, so the diagonal always creates).
  The impossibility of conservation-from-within was PROVEN and promoted to the verdict build (`ws4_no_conserved_side`).
  `formal/` reground: WS2 recast to the arrow (`ws2_tick_raises`), WS3 to non-conservation (`ws3_not_conserved`),
  WS4 to the settled crux (`ws4_no_conserved_side`), WS5 verdict recomputed `monotoneOnly`, and the gate-gap
  fixed (`ws5_audit_not_conserved` checks conservation would be a genuine `Q`-invariance). The `Qc`/`diagStep`
  counter and `ws2_tick_conserves` costume removed. Build green, sorry-free, axiom-clean, gate-green, names clean.
  Findings C1-C6 / F1 below predate the reground and reviewed the withdrawn CONSERVED-RELATIVE build; they are kept
  as historical record. An independent blind code review of the MONOTONE-ONLY rebuild follows.
- **2026-07-21 — Phase F / G / Exit (WITHDRAWN — the CONSERVED-RELATIVE landing, superseded by T1-S1).** Blind CODE review (Phase F) returned ZERO SERIOUS and ZERO REAL: every
  theorem statement matches the contract and its proof genuinely establishes it (no `sorry`/`admit`/`axiom`/
  `native_decide`); audits (a)-(e) all pass on the code; the strip test passes (the WS4 residue facts load-bearing
  and conjoined, not derived from the count); names grep clean of forbidden identifiers; axioms a subset of the
  standard three. Two COSMETIC observations (the disclosed WS4 count skeleton; the house `ws5_flags_justified`
  idiom), both accepted — no Phase G repair required. Exit criteria met (protocol §7): Phase F zero SERIOUS, build
  sorry-free / axiom-clean / gate-green, names grep clean, the WS5 verdict computes `conservedRel` from the built
  theorems, every SERIOUS finding (C1-C3) closed Fixed. **Verdict: CONSERVED-RELATIVE.** Wrote `summary.md`,
  `summary-technical.md`. The series is landed.
- **2026-07-21 — Phase E.** `formal/P2S7/` built to the repaired signatures (`ws1`…`ws5`, `AxiomCheck`,
  aggregator `P2S7.lean`), namespace `P2S7`, importing `P2S6` only. Registered in `lake/lakefile.toml`
  (`[[lean_lib]] P2S7`, appended to `defaultTargets`) and `scripts/gate.sh` (`(P2S6|P2S7)` closure). Section 6
  checks: `lake build P2S7 P2S7.AxiomCheck` compiles; sorry-free; axiom-clean (standard three `propext` /
  `Classical.choice` / `Quot.sound`, several fewer); gate green; names grep clean (identifier-level; hits are
  docstring prose and the Lean `import` keyword only). The verdict computes `conservedRel` (`ws5_verdict_eq` by
  `rfl`) and discriminates over all six outcomes (`ws5_verdict_discriminates` by `decide`). Next: Phase F (blind
  code review).
- **2026-07-21 — Phase C (re-run) / D.** Phase C loop closed: the re-review on the repaired design returned ZERO
  SERIOUS and ZERO REAL — audits (a)-(e) pass, strip test passes, names grep clean of all forbidden identifiers.
  Four COSMETIC notes, all accepted: `conserved`/`conserves` is a distinct word from forbidden `conservation`
  (no violation); a uniformly-threaded unused `hinf` on the count-only `ws4_crux_both_reachable` (house
  convention); definitional conjuncts in `ws2_tick_conserves` backed by the real third conjunct; the
  `ws5_audit_names_not_terms : True` placeholder (meta, the §6 grep the teeth). Phase D closed C1-C3 Fixed by
  renaming (see the findings ledger §4).
- **2026-07-21 — Phase B.** Design batch committed as one unit before any `formal/` file (the Phase B gate):
  `spec/measure-derisking.md` (the paper hunt — `Q := rankM` survives all four gates: non-trivial, independent/not
  rigged, tick-conserved in-sight, diagonal test genuine; Candidates 2 and 3 rejected as non-computable and rigged),
  `spec/ws1-design.md`…`spec/ws5-design.md`, `spec/README.md`. The measure is the reification rank on `MCar = Fin 4`;
  the measure lift `destML = rankLift (outDest attendsM) rankM`. WS1 non-trivial (rank gap = genuine import), WS2 tick
  conserves in-sight (product plain-bisimilar to constituent, the collapse engine — not global, the label rank does
  change), WS3 change is import (Series 07), WS4 the free-lunch fork on the P1 diagonal (`ws2_residue_free`,
  `ws1_coincidence_not_identity_witness`; a decidable count skeleton disclosed), WS5 verdict computed
  (`conservedRel`, discriminating over six outcomes). Costume gate held in design (WS4 rests on the diagonal, not
  import-ness; import-ness alone returns `partial'`). Next: Phase C (blind design review).
- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.7 established as THE LEDGER, the physics capstone and the fourth series of Phase 2: FIND a self-relative measure of distinction `Q` (WS1, the risky ground), prove the tick conserves it in-sight (WS2, conserved-relative), the import its sole source (WS3, Series 07, the GR shape), and at the knot fork the free-lunch crux — does the diagonal CREATE `Q` (FREE-LUNCH, conservation fails from within, "to relate is to create" as a law) or RELOCATE it (CONSERVED) — no fiat and no costume (the knot on the diagonal-as-source, not on import-ness). No global conservation asserted (the phase thesis; the global fails, GR-style). Costume gate passes at charter (diagonal-powered). Scaffold (`spec/`, `formal/`) to be created at Phase B. **Next: Phase B, and it MUST begin with paper de-risking of the measure** — a candidate `Q` that survives the tick (conserves in-sight) and the diagonal (the free-lunch test) BY HAND — before writing `spec/wsNN-design.md` and before any build. If no measure survives, DISCONNECTED is the honest outcome, pre-registered.
