# Program 2 Series 7 (2.7), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: COMPLETE (Phase F returned zero SERIOUS; series landed). Current verdict: **CONSERVED-RELATIVE** (computed, `ws5_verdict_eq`). This is the fourth series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE LEDGER: the measure and its conservation — the physics capstone, and the hardest, its risk concentrated in WS1 (the measure must be FOUND). A measure SURVIVED the paper de-risking and the build: `Q := rankM` (the reification rank). The universe keeps a private ledger each self balances within its own sight, changed only at the import, no global books, the free-lunch crux self-relative.*

---

## 0. Snapshot

- **Phase:** ALL COMPLETE (A charter, B design + de-risking, C/D blind design review + repair to zero SERIOUS, E build, F/G blind code review to zero SERIOUS, Exit summaries). **Precondition:** Series 2.6 landed (SHAPE-DRAWN). **The measure was de-risked on paper first** (`spec/measure-derisking.md`): `Q := rankM` survives the tick (in-sight conservation, the collapse engine) and the diagonal (both fork sides reachable).
- **Verdict:** **CONSERVED-RELATIVE** — computed (`ws5_verdict_eq : verdict true true true true true false = Outcome.conservedRel`, by `rfl`), discriminating over all six outcomes (`ws5_verdict_discriminates`, by `decide`), the deciding flags earned by WS1–WS4 (`ws5_flags_justified`).
- **Build state:** `formal/P2S7` built (`ws1`…`ws5`, `AxiomCheck`, aggregator), registered in `lake/lakefile.toml` and `scripts/gate.sh`. `lake build P2S7 P2S7.AxiomCheck` compiles, sorry-free.
- **Axiom state:** axiom-clean — every payoff reduces to a subset of the standard three (`propext`, `Classical.choice`, `Quot.sound`); `ws4_crux_both_reachable` uses only `propext`/`Quot.sound`; the `verdict`/`decide` theorems use none.
- **Gate state:** GREEN. S7's `formal/` imports `P2S6` only (gate `(P2S6|P2S7)`), reaching S5–S0/P1 transitively.
- **Costume gate (Phase-2 discipline):** PASSES — verified at Phase F (audit c): the knot is DIAGONAL-powered (`ws5_audit_knot_is_diagonal`: import-ness alone returns `partial'`; the WS4 payoffs rest on `ws2_residue_free`), not import-powered.
- **Names grep:** CLEAN (identifier-level); hits are docstring prose and the Lean `import` keyword only.
- **Open SERIOUS findings:** none. Phase C final pass and Phase F pass each returned zero SERIOUS / zero REAL.

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
| WS1 (the risky ground) | `ws1_rank_nontrivial` (`Q := rankM` well-defined and non-constant, difference a genuine import, not rigged) | BUILT (Phase F pending) | — |
| WS2 | `ws2_tick_conserves` (a reification-tick preserves `Q` within the self's sight — conserved-relative, the product plain-bisimilar to its constituent) | BUILT (Phase F pending) | — |
| WS3 | `ws3_change_is_source` / `ws3_source_nonvacuous` (every change in `Q` is an import, the import the sole source, Series 07) | BUILT (Phase F pending) | — |
| WS4 (the knot) | the free-lunch fork: `ws4_free_lunch_reachable` / `ws4_conserved_reachable` / `ws4_crux_both_reachable` (the diagonal creates vs relocates, both reachable), on the diagonal not import-ness | BUILT (Phase F pending) | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, `ws5_audit_no_global/fork_genuine/knot_is_diagonal/change_is_source/names_not_terms`) — verdict computes `conservedRel`, discriminates over six | BUILT (Phase F pending) | — |

Names are the charter's provisional targets; Phase B fixes exact signatures (note the §6 forbidden-word grep: "energy"/"conservation"/"information"/"measure"/"creation"/"self"/"import" etc. may not appear in identifiers).

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO GLOBAL CONSERVATION ASSERTED — VERIFIED (`ws5_audit_no_global`). Conservation is FOR the in-sight plain-bisim relating, changed at the import; the label rank does change (`rankM e1 = 1 ≠ 0`); `global` returned only under `globalForced = true` (honestly false). No proof term asserts a globally conserved `Q`.
- (b) THE FORK NOT BY FIAT — VERIFIED (`ws5_audit_fork_genuine`). FREE-LUNCH (`ws4_free_lunch_reachable`) and CONSERVED (`ws4_conserved_reachable`) both reachable, the measure non-trivial (`ws1_rank_nontrivial`), the verdict discriminating.
- (c) THE KNOT IS THE DIAGONAL-AS-SOURCE, NOT THE IMPORT-NESS (the costume gate) — VERIFIED (`ws5_audit_knot_is_diagonal`). Import-ness alone (`changeIsSource = true`, `freeLunchReachable = false`) returns `partial'`; the WS4 payoffs rest on `ws2_residue_free` / `ws1_coincidence_not_identity_witness` (the diagonal), not boundary import-ness.
- (d) CHANGE IS AN IMPORT — VERIFIED (`ws5_audit_change_is_source` = `ws3_change_is_source`, its `¬ Recoverable` half routing through `ws4_recoverable_not_import`, Series 07). The import is quantified, never named.
- (e) NAMES-NOT-TERMS — VERIFIED. The §6 grep is clean of forbidden identifiers (hits are docstring prose and the Lean `import` keyword only); `ws5_audit_names_not_terms : True` the disclosed house placeholder, the grep the teeth.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
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

- **2026-07-21 — Phase F / G / Exit.** Blind CODE review (Phase F) returned ZERO SERIOUS and ZERO REAL: every
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
