# Program 2 Series 6 (2.6), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: E complete (formal build landed, sorry-free, axiom-clean, gate-green). Current verdict: SHAPE-DRAWN (computed at WS5). Targets built; pending the Phase F blind code review. This is the third series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE THREAD: the persistence of the self, and the single lived timeline.*

---

## 0. Snapshot

- **Phase:** E complete (formal build landed, mechanical checks green). A/B/C/D complete. **Precondition:** Series 2.5 landed before Phase B (ACYCLIC, including Charter Extension 1). Next: Phase F (blind code review).
- **Verdict:** SHAPE-DRAWN (computed by `ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn := rfl`). Strict identity fails across a tick and the single line is an import (the ground); the weak continuity is RECOVERABLE on the merged carrier (WOVEN) and an IMPORT on the cut carrier (SEVERED), both reachable, so its recoverability is SELF-RELATIVE and not forced. The self is at most a thread continuously re-woven; whether the relating carries the weave is self-relative, undecidable from within. To be confirmed at Phase F.
- **Build state:** `formal/P2S6.lean` + `P2S6/ws1..ws5.lean` + `P2S6/AxiomCheck.lean` built (registered in `lake/lakefile.toml`, `defaultTargets`, and `scripts/gate.sh`). `lake build P2S6 P2S6.AxiomCheck` compiles; sorry-free.
- **Axiom state:** every payoff is axiom-clean on the standard three (`propext`, `Classical.choice`, `Quot.sound`) or fewer (`ws5_verdict_eq`/`ws5_verdict_discriminates`/`ws5_audit_names_not_terms` depend on NO axioms; `ws3_line_not_scalar` on `propext` only).
- **Gate state:** green. S6's `formal/` imports `P2S5` only (gate `(P2S5|P2S6)`), reaching S4/S3/S2/S1/S0/P1 transitively; `bash scripts/gate.sh` reports OK for `program-2/series-6`.
- **Names grep:** clean of forbidden content-names as identifiers; all `\b(self|thread|persistence|life|death|time|...)\b` hits are docstring prose (verified Phase E).
- **Costume gate (Phase-2 discipline):** PASSES at charter — the knot is the WEAK THREAD (whether a recoverable continuity exists over the failure of strict identity) and the LINEARIZATION-import (the single line is the self's import), NOT the trivial failure of strict identity, and NOT rank being a scalar. To be verified at Phase F (audit c).
- **Open SERIOUS findings:** none (no review has run).

## 1. The carrier — the thread on the imported chain

**S6 stands on the imported chain** (`program-2/series-5`, namespace `P2S5`, reaching `P2S4` / `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively). Its working material is chiefly the Series 2.1 tick and its linearization import, and relational identity. The pieces S6 builds on:

| Carrier piece | Where |
|---|---|
| The tick and its linearization import: `ws4_linearization_import` (the total order of the moments is non-recoverable) | `P2S1` (transitive) |
| Relational identity, the collapse engine `ws1_atomless_bisim`, recoverability (`Recoverable`, `plainOf`) | `P1.Core` / `P2S0` (transitive) |
| The knowing-asymmetry (for attention-relative mortality): `ws3_direction_not_recoverable` | `P2S0` (transitive) |
| The reification rank / the partial causal order | `P2S1` / `P2S5` (transitive) |
| **The weak thread** (a successor-self continuity, weaker than strict identity) and the reading of the single line as the linearization import | **built at S6 WS1/WS2/WS3** |

**Design note (from `charter-extension.md` §4, 2.6):** the thread is TWO things — the persistence of identity AND the self's linearization of the partial causal order into one sequence (so 1D lived time is the linearization import). Its continuity is expected self-relative (continuous vs severed — the human/AI contrast made structural). The knot must rest on the weak thread and the linearization, not on strict identity trivially failing.

## 2. Targets (BUILT at Phase E; pending the Phase F code review)

| WS | Target theorem(s) (Phase B exact name) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_strict_fails` (charter `ws1_strict_identity_fails`): the reified successor is plain-bisimilar to its constituent yet rank-lift-separated (`AttentionDistinguishes`), the trivial ground; `succDep`/`ws1_succ_witnessed` the tick-successor | BUILT (E) | pending F |
| WS2 | `ws2_cont_recoverable` (charter `ws2_thread_recoverable`) / `ws2_cont_is_import` (charter `ws2_thread_is_import`); `ws2_weaker_than_strict`; the weak-continuity lifts `mergeLift`/`cutLift` | BUILT (E) | pending F |
| WS3 | `ws3_line_is_import` (charter `ws3_timeline_is_linearization_import`): the total order non-recoverable, on `P2S1.ws4_linearization_import`; `ws3_line_not_scalar`, `ws3_partial_order_endogenous` | BUILT (E) | pending F |
| WS4 (the knot) | `ws4_woven_reachable` / `ws4_severed_reachable` (the fork, both reachable), `ws4_carrier_relative` (self-relative), `ws4_cessation_relative` (charter `ws4_attention_relative_cessation`, the mortality companion), `ws4_conservative_reachable` | BUILT (E) | pending F |
| WS5 | `Outcome | woven | severed | shapeDrawn | partial'`, `verdict`, `ws5_verdict_eq` (= `shapeDrawn`), `ws5_verdict_discriminates`, `ws5_flags_justified`, `ws5_carrier_relative_verdict`, audit a–e (`ws5_audit_no_absolute`/`_fork_genuine`/`_knot_not_strict`/`_line_is_import`/`_names_not_terms`) | BUILT (E) | pending F |

**Renames (Phase B, §6 forbidden-word grep).** The charter's provisional target names embed forbidden content-words as whole words, so Phase B fixes neutral identifiers and records them here: `ws1_strict_identity_fails` → `ws1_strict_fails`; `ws2_thread_*` → `ws2_cont_*`; `ws3_timeline_is_linearization_import` → `ws3_line_is_import` (avoid "time"); `ws4_attention_relative_cessation` → `ws4_cessation_relative`; the fork outcomes THREADED/SEVERED → `Outcome.woven`/`Outcome.severed` (avoid "thread"); "self-relative" → `carrier_relative` in identifiers (avoid "self"). Carriers: `MCar`/`CCar` (merged/cut), `mergeLift`/`cutLift`, `succDep`. The interpretive words ("self," "thread," "persistence," "life," "death," "time," "timeline") appear only in docstring prose.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO ABSOLUTE PERSISTENCE — no proof term asserts the self persists frame-independently; continuity is FOR a self, self-relative, the single line the self's import. UNVERIFIED.
- (b) THE FORK NOT BY FIAT — THREADED and SEVERED both reachable, the weak thread genuinely weaker than strict identity, the verdict discriminating. UNVERIFIED.
- (c) THE KNOT IS THE WEAK THREAD, NOT THE STRICT FAILURE (the costume gate) — the verdict rests on the weak thread's recoverability and the linearization import, not on strict identity failing. UNVERIFIED.
- (d) THE LINE IS THE LINEARIZATION IMPORT — `ws3_timeline_is_linearization_import` rests on Series 2.1 / Series 07, the single line non-recoverable, not a scalar-rank triviality. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| C1-S1 | C | COSMETIC | `const_first_recoverable`/`ws2_cont_recoverable`: the WOVEN witness is the near-definitional constant-label recoverable ("cont" a lofty name for a uniform label). Reviewer confirmed NON-vacuous (pins WOVEN to `outDest attendsM` where the rank lift separates `m1`,`m0`), not the vacuous-recoverable-side REAL item. | Noted (COSMETIC; the carrier-pin `ws2_weaker_than_strict` makes it load-bearing) |
| C2-S1 | C | REAL | `ws4_cessation_relative` bundled two facts on mismatched graphs: the mortal node came from `cutAttends` (one-way) while `¬ Recoverable` is about `cutLift` (whose plain reduct is the symmetric 2-cycle), sharing only the carrier name. | Fixed (Phase D): mortality reframed on the DIRECTIONAL knowing `cutKnows` that `cutLift` encodes; both conjuncts now describe one structure. `cutAttends` retired. |
| C3-S1 | C | REAL | `verdict` has 6 inputs but `ws5_flags_justified` grounds only 4; `carrierDecided`/`carrierWoven` are meta-flags (hardcoded in the certified tuple), so "inputs are exactly the WS1–WS4 propositions" overclaims. | Fixed (Phase D): disclosed in §5. `carrierDecided = false` is grounded by the self-relativity (`ws5_carrier_relative_verdict`: both reachable ⇒ no canonical carrier forced); `carrierWoven` irrelevant (branch not reached, verdict stops at `shapeDrawn`). |
| C4-S1 | C | COSMETIC | `succDep` re-declares `causal` verbatim; `ws3_partial_order_endogenous` restates `ws4_causal_order_endogenous`. Harmless redundancy (the tick-successor / partial-order named for this series). | Noted (COSMETIC; intentional aliases, both true and non-vacuous) |
| C5-S1 | C | COSMETIC | `verdict` gates on `strictFails` as a necessary precondition. By design (WS1 the gate, not the deciding fact); audit (c) still holds (strict alone never decides). | Noted (COSMETIC; by design) |

## 5. Deviations from charter (disclosed)

- **The WS5 verdict has two META-flags beyond the four WS-propositions (Phase D, finding C3-S1).** `verdict` takes six booleans; `ws5_flags_justified` grounds four in the WS1–WS4 headline propositions (`strictFails`←WS1, `lineIsImport`←WS3, `wovenReachable`/`severedReachable`←WS4). The remaining two, `carrierDecided` and `carrierWoven`, are META-flags about whether the plain structure FORCES a canonical carrier. In the certified tuple `carrierDecided = false` (grounded by the self-relativity: `ws5_carrier_relative_verdict` shows both carriers reachable, so no canonical carrier is forced), which makes the verdict `shapeDrawn` and never enters the `carrierWoven` branch (so `carrierWoven` is irrelevant). This is disclosed rather than dressed as a WS-proposition: the honest verdict is the UNDECIDED `shapeDrawn`, self-relative, not a fiat decided outcome.
- **The mortality companion is on the directional knowing, not a separate attention map (Phase D, finding C2-S1).** The cut carrier's cessation is stated on the DIRECTIONAL knowing relation `cutKnows` that `cutLift` encodes (c0 knows c1, c1 does not know c0), so the mortal node (c0, nothing knows it) and the import (`¬ Recoverable (cutLift)`) describe ONE structure. The earlier `cutAttends` one-way Finset (whose graph differed from `cutLift`'s symmetric plain reduct) is retired.

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.6 adds none and closes none; it draws the self-relativity of persistence and of lived time sharper.

## 7. Phase log

- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.6 established as THE THREAD, the third series of Phase 2: prove strict identity fails across a tick (WS1, the trivial ground), fork the WEAK thread's recoverability (WS2, recoverable continuity vs import, Series 07), read the single lived timeline as the self's linearization import (WS3, 1D lived time self-relative, on Series 2.1's `ws4_linearization_import`), and at the knot fork the thread's continuity THREADED / SEVERED with a mortality companion (attention-relative cessation), self-relative, no fiat and no costume (the knot on the weak thread and the linearization, not on strict identity trivially failing, and not on rank being scalar). Costume gate passes at charter. Scaffold (`spec/`, `formal/`) to be created at Phase B.
- **2026-07-21 — Phase B (design).** `spec/README.md` + `spec/ws1-design.md`…`ws5-design.md` written and committed as one batch (Phase B gate: before any `formal/` file). The design fixes the three-level frame (plain ⊂ weak continuity ⊂ strict/rank identity), the two new primitives (the weak-continuity lift, built fresh; the single line as `P2S1.ws4_linearization_import`), and the genuine fork on two fresh carriers: `MCar = Fin 2` (merged, `m0 ⇄ m1`) where the continuity is `Recoverable` (WOVEN, via the general `const_first_recoverable`) with every moment attended (CONSERVATIVE), and `CCar = Bool` (cut, `c0 → c1`) where the continuity is not `Recoverable` (SEVERED, the knowing-asymmetry) with a moment nothing attends (MORTAL, attention-relative cessation). WS1 (`ws1_strict_fails`) reuses the tick carrier `TCar` (`AttentionDistinguishes` on `kC`/`kA`); WS3 (`ws3_line_is_import`) reuses `P2S1.ws4_linearization_import` transitively; the weak continuity is genuinely weaker than strict identity (`ws2_weaker_than_strict`, recoverable where strict fails). WS5 computes SHAPE-DRAWN (both carriers reachable, `carrierDecided = false`, the continuity self-relative). Renames recorded in §2. Costume gate: the verdict keys on the weak continuity (WS2/WS4) and the linearization import (WS3), never on strict identity failing (WS1, walled out); audit (c) design-level PASS, to be verified at Phase F. Next: Phase C, generate `spec/blind-seed-C.md` and spawn a blind design reviewer. Weigh: is the merged (constant-mark) recoverable continuity non-vacuous as a weak thread, or is it too thin (the reviewer's likely press on audit b)?
- **2026-07-21 — Phase C (blind design review).** `spec/blind-seed-C.md` generated (self-contained: given machinery, signatures under review, mechanical success criteria, audit checks a–e, strip test, rubric — no motivating prose). One blind reviewer (`general-purpose`) spawned, pointed at the seed ONLY; it confirmed reading no forbidden file. Verdict: ZERO SERIOUS. Findings: C1-S1 (COSMETIC, the constant-label WOVEN witness is non-vacuous — pins WOVEN to the carrier where the rank lift separates the pair — but "cont" is a lofty name), C2-S1 (REAL, mortality bundled on mismatched graphs), C3-S1 (REAL, two verdict meta-flags ungrounded/overclaimed), C4-S1 / C5-S1 (COSMETIC, intentional aliases / by-design gate). All audit clauses (a)–(e) PASS at design level; the reviewer's hard presses on (c) costume, (b) fiat, (d) scalar-rank all passed. No SERIOUS ⇒ no Phase C re-loop.
- **2026-07-21 — Phase D (design repair).** No SERIOUS to close. The two REAL findings fixed (both cheap): C2-S1 — the mortality companion reframed on the directional knowing `cutKnows` that `cutLift` encodes (mortal node and import now one structure; `cutAttends` retired); C3-S1 — the two verdict meta-flags disclosed in §5, `carrierDecided = false` grounded by `ws5_carrier_relative_verdict` (both reachable ⇒ no canonical carrier forced). COSMETIC noted, no change. `spec/ws4-design.md` and `spec/ws5-design.md` updated accordingly. Next: Phase E (build `formal/`).
- **2026-07-21 — Phase E (code).** `formal/P2S6.lean` + `P2S6/ws1..ws5.lean` + `P2S6/AxiomCheck.lean` built to the post-repair signatures, in the `P2S6` namespace, `import P2S5` (chain reached transitively). Registered in `lake/lakefile.toml` (`[[lean_lib]] P2S6`, appended to `defaultTargets`) and `scripts/gate.sh` (`check program-2/series-6 "^import (P2S5|P2S6)…"`). Mechanical checks (protocol §6): `lake build P2S6 P2S6.AxiomCheck` compiles; sorry-free; axiom-clean (standard three or fewer — the `verdict`/`decide` facts depend on no axioms); gate green (a docstring line starting "import " initially tripped the text-grep gate and was reworded); names grep clean (all hits docstring prose). The WS5 verdict COMPUTES `Outcome.shapeDrawn` from the built theorems (`ws5_verdict_eq`, by `rfl`), never hand-set: strict identity fails (WS1), the single line is an import (WS3), the weak continuity is recoverable (WOVEN, `ws2_cont_recoverable`) and an import (SEVERED, `ws2_cont_is_import`) — both reachable — and no canonical carrier is forced (`ws5_carrier_relative_verdict`), so the recoverability is self-relative. Next: Phase F, generate `spec/blind-seed-F.md` and spawn a blind code reviewer over the `formal/` sources.
