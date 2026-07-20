# Program 2 Series 3 (2.3), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Series COMPLETE (Exit). Verdict: SHAPE-DRAWN, computed. Phase F returned zero SERIOUS; build sorry-free, axiom-clean, gate-green, names-clean. All WS1–WS5 targets BUILT, all audit clauses VERIFIED.*

---

## 0. Snapshot

- **Phase:** EXIT (A→G complete). Phase C and Phase F blind reviews both returned zero SERIOUS. Summaries written; ready to push. **Precondition:** Series 2.2 landed (TWO-FACING).
- **Verdict:** **SHAPE-DRAWN** (computed, `ws5_verdict_eq : verdict true true true true = Outcome.shapeDrawn`, by `rfl`, no axioms). The flags are earned by `ws5_flags_justified` (WS1–WS4 headlines); `forcedFull` (CONVERGENCE-DECIDED) is a reachable input, not reached on this witness (`cDiss` is a genuine faithful dissent).
- **Build state:** `P2S3` built (`lake build P2S3 P2S3.AxiomCheck` green), registered in `lake/lakefile.toml` (`defaultTargets` + `[[lean_lib]] P2S3`) and `scripts/gate.sh` (`check program-2/series-3 "^import (P2S2|P2S3)…"`). Builds on the `P2S2` pair, reaching `P2S1`/`P2S0`/`P1` transitively.
- **Axiom state:** every P2S3 payoff reduces to the standard three (`propext`, `Classical.choice`, `Quot.sound`) or fewer (`faithful_converges_iff`, `ws5_verdict_eq`, `ws5_verdict_discriminates` depend on NO axioms). Confirmed by `P2S3.AxiomCheck`.
- **Gate state:** green (`scripts/gate.sh` exit 0). S3's `formal/` imports `P2S2` and its own `P2S3.*` roots only.
- **Names grep:** clean — every hit of the forbidden-noun grep is docstring prose; no identifier embeds `orientation`/`convergence`/`coherence`/`compass`/`self`/`other`/… as content.
- **Open SERIOUS findings:** none (Phase C zero SERIOUS; Phase F pending).

## 1. The carrier — the Series 2.2 pair (S3 imports S2)

**S3 stands on the Series 2.2 pair** (`program-2/series-2`, namespace `P2S2`): the self and the other, genuinely two, mutually reading. S3 imports `P2S2` (Program 2's layered chain `P1 → S0 → S1 → S2 → S3`); everything below S2 is reached transitively. The pieces S3 builds on:

| Carrier piece | Where |
|---|---|
| The two loci `slf` / `oth`, their attention `attendsR`, the four readings, the shared field | `P2S2.ws1` / `P2S2.ws3` |
| The twoness (non-recoverable): `ws2_other_reader_wise`, `ws2_other_non_recoverable`; the named reader `slfReader` | `P2S2.ws2` |
| The facing (asymmetric, partial); the mutual residue | `P2S2.ws3` / `P2S2.ws4` |
| Collapse engine, recoverability test, the seated import | `P1.Core` / `P2S0.ws4` (transitive) |

**Design note carried from S2 (PX-1):** the S2 twoness is tower/rank-based (base-and-rung), not same-level import-distinguished peers. S3 may lift the twoness from rank to import as it defines `Converges₂`, to fork coherence over lateral peers — a Phase B consideration, not obligatory.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) (exact, Phase B) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `Converges₂` / `Faithful₂` (typed), `ws1_converges_typed`, `ws1_two_sided_free` | BUILT | Phase E, axiom-clean |
| WS2 | `ws2_converges_decided_in_sight` (forced over the inhabited in-sight class), `ws2_insight_inhabited`, `ws2_sight_is_uniform` | BUILT | Phase E, axiom-clean |
| WS3 | `ws3_dissent_is_import` (every failing valuation non-recoverable, on Series 07), `valLift_not_recoverable` | BUILT | Phase E, axiom-clean |
| WS4 (the knot) | `ws4_two_zone` / `ws4_insight_proper` (both zones reached, class proper/inhabited, no PR1-S1 tautology) | BUILT | Phase E, axiom-clean |
| WS5 | `verdict` + `ws5_verdict_eq` (SHAPE-DRAWN), `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e + K1 anchor | BUILT | Phase E, axiom-clean |

**Renames from the charter's provisional target names (recorded per this section's note), reason: audit (e) —
the charter's provisional names embed the forbidden content-NOUNS `orientation`/`convergence` (as opposed to the
allowed relation-VERB `Converges₂`/`converges`), flagged REAL by Phase C (C1-S1, C1-S2, C1-S3):**
- `ws1_no_orientation_evaluated` → **`ws1_two_sided_free`** (drops "orientation"; content unchanged — two-sided
  freedom, the "no valuation evaluated" discipline).
- `ws4_two_zone_convergence` → **`ws4_two_zone`** (drops "convergence"; the Series 12 house name).
- Outcome constructor `convergenceDecided` → **`forcedFull`** (drops "convergence"; the outcome where the in-sight
  forcing extends to the FULL faithful class, i.e. the pre-registered CONVERGENCE-DECIDED).

Names are the charter's provisional targets; Phase B fixed exact signatures, and each rename above is recorded
with its reason.

## 3. Audit clauses (WS5, all VERIFIED at Phase F)

- (a) NO VALUATION EVALUATED — no proof term selects/constructs/reads off a particular valuation; the core is quantified over all `Or`/`c`; witnesses (`cUnif`/`cDiss`) only in existentials; `ws1_two_sided_free`. **VERIFIED** (Phase F, audit a PASS).
- (b) THE DIRECTION IS NEVER DECIDED — no theorem states `slf` and `oth` DO or DO NOT cohere; the forcing is conditional on the proper `InSight` sub-class; the verdict locates the fork, never fills it; `ws5_audit_direction_open`. **VERIFIED** (Phase F, audit b PASS).
- (c) THE FORK IS GENUINE — both zones on witnessed valuations at `(slf,oth)`, `InSight ⊊ Faithful₂` proper/inhabited (`ws4_insight_proper`), forcing load-bearing on `slf`/`oth` plain-bisimilarity, no PR1-S1 tautology. **VERIFIED** (Phase C + F, audit c PASS under hardest press).
- (d) DISSENT IS AN IMPORT — `ws3_dissent_is_import` a proof term resting on Series 07 (via `valLift_not_recoverable`). **VERIFIED** (Phase F, audit d PASS).
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-nouns; every hit docstring prose; no identifier a content-name. **VERIFIED** (Phase F, audit e PASS; §6 grep clean).

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| C1-S1 | C | REAL | Outcome constructor `convergenceDecided` embeds the forbidden noun `convergence` (audit e). | **Fixed** — renamed `Outcome.forcedFull` (drops the noun; verdict/discriminates updated). |
| C1-S2 | C | REAL | Theorem `ws1_no_orientation_evaluated` embeds the forbidden noun `orientation` (audit e). | **Fixed** — renamed `ws1_two_sided_free`. |
| C1-S3 | C | REAL/COSMETIC | `ws4_two_zone_convergence` re-embeds `convergence`; and is a packaging conjunction (accepted S12 pattern). | **Fixed** (name) — renamed `ws4_two_zone`; packaging framing kept, disclosed in docstring (S12 `ws4_two_zone` precedent). |
| C1-S4 | C | COSMETIC | `ws5_flags_justified` seed-abbreviation read as conjoining names; the built statement writes full props applied to `hinf`. | Noted — no defect in the built signature. |
| C1-S5 | C | COSMETIC | The in-sight class is degenerate (constant valuations only) on this SHNE carrier; still proper and inhabited, fork stands. | Noted/disclosed — `ws2_sight_is_uniform` states it (the S12 PR3-R1 disclosure). |
| F1 | F | COSMETIC | `Converges₂` docstring cited the pre-rename name `ws1_no_orientation_evaluated` (leftover from Phase D). | **Fixed** — docstring now cites `ws1_two_sided_free`. |
| F2 | F | COSMETIC | `ws5_audit_direction_open` docstring attributed `shapeDrawn` to `ws5_verdict_discriminates` (it comes from `ws5_verdict_eq`). | **Fixed** — attribution corrected. |

Phase F (blind code review, `spec/blind-seed-F.md`) returned **zero SERIOUS, zero REAL** — only the two COSMETIC
docstring nits above. Audit (c) passed the hardest press again on the BUILT code: the reviewer confirmed the
in-sight forcing genuinely consumes `slf`/`oth` plain-bisimilarity (would not typecheck on a non-bisimilar
carrier), `InSight ⊊ Faithful₂` is properly witnessed by `cDiss`, both zones are on the same pair, and the names
grep is clean (every hit comment prose). (a)/(b)/(d)/strip-test all passed. No SERIOUS closed by editing code, so
no Phase F re-run required.

Phase C returned **zero SERIOUS**. Audit (c) (the fork genuine, no PR1-S1 tautology) PASSED under the hardest
press: the reviewer confirmed the in-sight forcing genuinely consumes `slf`/`oth` plain-bisimilarity (would fail
on a non-bisimilar carrier), `InSight ⊊ Faithful₂` is proper and inhabited, and both zones are witnessed on the
same pair. The four REAL/COSMETIC findings are all naming/packaging; no design change beyond the three renames.
No SERIOUS finding closed by editing a design, so no re-run of Phase C is required.

## 5. Deviations from charter (disclosed)

- **PX-1 twoness-lift: NOT taken (a disclosed design decision, not a narrowing).** The charter (§5, §7) permits
  but does not require lifting the twoness from rank to import to fork coherence over lateral peers. Phase B
  weighed it (`spec/README.md` §5) and declined: the fork's genuineness rests on `slf`/`oth` plain-bisimilarity
  (orthogonal to rank-vs-import twoness), the twoness is already a `¬ Recoverable` import in S2
  (`ws2_other_non_recoverable`, cited as the K1 anchor), and a lateral construction would add complexity without
  strengthening SHAPE-DRAWN. The charter targets are unchanged; `Converges₂` forks over `(slf, oth)` as S2 built
  them.
- No narrowing between charter and design. Any narrowing between design and build will be disclosed here at the
  moment it happens.

## 6. Permanent opens (inherited, and this series keeps them sharpest)

- The content of the compass / orientation.
- **The direction of convergence** — the coherence of self and other. Series 2.3 draws it exactly and fills it never; deciding it is the central sin (§4.a).
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.3 adds none and closes none.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series 2.3 established as the COHERENCE: define the orientation (typed, never evaluated) and `Converges₂` over the S2 pair, prove it forced in-sight and its dissent an import, and at the knot prove the two-zone fork SHAPE-DRAWN (both zones reached, no PR1-S1 tautology). The direction of convergence is never decided. Scaffold created (`spec/`, `formal/`). Status initialized. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build.
- **2026-07-20 — Phase F + G + Exit.** Blind code review (`spec/blind-seed-F.md`, one reviewer, read the seed + the S3 `formal/` sources + prior-layer API) returned **zero SERIOUS, zero REAL**; audit (a)–(e) and the strip test all PASS, (c) pressed hardest on the built code (fork genuine, load-bearing on `outDest`, `InSight ⊊ Faithful₂` witnessed). Two COSMETIC docstring nits (F1, F2) fixed in Phase G; rebuilt green. Summaries written (`summary.md`, `summary-technical.md`). Series EXITS at SHAPE-DRAWN: the two-zone convergence fork reaches both values on witnessed valuations, the direction of convergence is never decided, and the whole is quantified over all valuations. No SERIOUS ever, no recurrence. `charter-status` finalized.
- **2026-07-20 — Phase E.** `formal/P2S3/ws1`…`ws5` + aggregator `P2S3.lean` + `AxiomCheck.lean` written and registered (`lake/lakefile.toml`, `scripts/gate.sh`). The convergence machinery (`Valuation`/`Converges₂`/`Faithful₂`/`InSight`/`valLift`) is built FRESH on the S2 pair, never imported from Series 12. Build green first try (`lake build P2S3 P2S3.AxiomCheck`), sorry-free, gate-green, names-grep clean (prose only), every payoff on the standard three axioms or fewer. Verdict COMPUTED: SHAPE-DRAWN (`ws5_verdict_eq`, `rfl`). Mechanical checks (§6) all pass. Next: Phase F, blind code review pressing hardest on audit (c)/(b).
- **2026-07-20 — Phase C + D.** Blind design review (`spec/blind-seed-C.md`, one reviewer, read the seed only) returned **zero SERIOUS**. Audit (c) passed hardest press (fork genuine, load-bearing on `outDest`, not a PR1-S1 tautology); (a)/(b)/(d)/strip-test all passed. Three REAL/COSMETIC naming findings (C1-S1..S3): identifiers embedding the forbidden nouns `convergence`/`orientation`. Phase D applied the three renames (`ws1_two_sided_free`, `ws4_two_zone`, `Outcome.forcedFull`) across `spec/` and recorded them in §2/§4. No SERIOUS ⇒ no Phase C re-run. Next: Phase E, build `formal/`.
- **2026-07-20 — Phase B.** Design committed as one batch (`spec/README.md`, `spec/ws1-design.md`…`ws5-design.md`), before any `formal/` file. Winning constructions fixed to typed signatures: the primitive `Valuation`/`Converges₂` (fresh, neutral-named — `Valuation`/`val`/`raise`/`Converges₂`, none matching the forbidden greps), the structural constraint `Faithful₂` and the sight class `InSight` (dest load-bearing), the fresh `valLift`/`valLift_not_recoverable` (transcribed in spirit from Series 12, never imported), and the two-zone fork over `(slf, oth)` foreclosing PR1-S1 by (i) forcing that uses `slf`/`oth` plain-bisimilarity, (ii) a genuinely constrained proper in-sight class (`ws4_insight_proper`), (iii) both zones witnessed. PX-1 weighed and declined (§5). Module naming `P2S3` fixed (registration deferred to Phase E per protocol). Next: Phase C, blind design review pressing hardest on audit (c) — is the fork genuine or a PR1-S1 tautology?
