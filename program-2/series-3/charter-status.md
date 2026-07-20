# Program 2 Series 3 (2.3), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: B (design committed). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN.*

---

## 0. Snapshot

- **Phase:** B complete (design committed as one batch: `spec/README.md` + `spec/ws1-design.md`…`ws5-design.md`). C (design review) next. **Precondition:** Series 2.2 has landed (TWO-FACING).
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The **Series 2.2 pair** (`P2S2`, TWO-FACING) is built and registered, reaching `P2S1` / `P2S0` / `P1` transitively.
- **Axiom state:** the imported layers (P2S2, P2S1, P2S0, P1) are axiom-clean on the standard three. Series build N/A.
- **Gate state:** green upstream. S3's `formal/` will import `P2S2` only (gate `(P2S2|P2S3)`), reaching S1/S0/P1 transitively.
- **Open SERIOUS findings:** none (no review has run).

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

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `Converges₂` (typed), `ws1_no_orientation_evaluated` | OPEN | — |
| WS2 | `ws2_converges_decided_in_sight` (forced over a genuine in-sight class) | OPEN | — |
| WS3 | `ws3_dissent_is_import` (every failing orientation non-recoverable, on Series 07) | OPEN | — |
| WS4 (the knot) | `ws4_two_zone_convergence` / `ws4_shape_drawn` (both zones reached, no PR1-S1 tautology) | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO ORIENTATION EVALUATED — no proof term selects/constructs/reads off a particular orientation; the core is quantified over all. UNVERIFIED.
- (b) THE DIRECTION IS NEVER DECIDED — no theorem states the self and other DO or DO NOT cohere; the verdict draws the fork, never fills it. UNVERIFIED.
- (c) THE FORK IS GENUINE — both zones (in-sight decided, faithful dissent) reached on witnessed orientations, the faithful class structurally constrained, no PR1-S1 tautology. UNVERIFIED.
- (d) DISSENT IS AN IMPORT — `ws3_dissent_is_import` a proof term resting on Series 07. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| — | — | — | (none yet) | — |

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
- **2026-07-20 — Phase B.** Design committed as one batch (`spec/README.md`, `spec/ws1-design.md`…`ws5-design.md`), before any `formal/` file. Winning constructions fixed to typed signatures: the primitive `Valuation`/`Converges₂` (fresh, neutral-named — `Valuation`/`val`/`raise`/`Converges₂`, none matching the forbidden greps), the structural constraint `Faithful₂` and the sight class `InSight` (dest load-bearing), the fresh `valLift`/`valLift_not_recoverable` (transcribed in spirit from Series 12, never imported), and the two-zone fork over `(slf, oth)` foreclosing PR1-S1 by (i) forcing that uses `slf`/`oth` plain-bisimilarity, (ii) a genuinely constrained proper in-sight class (`ws4_insight_proper`), (iii) both zones witnessed. PX-1 weighed and declined (§5). Module naming `P2S3` fixed (registration deferred to Phase E per protocol). Next: Phase C, blind design review pressing hardest on audit (c) — is the fork genuine or a PR1-S1 tautology?
