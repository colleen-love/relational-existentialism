# Program 2 Series 6 (2.6), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: A (charter written). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN. This is the third series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE THREAD: the persistence of the self, and the single lived timeline.*

---

## 0. Snapshot

- **Phase:** A complete (charter committed). B (design) not started. **Precondition:** Series 2.5 must have landed before Phase B begins (it has: ACYCLIC, including Charter Extension 1).
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The imported chain (`P2S5`, `P2S4`, `P2S3`, `P2S2`, `P2S1`, `P2S0`, `P1`) is built and registered, reaching all lower layers transitively.
- **Axiom state:** the imported layers are axiom-clean on the standard three. Series build N/A.
- **Gate state:** green upstream. S6's `formal/` will import `P2S5` only (gate `(P2S5|P2S6)`), reaching S4/S3/S2/S1/S0/P1 transitively.
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

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_strict_identity_fails` (the self post-tick is not plain-bisimilar to pre-tick; the trivial ground), the tick-successor relation | OPEN | — |
| WS2 | `ws2_thread_recoverable` / `ws2_thread_is_import` (is a weak continuity recoverable, or an import — the fork's substance, Series 07) | OPEN | — |
| WS3 | `ws3_timeline_is_linearization_import` (the single line the self's linearization import, 1D lived time self-relative, on Series 2.1) | OPEN | — |
| WS4 (the knot) | the thread fork (THREADED / SEVERED), both reachable, self-relative continuity, `ws4_attention_relative_cessation` (the mortality companion), no fiat, no costume | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here (note the §6 forbidden-word grep: "self"/"thread"/"persistence"/"life"/"time" etc. may not appear in identifiers).

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
| — | — | — | (none yet) | — |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing between charter and design, or design and build, is disclosed here at the moment it happens.

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.6 adds none and closes none; it draws the self-relativity of persistence and of lived time sharper.

## 7. Phase log

- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.6 established as THE THREAD, the third series of Phase 2: prove strict identity fails across a tick (WS1, the trivial ground), fork the WEAK thread's recoverability (WS2, recoverable continuity vs import, Series 07), read the single lived timeline as the self's linearization import (WS3, 1D lived time self-relative, on Series 2.1's `ws4_linearization_import`), and at the knot fork the thread's continuity THREADED / SEVERED with a mortality companion (attention-relative cessation), self-relative, no fiat and no costume (the knot on the weak thread and the linearization, not on strict identity trivially failing, and not on rank being scalar). Costume gate passes at charter. Scaffold (`spec/`, `formal/`) to be created at Phase B. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build. Weigh the witness: a tick-successor carrier where a weak thread is recoverable, and a second carrier where it is severed (self-relative continuity), and the reading of Series 2.1's linearization import as the single line.
