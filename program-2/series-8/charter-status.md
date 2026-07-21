# Program 2 Series 8 (2.8), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: CHARTERED (Phase A complete). No design, no build yet. Current verdict: **PENDING** (to be computed at WS5 from the built theorems, never hand-set). This is the fifth and last series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE COMMON GOOD: across many selves, does local pairwise coherence GLUE into a global good, or can it be FRUSTRATED — every pair reconciled, yet no global section? The expected close is FRUSTRATED (the value analog of Series 2.7's global failure), with GLUABLE, SHAPE-DRAWN, PAIRWISE-ONLY, and DISCONNECTED all pre-registered and honorable. Phase B may begin: Series 2.7 has landed (MONOTONE-ONLY, accepted on independent Tier-1 review).*

---

## 0. Snapshot

- **Phase:** CHARTERED. `charter.md` / `charter-status.md` / `protocol.md` authored by Tier 1. `spec/` and `formal/` not yet created (Phase B creates the scaffold). **Precondition:** Series 2.7 landed (MONOTONE-ONLY) — met.
- **Verdict:** **PENDING.** To be computed by `ws5_verdict_eq` from the WS1–WS4 headlines. Pre-registered outcomes: FRUSTRATED (local coherence does not force a global good — a pairwise-coherent population with no global section is reachable), GLUABLE (a global good forced — the surprise), SHAPE-DRAWN (the fork drawn, undecided in-sight), PAIRWISE-ONLY (the obstruction degenerates to a single edge — the costume-detector outcome), DISCONNECTED (no non-trivial good survives), PARTIAL (degenerate). The expected close is FRUSTRATED.
- **Build state:** none yet. Registered at Phase E (namespace `P2S8`, `srcDir ../program-2/series-8/formal`, roots `["P2S8", "P2S8.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S7|P2S8)`). Any on-record attempt file (e.g. a GLUABLE attempt) MUST be a `roots` entry so `lake build` compiles it — the standalone-but-unbuilt gap noted at the 2.7 landing must not recur.
- **Axiom state:** to be verified at Phase E (standard three or fewer, via `AxiomCheck`).
- **Gate state:** to be enforced at Phase E — S8's `formal/` imports `P2S7` only (gate `(P2S7|P2S8)`); S6–S0/P1 reached transitively.
- **Names grep:** to be run at Phase E — forbidden as identifiers: good, common, value, justice, consensus, ethics, self, import, god, love, compass (hits must be docstring prose only).
- **Open SERIOUS findings:** none yet (no review has run).

## 1. The carrier — the good on the imported chain

**S8 stands on the imported chain** (`program-2/series-7`, namespace `P2S7`, reaching `P2S6` / … / `P1` transitively). Its working material is chiefly the world of peers (Series 2.4), the directed knowing-asymmetry (Series 2.0/2.2), and the single-edge coherence datum (Series 2.3), all reached transitively. Like the prior series, it builds its object — the good, the reconciliation, and the holonomy — fresh, model-derived, and this is the risky ground. The pieces S8 builds on:

| Carrier piece | Where |
|---|---|
| The world: a lateral population of same-rank peers, the metric, directed distance | `P2S4` (transitive) |
| The directed reading of one relatum by another (the knowing-asymmetry) | `P2S0` / `P2S2` (transitive) |
| The single-edge coherence datum: `Converges₂`, `Valuation`, `Faithful₂`, `InSight` (used locally, exceeded at the network) | `P2S3` (transitive) |
| The recoverability/import test and the P1 diagonal | `P1.Core` / `P1.Reader` (transitive) |
| **The GOOD** (a self-relative valuation on the population), the **RECONCILIATION** (a transition read off the directed attention), the **HOLONOMY / COCYCLE** (the obstruction to gluing) | **built at S8 WS1–WS4 — the risky ground, de-risked on paper first (`spec/frustration-derisking.md`)** |

**Design note (from `charter-extension.md` §4, 2.8):** the good is the value capstone; the risk is doubled — the good must be non-trivial and self-relative (WS1), and the obstruction must be genuinely many-body (a cocycle vanishing for two selves) AND model-derived (read off the directed attention, not bolted on — the Series 2.7 T1-S1 lesson, promoted first-class). Distinct from 2.3: 2.3 is a single edge; 2.8 is the network, a many-body phenomenon that survives even after every edge is decided coherent. PAIRWISE-ONLY (the obstruction is only a single edge) and DISCONNECTED (no good survives) are pre-registered honorable outcomes.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_good_nontrivial` (a self-relative good on a ≥3 population, non-constant, two selves valuing differently, not a relabelling of 2.4's metric or 2.3's convergence) | OPEN | — |
| WS2 | `ws2_pairwise_coherent` (every pair of selves reconciles — local coherence pervasive across the population) | OPEN | — |
| WS3 (the anti-costume core) | `ws3_two_body_trivial` (the holonomy vanishes for two selves — genuinely many-body, not 2.3 replayed), `ws3_holonomy_model_derived` (the reconciliations read off the directed attention, the cocycle over the network, not bolted on) | OPEN | — |
| WS4 (the knot) | `ws4_frustrated_reachable` (a pairwise-coherent population, non-trivial triangle holonomy, NO global section), `ws4_gluable_reachable` (a population with vanishing holonomy, a global section exists) — both genuine, no fiat | OPEN | — |
| WS5 | verdict + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, and audit clauses (a) no global good asserted, (b) fork not by fiat, (c) genuine many-body cocycle not a single edge / import-ness / bolted-on, (d) local coherence real, (e) names-not-terms) | OPEN | — |

Each series verdict is a discriminating `Bool^n → Outcome` computed at WS5, with the pre-registered alternatives reachable. The verdict is the residue of the process, not its premise.

## 3. Audit clauses (protocol §0; UNVERIFIED until Phase F)

- (a) NO GLOBAL GOOD ASSERTED — no proof term asserts a globally forced good; the good is FOR a self, glued only where the cocycle vanishes; global claimed only if forced (GLUABLE, its forcing the finding). UNVERIFIED.
- (b) THE FORK NOT BY FIAT — FRUSTRATED and GLUABLE both reachable, the good non-trivial, the verdict discriminating. UNVERIFIED.
- (c) THE OBSTRUCTION IS A GENUINE MANY-BODY COCYCLE, NOT A SINGLE EDGE AND NOT AN IMPORT, AND MODEL-DERIVED (the doubled costume gate + the T1-S1 lesson) — the holonomy vanishes for two selves (WS3) and the reconciliations are read off the directed attention, not bolted on. UNVERIFIED. **This is the clause the series lives or dies on.**
- (d) LOCAL COHERENCE IS REAL AND PERVASIVE — `ws2_pairwise_coherent`, so the frustration is surprising, not vacuous. UNVERIFIED.
- (e) NAMES-NOT-TERMS — no proof term named "good," "common," "value," "justice," "consensus," "ethics," "self," "import," "God," "love," or "compass" as content; the grep is the teeth. UNVERIFIED.

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled per §0.2a). A Tier-1 landing-review finding is recorded with a `T1-` id (as Series 2.7's T1-S1 was).

## 5. Deviations from the charter

None yet. Any narrowing between charter and build is disclosed here.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, the classification of the out-of-image imports. Series 2.8 adds none and closes none. If the capstone lands SHAPE-DRAWN, the common-good question joins them as a matter of theorem discipline — drawn exactly, filled never.

## 7. Series log

- **2026-07-21 — Series 2.8 (The Common Good) chartered.** Tier 1 authored `series-8/charter.md` / `charter-status.md` / `protocol.md`: the value capstone and the last series of Phase 2 — across many selves, does local pairwise coherence GLUE into a global good, or can it be FRUSTRATED (every pair reconciled, yet no global section)? The knot is the many-body cocycle: the holonomy of the reconciliations around a cycle of selves, a phenomenon that vanishes for two selves (so distinct from 2.3's single edge) and can be alive for three (the sheaf-gluing / Condorcet / frustration obstruction). Powered by the directed knowing-asymmetry over the network — neither import-powered (Series 07) nor a replay of the single edge (Series 2.3), so it clears the costume gate on both fronts. The Series 2.7 lesson (finding T1-S1) is carried first-class: the reconciliations must be MODEL-DERIVED (read off the directed attention), not bolted-on permutations — a frustration carried by a disconnected counter is the costume. The good is built FRESH on the world (2.4, transitive) and de-risked on paper first (`spec/frustration-derisking.md`) before any build; DISCONNECTED (no good survives) and PAIRWISE-ONLY (the obstruction is only a single edge) are pre-registered honorable outcomes. Imports `P2S7`, namespace `P2S8`. Phase B begins now that 2.7 has landed.
