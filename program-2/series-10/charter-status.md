# Program 2 Series 10 (2.10), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: CHARTERED (Phase A complete). No design, no build yet. Current verdict: **PENDING** (computed at WS5, never hand-set). This is the second tier-1 probe of Phase 3 (`charter-extension-2.md`) and the most consequential, THE REVERSAL: does the tick have an invertible core — a measure-preserving bijective sub-dynamics one could run backward — or is reification irreversibly one-way at every scale? The verdict is the common root of conservation (Noether needs a reversible symmetry) and of the quantum reconstruction axiom of continuous reversibility. The expected close is IRREVERSIBLE (the arrow fundamental, per Series 2.7's `ws2_tick_raises` / `ws2_residue_free`) — a NOT-RECOVERED that specifies the sharpest fork of the program; REVERSIBLE-CORE (the surprise) and SHAPE-DRAWN are pre-registered. Phase B may begin: Series 2.8 has landed. Runs IN PARALLEL with Series 2.9 (The Cone), the other tier-1 probe, which is independent of it.*

---

## 0. Snapshot

- **Phase:** CHARTERED. `charter.md` / `charter-status.md` / `protocol.md` authored by Tier 1. `spec/` and `formal/` not yet created (Phase B creates the scaffold). **Precondition:** Series 2.8 landed (FRUSTRATED) — met.
- **Verdict:** **PENDING.** Pre-registered outcomes: REVERSIBLE-CORE (a genuine measure-preserving invertible sub-dynamics — a symmetry can live, conservation and the quantum reversibility axiom reachable), IRREVERSIBLE (the tick raises the measure at every scale, no such core — the arrow fundamental, the NOT-RECOVERED specification), SHAPE-DRAWN, DISCONNECTED / PARTIAL. Expected close: IRREVERSIBLE.
- **Build state:** none yet. Registered at Phase E (namespace `P2S10`, `srcDir ../program-2/series-10/formal`, roots `["P2S10", "P2S10.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S8|P2S10)`).
- **Axiom state / gate state / names grep:** to be verified at Phase E (standard three or fewer; imports `P2S8` only, S7–S0/P1 transitive; forbidden identifiers: reversal, reversible, symmetry, conservation, energy, time, self, import, god, choice — docstring prose excepted).
- **Open SERIOUS findings:** none yet (no review has run).

## 1. The carrier — the tick's invertibility on the imported chain

**S10 stands on the imported chain** (`program-2/series-8`, namespace `P2S8`, reaching `P2S7` / … / `P1` transitively). Its working material, reached transitively:

| Carrier piece | Where |
|---|---|
| The tick and its reification section (the map under study; `attends ∘ reify = id` on patterns) | `P2S1` (transitive) |
| The reification rank (the measure the tick moves; must be PRESERVED for a genuine reversal) | `P2S7` (transitive) |
| The collapse engine (the identification that makes the tick non-injective) | `P1` / `P2S0` (transitive) |
| The diagonal (`ws2_residue_free`, self-reference as creation — the obstruction to reversal) | `P1.Reader` (transitive) |
| **The INVERTIBILITY question** (measure-preserving bijection), the section-vs-reversal distinction, the core criterion | **built at S10 WS1–WS4 — the crux, de-risked on paper first** |

**Design note (from `charter-extension-2.md` §4, 2.10):** two senses of "invertible" must be held apart — a DECODABLE section (a right-inverse that recovers the pattern but does NOT preserve the measure) versus a genuine dynamical REVERSAL (a measure-preserving bijection one could run backward). Only the higher bar is the physics. The core must be EARNED from the built tick (no inverse smuggled). This series inherits Series 2.7's exact lesson (a genuine invariance vs a look-alike). IRREVERSIBLE is a pre-registered honorable NOT-RECOVERED and the expected, most consequential close.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_tick_moves` (the tick genuinely changes the configuration and its measure — there is something to reverse) | OPEN | — |
| WS2 | `ws2_tick_not_invertible` (the full tick is not a measure-preserving bijection: it raises the rank, Series 2.7, and/or is non-injective under the collapse) | OPEN | — |
| WS3 (the crux) | `ws3_section_is_not_reversal` (the section decodes but does not preserve the measure — decodability ⊊ reversibility), `ws3_core_criterion` (a genuine core = a rank-preserving bijective tick-restriction) | OPEN | — |
| WS4 (the knot) | `ws4_reversible_core_reachable` (a measure-preserving bijective sub-dynamics, if one exists) / `ws4_irreversible_reachable` (no such core — the tick raises the measure at every scale) — both tested honestly | OPEN | — |
| WS5 | verdict + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`; audits (a) no inverse smuggled, (b) fork not by fiat, (c) decodability is not reversal, (d) measure is the built rank, (e) names-not-terms) | OPEN | — |

## 3. Audit clauses (protocol §0; UNVERIFIED until Phase F)

- (a) NO INVERSE SMUGGLED — no proof term adds an inverse the reification does not have; the core is found inside the built tick (the no-smuggling gate). UNVERIFIED. **The clause the series lives or dies on.**
- (b) THE FORK NOT BY FIAT — REVERSIBLE-CORE and IRREVERSIBLE both tested on genuine carriers, the verdict discriminating. UNVERIFIED.
- (c) DECODABILITY IS NOT REVERSAL (the costume gate) — the section is a right-inverse that does not preserve the measure; a genuine core is a measure-preserving bijection. **The exact Series 2.7 lesson.** UNVERIFIED.
- (d) THE MEASURE IS THE BUILT RANK — reversibility tested against Series 2.7's rank, not a rigged measure. UNVERIFIED.
- (e) NAMES-NOT-TERMS — no proof term named "reversal," "reversible," "symmetry," "conservation," "energy," "time," "self," "import," "God," "choice" as content; the grep is the teeth. UNVERIFIED.

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

Empty. Phase C and Phase F findings are recorded here with stable IDs, grades, and closure (Fixed / Relabeled per §0.2a). A Tier-1 landing-review finding is recorded with a `T1-` id.

## 5. Deviations from the charter

None yet. Any narrowing between charter and build is disclosed here.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, the classification of the out-of-image imports. Series 2.10 adds none and closes none. If it lands SHAPE-DRAWN or IRREVERSIBLE, its question joins the standing catalogue of what the ontology does not yet own — and IRREVERSIBLE hands the next iteration its sharpest specification.

## 7. Series log

- **2026-07-21 — Series 2.10 (The Reversal) chartered.** Tier 1 authored `series-10/charter.md` / `charter-status.md` / `protocol.md`: the second tier-1 probe of Phase 3, the most consequential. Knot: does the tick have an invertible core — a measure-preserving bijective sub-dynamics one could run backward — or is reification irreversibly one-way at every scale? The verdict is the common root of conservation (Noether) and of the quantum reversibility axiom (the reconstruction theorems). Two senses of invertible must be held apart: a decodable section (right-inverse, does not preserve the measure) vs a genuine dynamical reversal (measure-preserving bijection) — only the higher bar is the physics; the core must be earned, not smuggled. Inherits Series 2.7's lesson (genuine invariance vs look-alike). Pre-registered: REVERSIBLE-CORE (the surprise), IRREVERSIBLE (the expected NOT-RECOVERED specification), SHAPE-DRAWN. Imports `P2S8`, namespace `P2S10`. Phase B begins now that 2.8 has landed; runs in parallel with Series 2.9 (The Cone). Handoff to a fresh Tier-2 executor pending.
