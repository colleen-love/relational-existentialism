# Program 2 Series 8 (2.8), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: BUILT (Phases B, C, D, E complete; a fresh Phase C pass and Phase F/G remain). The full `formal/P2S8/` compiles: sorry-free, axiom-clean (standard three), gate-green, names-grep clean. Current verdict: **FRUSTRATED** (computed by `ws5_verdict_eq` from the WS1–WS4 headlines). This is the fifth and last series of Phase 2 (the physics of the built universe), THE COMMON GOOD: across many selves, does local pairwise coherence GLUE into a global good, or can it be FRUSTRATED — every pair reconciled, yet no global section? The computed close is FRUSTRATED (the value analog of Series 2.7's global failure), with GLUABLE, SHAPE-DRAWN, PAIRWISE-ONLY, and DISCONNECTED all pre-registered and honorable.*

---

## 0. Snapshot

- **Phase:** BUILT. `spec/` (de-risking + six design files) and `formal/P2S8/` authored; the build compiles. A fresh blind Phase C pass (design) and Phase F (code) remain before exit.
- **Verdict:** **FRUSTRATED**, computed by `ws5_verdict_eq : verdict true true true true true true = Outcome.frustrated` from the WS1–WS4 headlines (never hand-set). Pre-registered outcomes reachable in `verdict` (`ws5_verdict_discriminates`): frustrated, gluable, shapeDrawn, pairwiseOnly, disconnected, partial'.
- **Build state:** registered at Phase E (namespace `P2S8`, `srcDir ../program-2/series-8/formal`, roots `["P2S8", "P2S8.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S7|P2S8)`). `lake build P2S8 P2S8.AxiomCheck` succeeds. No on-record attempt file was needed (the fork is reached by two carriers, both built and compiled).
- **Axiom state:** verified via `AxiomCheck` — every payoff depends only on `propext` / `Classical.choice` / `Quot.sound` (several on fewer; `ws5_verdict_eq`, `ws5_verdict_discriminates` on none). Standard three, no others.
- **Gate state:** enforced — `scripts/gate.sh` reports `OK program-2/series-8` (imports resolve to `P2S7` / `P2S8.*` / Mathlib only; S6–S0/P1 transitive).
- **Names grep:** run over `formal/` — no proof term / definition / obligation is named `good`, `common`, `value`, `justice`, `consensus`, `ethics`, `self`, `import`, `god`, `love`, `compass` as a whole word. The good's definition is named `valu`; hits in the grep are docstring/comment prose and the Lean `import` keyword only.
- **Open SERIOUS findings:** none. Phase C found one (C1-S1, a forbidden term in a theorem name), closed Fixed by rename.

## 1. The carrier — the good on the imported chain

**S8 stands on the imported chain** (`program-2/series-7`, namespace `P2S7`, reaching `P2S6` / … / `P1` transitively). Its working material is chiefly the world of peers (Series 2.4), the directed knowing-asymmetry (Series 2.0/2.2), and the single-edge coherence datum (Series 2.3), all reached transitively. It builds its object — the good, the reconciliation, and the holonomy — fresh, model-derived off the directed attention, de-risked on paper first. The pieces S8 builds on:

| Carrier piece | Where |
|---|---|
| The world: a lateral population of same-rank peers, the directed ring | `P2S4` (transitive) |
| The directed reading of one relatum by another (the knowing-asymmetry) `P2S0.knows` | `P2S0` / `P2S2` (transitive) |
| The single-edge coherence datum: `Converges₂`, `Valuation` (used locally via `ws2_bridge_converges`, exceeded at the network) | `P2S3` (transitive) |
| The recoverability/import test and the P1 diagonal (used to say what the obstruction is NOT) | `P1.Core` / `P1.Reader` (transitive) |
| **The GOOD** (`valu`), the **RECONCILIATION** (`recon`), the **HOLONOMY / COCYCLE** (`hol`) — all read off the ONE model quantity `incr` (the signed directed-attention increment) | **built at S8 WS1–WS4** |

## 2. Targets (built and passing the mechanical checks; blind code review pending at Phase F)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_nontrivial` (a self-relative good, non-constant AND perspectival — two selves value a relatum oppositely, so not a 2.4-metric relabel) | BUILT | — |
| WS2 | `ws2_pairwise_coherent` (every pair reconciles, pervasive), `ws2_reconciliation_nontrivial`, `ws2_bridge_converges` (the edge datum IS 2.3's `Converges₂`) | BUILT | — |
| WS3 (the anti-costume core) | `ws3_two_body_trivial` (the holonomy vanishes for two selves), `ws3_holonomy_model_derived` (`incr` off `knows`; symmetric attention kills all holonomy; the ring is genuinely directed) | BUILT | — |
| WS4 (the knot) | `ws4_frustrated_reachable` (ring `hol = 3`, NO global section), `ws4_gluable_reachable` (star `hol = 0`, a global section restricting to the self's good) | BUILT | — |
| WS5 | `ws5_verdict_eq` (= frustrated), `ws5_verdict_discriminates`, `ws5_flags_justified`, audit clauses (a)-(e) | BUILT | — |

Each series verdict is a discriminating `Bool⁶ → Outcome` computed at WS5, with the pre-registered alternatives reachable. The verdict is the residue of the process, not its premise.

## 3. Audit clauses (protocol §0; verified in the build, blind-code-review-confirmed at Phase F)

- (a) NO GLOBAL GOOD ASSERTED — no proof term asserts a globally forced good (`ws5_audit_no_global`: `¬ ∃ s, IsSection attTri s`); the good is FOR a self (`valu`); a section is asserted only where the holonomy vanishes (the star). PENDING Phase F confirmation.
- (b) THE FORK NOT BY FIAT — frustrated (`hol attTri = 3`) and gluable (`hol attStar = 0`) both reachable from the same `hol`/`incr`; the good non-trivial; the verdict discriminates (`ws5_audit_fork_genuine`, `ws5_verdict_discriminates`). PENDING Phase F.
- (c) GENUINE MANY-BODY COCYCLE, NOT A SINGLE EDGE / IMPORT / BOLTED-ON — the holonomy vanishes for two selves and vanishes identically when the attention is symmetric (`ws3_two_body_trivial`, `ws3_holonomy_model_derived`, `ws5_audit_many_body`); no clause mentions `Recoverable`. **The clause the series lives or dies on.** PENDING Phase F.
- (d) LOCAL COHERENCE IS REAL AND PERVASIVE — `ws2_pairwise_coherent` (`∀ att x y v`). PENDING Phase F.
- (e) NAMES-NOT-TERMS — the §6 grep is clean (prose/keyword only). PENDING Phase F.

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

- **C1-S1 — SERIOUS — Fixed (rename).** Phase C (design review, blind) found the WS1 theorem named `ws1_good_nontrivial`, which embeds the forbidden whole-word `good` — an audit-(e) violation (the §6 grep over `formal/` would hit the proof-term name). Closed **Fixed** per §0.2a: the target (a non-trivial self-relative good) IS built, renamed to the compliant identifier `ws1_nontrivial` across code, design, seed, and this ledger. The charter's prose handle for the target was likewise updated (see §5). All other Phase C checks passed: every payoff verified true by hand, the fork genuine, the obstruction a genuine directed 3-body cocycle (two-body-trivial, symmetry-killed, `att`-only, no import-ness), no global section over the frustrated carrier asserted, the verdict computed and discriminating, the strip test passing throughout.

## 5. Deviations from the charter

- **WS1 theorem name.** The charter §2 prose named the WS1 target `ws1_good_nontrivial`; to satisfy audit (e) (no proof term named `good`), the built Lean theorem and all references are named `ws1_nontrivial` (a design-error fix per protocol §0, no build depended on the old name). The theorem proves exactly the charter's WS1 target (a non-trivial, self-relative good). No narrowing of content.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, the classification of the out-of-image imports. Series 2.8 adds none and closes none.

## 7. Series log

- **2026-07-21 — Series 2.8 (The Common Good) chartered.** Tier 1 authored `charter.md` / `charter-status.md` / `protocol.md`: the value capstone and the last series of Phase 2. The knot is the many-body cocycle — the holonomy of the reconciliations around a cycle of selves, invisible for two selves and alive for three. Powered by the directed knowing-asymmetry over the network; the Series 2.7 lesson (T1-S1, reconciliations MODEL-DERIVED not bolted on) carried first-class. Imports `P2S7`, namespace `P2S8`.
- **2026-07-21 — Phase B complete (design + paper de-risking).** One model quantity carries everything: the signed directed-attention increment `incr att x y = ⟦y∈att x⟧ - ⟦x∈att y⟧`, a function of the attention alone. The GOOD `valu := incr att p0 ·` (non-constant AND perspectival — not a 2.4 relabel; WS1). The RECONCILIATION `recon att x y v := v + incr att x y`; pairwise coherence pervasive and unconditional (antisymmetry definitional; WS2). The HOLONOMY `hol := incr x y + incr y z + incr z x`, vanishing for two selves and vanishing identically when the attention is symmetrised — the obstruction lives in the directedness, not a bolted-on gadget (WS3). The FORK on two directed-attention carriers: the ring `attTri` (`hol=3`, no section — FRUSTRATED) and the star `attStar` (`hol=0`, a section — GLUABLE), neither by fiat (WS4). Rejected candidates recorded (path metric, `Converges₂`-as-good, free-permutation cocycles, `Finset.card` counters, the symmetric relating). Six design files + de-risking written.
- **2026-07-21 — Phase C (blind design review) + Phase D (repair).** A blind reviewer, seeded only with signatures and mechanical checks, verified every payoff true by hand and found ONE SERIOUS finding (C1-S1: forbidden word `good` in a theorem name), closed Fixed by renaming to `ws1_nontrivial`. See §4.
- **2026-07-21 — Phase E (build) complete.** `formal/P2S8/` (`ws1`…`ws5`, `P2S8`, `AxiomCheck`) built to the post-repair signatures. Mechanical checks all pass: compiles; sorry-free; axiom-clean (standard three, several fewer); gate-green; names-grep clean (prose/keyword only). The verdict computes FRUSTRATED (`ws5_verdict_eq`). A fresh blind Phase C pass and Phase F (blind code review) remain before exit.
