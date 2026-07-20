# Program 2 Series 2 (2.2), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: EXIT (Phase F returned zero SERIOUS/zero REAL; build sorry-free, axiom-clean, gate-green; names/coherence greps clean). Current verdict: **TWO-FACING** (`ws5_verdict_eq`, `rfl`). All WS1-WS5 targets BUILT and VERIFIED.*

---

## 0. Snapshot

- **Phase:** EXIT. C CONVERGED (pass 1: SERIOUS C1-S1 Fixed; pass 2: ZERO SERIOUS, REAL C2p2-R1 Fixed); D applied (named `slfReader`; `Fin 5` INCOMPARABLE reaches `p ∈ slf∖oth`, `q ∈ oth∖slf`); E BUILT; F CONVERGED (blind code review: ZERO SERIOUS, ZERO REAL, three COSMETIC prose notes, one docstring softened). **Precondition met:** Series 2.1 (TWO-ZONE after Extension 1) has landed.
- **Verdict:** **TWO-FACING** — `ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing` by `rfl`, on the flags `ws5_flags_justified` earns. Confirmed by Phase F.
- **Build state:** `formal/P2S2/ws1`–`ws5` + aggregator + `AxiomCheck` BUILT sorry-free, registered in `lake/lakefile.toml` (`P2S2` added to `defaultTargets`) and `scripts/gate.sh` (`check program-2/series-2 "^import (P2S1|P2S2)…"`). Built on the **Series 2.1 ground** (`P2S1`), reaching **P2S0** and **P1** transitively.
- **Axiom state:** every payoff axiom-clean on the standard three (`propext`, `Classical.choice`, `Quot.sound`); `ws5_verdict_eq`/`ws5_verdict_discriminates`/`ws5_audit_coherence_open`/`ws5_audit_names_not_terms` depend on NO axioms.
- **Gate state:** green — S2's `formal/` imports `P2S1` and its own `P2S2.*` roots only.
- **Open SERIOUS findings:** none. Every SERIOUS finding in the run (C1-S1) closed **(Fixed)** — the named-reader target was built, never Relabeled. Phases C and F both converged to zero SERIOUS.

## 1. The carrier — the Series 2.1 ground (S2 imports S1)

**S2 stands on the Series 2.1 ground** (`program-2/series-1`, namespace `P2S1`): the tick, over Series 2.0's relating-is-finite-attending. S2 imports `P2S1` (Program 2's layered chain `P1 → S0 → S1 → S2`); S0 and P1 are reached transitively, not imported directly. The pieces S2 builds on:

| Carrier piece | Where |
|---|---|
| The tick: cycle reifies into a composite, the arrow, the clock knot | `P2S1.ws1`–`ws4` |
| The first other (the seed of the second locus): `ws1_first_other`; tower separation `rankLift` | `P2S0.ws1` (transitive) |
| The asymmetry of knowing: `knowLiftD`, `ws3_direction_not_recoverable`; `attends` / `sym` / `knows` / `attendedBy` | `P2S0.ws3` / `P2S0.ws1` (transitive) |
| Finite bound, no cardinal ceiling: `ws1_bound_is_finite_attention` | `P2S0.ws1` (transitive) |
| The seated exogenous import (the symmetry-breaker): `impLift`, `ws4_import_quantified` | `P2S0.ws4` (transitive) |
| Reader / recoverability / collapse engine: `RealFor`, `AttentionDistinguishes`, `Recoverable`, `plainOf`, `ws1_atomless_bisim` | `P1.Reader` / `P1.Core` (transitive) |

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_other_is_locus` (section + distinctness + finite attends + shared field + finite bound) | **BUILT** | discharged `decide`/`rfl` + S0 `ws1_bound_is_finite_attention` |
| WS2 (the reader knot) | `ws2_other_distinguishes`, `selfReader` (named), `ws2_other_reader_wise`, `ws2_other_non_recoverable` | **BUILT** | `RealFor` on the NAMED `selfReader` (K1, C1-S1 Fixed); `¬ Recoverable` import |
| WS3 | `faces`, `ws3_four_readings`, `faceLift`, `ws3_facing_asymmetric`, `ws3_facing_partial` | **BUILT** | direction `¬ Recoverable (faceLift)`; diagonal `ws1_no_self_total_hold` |
| WS4 (the knot) | `ws4_mutual_residue` (RESIDUE arm; ONE / TOTALIZED pre-registered) | **BUILT** | joint-unattended residue (distinct reaches, C3-S1) + `¬ Recoverable` + diagonal |
| WS5 | `Outcome`, `verdict`, `ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e | **BUILT** | verdict computes **twoFacing** by `rfl`, discriminating |

Names: the charter's provisional targets are kept verbatim as the built theorem names (`ws1_other_is_locus`, `ws2_other_reader_wise`, `ws2_other_non_recoverable`, `ws3_facing_asymmetric`, `ws3_facing_partial`, `ws4_mutual_residue`); the words "self"/"other"/"perspective" appear only underscore-embedded in identifiers (no `\bself\b`/`\bother\b`/`\bperspective\b` whole-word match) and freely in docstring prose, per protocol §6. The reader is named `selfReader`, the direction lift `faceLift`, the residue witness `bnd` (neutral). No rename needed.

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) THE OTHER IS A READER, NOT A LABEL — `ws2_other_reader_wise` proves `RealFor` for the NAMED `slfReader` (a fixed `def`, not `∃ att`, not `Many`); `attendsR oth` load-bearing across the bundle. **VERIFIED** (Phase F, audit (a) PASS; `oth` cannot be an inert tag).
- (b) THE TWONESS IS NON-RECOVERABLE — `ws2_other_non_recoverable : ¬ Recoverable (rankLift (outDest attendsR) rankR)`, a proof term via `ws4_recoverable_not_import` (the otherness an import, Series 07). **VERIFIED** (Phase F).
- (c) THE FACING IS ASYMMETRIC — `ws3_facing_asymmetric` a proof term: `¬ Recoverable (faceLift)`, the reading-DIRECTION (source-vs-target rank) genuinely distinct from WS2's source rank, read structurally by `IsBisimL`. **VERIFIED** (Phase F).
- (d) THE RESIDUE IS GENUINE, THE MUTUALITY TESTED — `ws4_mutual_residue`: the joint-unattended residue on the INCOMPARABLE reaches (both conjuncts load-bearing, F4-S1), the reading order rank-constrained, no PR1-S1 tautology; ONE/TOTALIZED arms reachable (`ws5_verdict_discriminates`); the coherence NEVER decided. **VERIFIED** (Phase F).
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names and of `converg`/`cohere`; all hits docstring prose. **VERIFIED** (Phase F; identifiers `slf`/`oth`/`p`/`q`/`bnd` neutral, `_other_` position-labels permitted).

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| C1-S1 | C | SERIOUS | `ws2_other_reader_wise`: the `FiniteAttention` is existentially bound, so the payoff collapses to a `Many`-style `∃ y, AttentionDistinguishes oth y` — the reader quantified out (K1). Audit (a). | **(Fixed)** — the reader is now a NAMED `def selfReader`; `ws2_other_reader_wise : RealFor … (selfReader hinf) oth` is proved for that fixed reader, so it cannot be tailored per witness. The other's OWN attention (`attendsR oth`, the four readings) is load-bearing (reviewer confirmed `oth` cannot be an inert tag). Target built: `ws2_other_reader_wise`. |
| C3-S1 | C | REAL | `ws4_mutual_residue` residue conjunct: with `attendsR slf = attendsR oth`, "jointly unattended" collapsed to one membership; mutuality decorative for that conjunct (the bisim is the generic collapse engine). | **(Fixed)** — the carrier is now `Fin 4`: the other's attention `{slf,oth,sh}` strictly extends the self's `{slf,oth}`, so the residue `bnd` is jointly unattended by two DISTINCT reaches (`bnd ∉ {slf,oth}` AND `bnd ∉ {slf,oth,sh}`); disclosed that the bisim is the collapse engine (Series 07), the honest import structure, the mutual content being the joint blind spot. |
| C2-S1 | C | REAL | WS5 flags are hand-set Bools with no Prop→Bool bridge; `nonCollapse`/`nonTotal` unconditionally true on this witness, so `one`/`totalized` arms are unreachable by THIS structure. | **(Addressed, disclosed)** — the accepted house pattern (S1 `ws5.lean`): `ws5_flags_justified` proves the WS1-WS4 headline Props that earn each flag; `ws5_verdict_discriminates` certifies falsifiability of the pure function; ONE / TOTALIZED are PRE-REGISTERED outcomes the same `verdict` computes for OTHER structures (charter §7), not hand-set claims about this witness. Disclosed in §5 and the WS5 docstrings. |
| C4-S1 | C | COSMETIC | `ws4_mutual_residue` (5) and `ws3_facing_partial` (2) are the universal diagonal (structure-independent). | Noted — carried as a DISCLOSED companion conjunct (not the payoff); the payoff is the residue + structural conjuncts (reviewer confirmed the tautology defect avoided). |
| C5-S1 | C | COSMETIC | `ws5_audit_coherence_open`/`ws5_audit_names_not_terms : True` are vacuous certificates. | Noted — the grep-certified pattern (S1 `ws5_audit_names_not_terms`); the properties are about identifiers, not propositions. (d-iv) `True` is the CORRECT non-decision of the coherence. |
| C6-S1 | C | COSMETIC | `ws3_facing_asymmetric`'s `¬ Recoverable (faceLift)` and WS2's `¬ Recoverable (rankLift)` share the witnessing pair `slf ~ oth`. | Noted — coherent: `faceLift`'s label is target-dependent (reading DIRECTION), genuinely distinct from `rankLift`'s source-rank; both read structurally by `IsBisimL` (reviewer confirmed distinct). |
| C2p2-R1 | C (pass 2) | REAL | `ws4_mutual_residue` conjunct (1): the C3-S1 repair made the two reaches distinct but NESTED (`attendsR slf ⊊ attendsR oth`), so `y ∉ attendsR oth ⟹ y ∉ attendsR slf` — the `slf` conjunct is redundant, the joint framing still partly decorative. | **(Fixed)** — the carrier is now `Fin 5` with INCOMPARABLE reaches: `attendsR slf = {slf,oth,p}` and `attendsR oth = {slf,oth,q}` with `p ∈ slf∖oth`, `q ∈ oth∖slf`. Now `p` is excluded from the residue ONLY by the `slf` conjunct and `q` ONLY by the `oth` conjunct, so BOTH conjuncts are load-bearing and neither implies the other — the residue `bnd` is genuinely the pair's JOINT blind spot. |
| C2p2-C1 | C (pass 2) | COSMETIC | `def selfReader` spells out "self". | **(Fixed)** — renamed `slfReader` (the `slf` abbreviation convention). |
| C2p2-C2 | C (pass 2) | COSMETIC | Blind-seed success criterion §1 had a stale example `attendsR (reifyR {slf,oth}) = {slf,oth}`. | Fixed — the seed's criterion now shows the actual minting section. |
| C2p2-S0 | C (pass 2) | — | Pass-2 blind re-review returned **ZERO SERIOUS**; C1-S1 fully resolved (named reader), C3-S1 tautology resolved; all five audit clauses PASS. | Phase C loop CONVERGED. The C2p2-R1 REAL strengthening below does not reopen C (no SERIOUS closed by it). |
| F4-S1 | F | (audit PASS) | `ws4_mutual_residue` conjunct (1): the blind code reviewer VERIFIED the joint residue is load-bearing — dropping the `slf` conjunct admits `y = p` (`p ∈ attendsR slf ∖ attendsR oth`, SHNE so the bisim horn is free) as a spurious witness; dropping the `oth` conjunct admits `y = q`. Both incomparable-reach conjuncts bite. | No action — audit (d) confirmed load-bearing, not the global diagonal. |
| F1-C1 | F | COSMETIC | `ws2.lean` docstring overclaimed that WS2's separation is done by the four-reading shape; WS2's label-separation needs only `oth` a rank-1 attending locus. | Fixed — docstring softened: WS2 needs `oth` a rank-1 locus; the four-reading shape is load-bearing across the BUNDLE (WS3/WS4). |
| F2-C1 | F | COSMETIC | `ws3_facing_partial` (2) and `ws4_mutual_residue` (5) are the structure-independent diagonal, bundled as a bare conjunction. | Noted — DISCLOSED in both docstrings as the structure-independent companion; the WS-specific content is the memberships / the residue conjunct (1). |
| F3-C1 | F | COSMETIC | The plain-bisim horns are trivially satisfiable (the collapse engine relates any two SHNE nodes). | Noted — by design (`AttentionDistinguishes` / residue put content in the negation / non-membership horn); DISCLOSED ("the collapse engine identifies all atomless relata", Series 07). |
| F-S0 | F | — | Phase F blind CODE review returned **ZERO SERIOUS, ZERO REAL**; every WS1-WS5 signature proves its stated type honestly and non-vacuously; all five audit clauses PASS; the reviewer independently confirmed no `sorry`/`admit`/`axiom`/`native_decide`, clean names/coherence greps, and the projection indices. | Phase F loop CONVERGED on the first pass (only one docstring softened, no proof change ⇒ no re-review needed). |

### Forward note for Series 2.3 (post-exit, independent read — not a defect)

**PX-1 (interpretive observation, not a review finding).** The self/other TWONESS is carried by the tower RANK (`ws2_other_distinguishes`: `oth` at `rankR = 1`, the reified self-relation; `slf` at `rankR = 0`, "the base of the constitution tower"), and its non-recoverability (`ws2_other_non_recoverable`) is the tower-rank non-recoverability. The lateral / world-of-relation structure (the two INCOMPARABLE reaches `{slf,oth,p}` and `{slf,oth,q}`, the other reading back with its own private reach) lives in WS4's joint residue but is not the basis of the twoness. So Series 2.2 built a tower rung (the reified self-relation) TURNED SIDEWAYS into a peer — genuinely two (non-recoverable, so a genuine other by Series 07, tower-origin notwithstanding, and by charter design "seed it in the first other") but NOT yet a full world of same-level, import-distinguished peers (the Series 2.1 concurrent-tick shape). **Implication for Series 2.3:** it will fork the coherence over a self and an other that are base-and-rung, which is honest but less than the world the program reaches for. If Series 2.3 wants coherence between genuine lateral peers, the move is to lift the twoness from RANK to IMPORT (self and other same-level, separated by the symmetry-breaker, not by reification height) before or as it defines `Converges₂`. This is a design consideration for Series 2.3, not a correction to Series 2.2.

## 5. Deviations from charter (disclosed)

None yet. Any narrowing of a target between charter and design, or design and build, is disclosed here at the moment it happens; an undisclosed narrowing is the PR1-S2 defect and is prohibited.

## 6. Permanent opens (inherited, untouched)

- The content of the import (the compass, the loved).
- The direction of convergence (the coherence of self and other — Series 2.3's fork, not this one's).
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.2 adds none and closes none.

## 7. Phase log

- **2026-07-20 — Phase A.** Charter committed (`charter.md`). Series 2.2 established as the OTHER: upgrade Series 2.0's first other into a genuine second attending locus, prove self and other genuinely two reader-wise, type the four readings (asymmetric and partial), and at the knot test whether mutual reading collapses, totalizes, or leaves a residue. The coherence of the two readings is deferred to Series 2.3. Scaffold created (`spec/`, `formal/`). Status initialized. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build — once Series 2.1 has landed.
- **2026-07-20 — Phase B.** Design committed as one batch: `spec/README.md` (the shared witness `RCar` = self `slf` / other `oth` / higher reader `bnd`, the imports, the discipline, the outcomes) and `spec/ws1`–`ws5-design.md`. The construction: the other is the reified reach pattern upgraded to a locus reading back (WS1); genuinely two reader-wise via a NAMED `FiniteAttention` (`RealFor`, not `Many`) and `¬ Recoverable` (WS2); the four readings typed, the facing asymmetric (the reading-direction `¬ Recoverable`, `faceLift`) and partial (the diagonal) (WS3); the mutual residue the JOINT attention subtracting the bisimilar `bnd`, NOT COLLAPSE and NOT TOTALIZED discharged, the coherence never decided (WS4); the verdict COMPUTED `twoFacing` and discriminating (WS5).
- **2026-07-20 — Phase C (design review, blind).** Pass 1: one SERIOUS (C1-S1, the reader existentially quantified out) + REAL (C3-S1, C2-S1) + cosmetics. Pass 2 (fresh seed after repair): ZERO SERIOUS, one REAL (C2p2-R1, nested reaches). Both passes confirmed reading only `blind-seed-C.md`. Loop CONVERGED.
- **2026-07-20 — Phase D (design repair).** C1-S1 **(Fixed)**: the reader named `slfReader` (a `def`, not `∃ att`). C3-S1 / C2p2-R1 **(Fixed)**: carrier `Fin 5` with INCOMPARABLE reaches (`attendsR slf = {slf,oth,p}`, `attendsR oth = {slf,oth,q}`) so both WS4 residue conjuncts bite. C2-S1 disclosed. Renamed `slfReader`, `ws5_audit_downstream_open` (clean greps).
- **2026-07-20 — Phase E (code).** `formal/P2S2/ws1`–`ws5` + aggregator + `AxiomCheck` BUILT sorry-free, axiom-clean (standard three; `ws5_verdict_eq`/`ws5_verdict_discriminates`/the two `True` audit clauses axiom-free), gate-green. Registered in `lake/lakefile.toml` (`defaultTargets`) and `scripts/gate.sh`. The WS5 verdict computes **twoFacing** by `rfl`.
- **2026-07-20 — Phase F (code review, blind) + EXIT.** Blind review of the built `formal/` sources (read `blind-seed-F.md` + the sources, no forbidden files): **ZERO SERIOUS, ZERO REAL**; every WS1-WS5 signature proves its stated type honestly and non-vacuously; audit (a)-(e) all PASS (F4-S1 confirmed the joint residue load-bearing: dropping either conjunct admits a spurious `p`/`q` witness); three COSMETIC prose notes. Phase G: one docstring softened (F1-C1, no proof change), section-6 checks re-run clean. Exit criteria met: zero SERIOUS, sorry-free, axiom-clean, gate-green, names grep prose-only, verdict computed. `summary.md` / `summary-technical.md` written. **Verdict: TWO-FACING.** Committed and pushed.
