# Program 2 Series 2 (2.2), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: D/E (design repaired after Phase C; `formal/` built and validated; Phase C re-review in progress). Current verdict: twoFacing (computed by `ws5_verdict_eq`, pending Phase F confirmation). All WS1-WS5 targets BUILT.*

---

## 0. Snapshot

- **Phase:** C complete (pass 1: one SERIOUS C1-S1, closed by repair); D applied (named reader, `Fin 4` distinct reaches); `formal/` BUILT and validated (Phase E work done early to validate the design); Phase C pass-2 re-review in progress (SERIOUS closed by editing the design ⇒ re-seed and re-review per protocol §2 loop). **Precondition met:** Series 2.1 (TWO-ZONE after Extension 1) has landed.
- **Verdict:** **twoFacing** — `ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing` by `rfl`, on the flags `ws5_flags_justified` earns. Pending Phase F.
- **Build state:** `formal/P2S2/ws1`–`ws5` + aggregator + `AxiomCheck` BUILT sorry-free, registered in `lake/lakefile.toml` (`P2S2` added to `defaultTargets`) and `scripts/gate.sh` (`check program-2/series-2 "^import (P2S1|P2S2)…"`). Built on the **Series 2.1 ground** (`P2S1`), reaching **P2S0** and **P1** transitively.
- **Axiom state:** every payoff axiom-clean on the standard three (`propext`, `Classical.choice`, `Quot.sound`); `ws5_verdict_eq`/`ws5_verdict_discriminates`/`ws5_audit_coherence_open`/`ws5_audit_names_not_terms` depend on NO axioms.
- **Gate state:** green — S2's `formal/` imports `P2S1` and its own `P2S2.*` roots only.
- **Open SERIOUS findings:** none (C1-S1 closed **(Fixed)**; pass-2 re-review pending).

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

- (a) THE OTHER IS A READER, NOT A LABEL — `ws2_other_reader_wise` names a genuine reader, its `attends` load-bearing, not the Series 11 Bookkeeping tag. UNVERIFIED.
- (b) THE TWONESS IS NON-RECOVERABLE — `ws2_other_non_recoverable` a proof term (the otherness an import, Series 07). UNVERIFIED.
- (c) THE FACING IS ASYMMETRIC — `ws3_facing_asymmetric` a proof term. UNVERIFIED.
- (d) THE RESIDUE IS GENUINE, THE MUTUALITY TESTED — `ws4_mutual_residue` proved under mutual reading on a witnessed pair, both collapse and residue arms reachable, no PR1-S1 tautology. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

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
- **2026-07-20 — Phase B.** Design committed as one batch: `spec/README.md` (the shared `Fin 3` witness `RCar` = self `slf` / other `oth` / higher reader `bnd`, the imports, the discipline, the outcomes) and `spec/ws1`–`ws5-design.md`. The construction: the other `oth = reifyR {slf,oth}` is the reified shared-field pattern upgraded to a locus reading back (WS1); genuinely two reader-wise via a NAMED `FiniteAttention` (`RealFor`, not `Many`) and `¬ Recoverable` (WS2); the four readings typed, the facing asymmetric (the reading-direction `¬ Recoverable`, `faceLift`) and partial (the diagonal) (WS3); the mutual residue the JOINT attention subtracting the bisimilar `bnd` (load-bearing on mutuality, not the bare diagonal), NOT COLLAPSE and NOT TOTALIZED discharged, the coherence never decided (WS4); the verdict COMPUTED `twoFacing` and discriminating (WS5). Next: Phase C, generate `spec/blind-seed-C.md` and delegate a blind design review.
