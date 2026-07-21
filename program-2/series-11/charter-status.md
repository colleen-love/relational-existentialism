# Program 2 Series 11 (2.11), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: LANDED (Phases A–G complete; Phase F returned zero SERIOUS). Current verdict: **INTERFERING** (computed at WS5 by `ws5_verdict_eq`, `rfl`, axiom-clean; never hand-set). This is the DECISIVE quantum test of Phase 3 (`charter-extension-2.md`), execution tier 2, THE PHASE: can distinction CANCEL — is there a signed amplitude, read off Series 2.8's holonomy, that produces genuine destructive interference (a combined weight strictly below its parts)? It does: the parity sign of the built holonomy takes both values (WS1), it cancels (WS2), the combined weight falls STRICTLY below the parts on the frustrated cycle and the sign is earned off the built `incr`/`hol` (WS3), and the interfering and additive poles are both reachable (WS4). The close is INTERFERING (the door to quantum theory open — distinction can subtract), honestly scoped as REAL (signed, `±1`) interference with the complex `U(1)` phase a disclosed forward-note. Build sorry-free, axiom-clean (standard three or fewer), gate-green (imports `P2S8` only), names-clean.*

---

## 0. Snapshot

- **Phase:** LANDED. `charter.md` / `charter-status.md` / `protocol.md` (Tier 1); `spec/` (Phase B: `phase-derisking.md`, `README.md`, `ws1..ws5-design.md`); `formal/` (Phase E: `P2S11.lean`, `P2S11/ws1..ws5.lean`, `AxiomCheck.lean`); blind Phase F review returned zero SERIOUS. **Precondition:** Series 2.8 landed (FRUSTRATED); the tier-1 pair 2.9/2.10 cleared — met.
- **Verdict:** **INTERFERING** (computed, `ws5_verdict_eq = Outcome.interfering` by `rfl`). Pre-registered outcomes: INTERFERING (a signed model-derived amplitude destructively cancels in a weight — the door to quantum theory, real interference — REACHED), ADDITIVE-ONLY (no combined weight ever falls below its parts — the world classical, the NOT-RECOVERED specification: add a phase — not reached), SHAPE-DRAWN, DISCONNECTED / PARTIAL. The verdict discriminates across all five (`ws5_verdict_discriminates`).
- **Build state:** built and registered (namespace `P2S11`, `srcDir ../program-2/series-11/formal`, roots `["P2S11", "P2S11.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S8|P2S11)` — imports the finished object 2.8 only, NOT the tier-1 probes 2.9/2.10). `lake build P2S11 P2S11.AxiomCheck` succeeds.
- **Axiom state:** standard three or fewer on every payoff (`propext`, `Classical.choice`, `Quot.sound`; `ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_audit_names_not_terms` depend on none). **Gate state:** green (`OK program-2/series-11 — imports resolve only to allowed roots`). **Names grep:** clean (no declared identifier is a forbidden whole word; hits are docstring prose or the `import` keyword only).
- **Open SERIOUS findings:** none. Phase F: 0 SERIOUS, 0 REAL, 1 COSMETIC (F1-S1, the accepted house `True` placeholder for audit (e) — a non-defect, enforcement delegated to the §6 grep).

## 1. The carrier — the amplitude on the imported holonomy

**S11 stands on the imported object** (`program-2/series-8`, namespace `P2S8`, reaching `P2S7` / … / `P1` transitively; the tier-1 probes 2.9/2.10 are NOT imported — their content is not reused). Its working material, reached transitively:

| Carrier piece | Where |
|---|---|
| The signed directed-attention increment `incr` (the first quantity that CANCELS: `incr x y + incr y x = 0`) | `P2S8` (imported) |
| The holonomy `hol` around a cycle, and the frustrated / gluable carriers (`hol = 3` / `hol = 0`) | `P2S8` (imported) |
| The directed knowing-asymmetry (the oriented structure, the seed of a phase) | `P2S0` / `P2S2` (transitive) |
| **The AMPLITUDE** (a sign read off the holonomy) and the **WEIGHT** (`|amp|²`), the reading of destructive interference | **built at S11 WS1–WS4 — the crux, earned from the built holonomy, de-risked on paper first** |

**Design note (from `charter-extension-2.md` §4, 2.11):** the amplitude must be EARNED from Series 2.8's built `incr`/`hol` (the no-smuggling gate, sharpest here — no bolted-on complex number); genuine destructive interference is a combined weight STRICTLY below the parts (`|a+b|² < |a|²+|b|²`), not additive bookkeeping (the costume gate); and the scope is disclosed — the amplitude is a REAL sign (`±1`), the complex `U(1)` phase a forward-note, never overclaimed. ADDITIVE-ONLY is a pre-registered honorable NOT-RECOVERED.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_amp_signed` (a `±1` amplitude read off the built holonomy, taking both signs — a real sign to cancel); `amp_values`, `amp_sq` | CLOSED | Built (Fixed): `-1` on `attTri` (odd `hol=3`), `+1` on `attStar` (even `hol=0`) |
| WS2 | `ws2_amp_cancels` (opposite amplitudes sum to zero, from Series 2.8's antisymmetry); `ws2_amp_cancels_general` (opposite parity ⇒ cancel) | CLOSED | Built (Fixed): `directAmp + loopAmp attTri = 0`; general parity criterion |
| WS3 (anti-costume core) | `ws3_destructive` (a combined weight strictly below the parts, `0 < 2`), `ws3_destructive_iff` (below-parts ↔ signs cancel), `ws3_amp_earned` (the amplitude a function of the built `incr`/`hol`, no smuggled phase) | CLOSED | Built (Fixed): strict `<` on `attTri`; earned by `rfl` |
| WS4 (the knot) | `ws4_interfering_reachable` (odd holonomy — the frustrated cycle — opposite amplitudes, weight below the parts), `ws4_additive_reachable` (even holonomy — the aligned case — weight the sum) — both genuine, no fiat | CLOSED | Built (Fixed): `attTri` `0 < 2`, `attStar` `2 ≤ 4` |
| WS5 | verdict + audit (`ws5_verdict_eq = interfering`, `ws5_verdict_discriminates`, `ws5_flags_justified`; audits (a) phase earned not smuggled, (b) fork not by fiat, (c) interference destructive not additive, (d) scope disclosed — real sign not complex phase, (e) names-not-terms) | CLOSED | Built (Fixed): verdict computed = INTERFERING, discriminates all five; audits (a)-(e) |

## 3. Audit clauses (protocol §0; UNVERIFIED until Phase F)

- (a) THE PHASE IS EARNED, NOT SMUGGLED — the amplitude is a function of the built `incr`/`hol` (definitional); no complex number or phase postulated. **VERIFIED** (`ws3_amp_earned` / `ws5_audit_earned`, all `rfl`; blind Phase F audit (a) PASS). **The clause the series lives or dies on — the sharpest no-smuggling test in the program; passed.**
- (b) THE FORK NOT BY FIAT — INTERFERING and ADDITIVE-ONLY both reachable, the verdict discriminating. **VERIFIED** (`ws5_audit_fork_genuine`, `ws5_verdict_discriminates`; both poles from the same `amp`/weight, only the attention differing; Phase F audit (b) PASS).
- (c) INTERFERENCE IS DESTRUCTIVE, NOT ADDITIVE (the costume gate) — the combined weight is STRICTLY below the parts (`0 < 2`), an inequality no classical mixture satisfies. **VERIFIED** (`ws3_destructive` strict, `ws3_destructive_iff` shows below-parts ↔ signs cancel; `partsWeight = directAmp²+loopAmp² = 2`, not a tuned constant; Phase F audit (c) PASS).
- (d) THE SCOPE IS DISCLOSED — the amplitude is a REAL sign (`±1`); no theorem claims the full complex `U(1)` phase (the disclosed forward-note, the gap to full quantum theory). **VERIFIED** (`ws5_audit_scope` / `amp_values`; no `ℂ`/`Complex` in code; Phase F audit (d) PASS).
- (e) NAMES-NOT-TERMS — no proof term named "phase," "amplitude," "interference," "quantum," "superposition," "wave," "complex," "self," "import," "God," "choice" as content; the grep is the teeth. **VERIFIED** (§6 grep clean; all 33 declared identifiers checked; `amp`≠`amplitude`, `interfering`≠`interference`; Phase F audit (e) PASS).

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

Phase B design was authored directly to the de-risked construction (the parity sign off the built holonomy, genuinely destructive on the frustrated cycle and additive on the gluable cycle, earned, no complex number — all survived the paper hunt in `spec/phase-derisking.md`). Phase E built to the design first-pass, sorry-free and axiom-clean. Phase F (blind code review) findings:

- **F1-S1 — COSMETIC — `ws5.lean` `ws5_audit_names_not_terms : True := trivial`.** The theorem name asserts a meta-property (no identifier is a forbidden term) but its body is `True`; enforcement is delegated to the §6 mechanical grep (run: PASS). The accepted house placeholder (identical to Series 2.8's `ws5_audit_names_not_terms`), openly disclosed in its docstring. Not a defect against the rubric — the signature proves exactly what it states, no `sorry`, no narrowing. **Closure: no action (accepted house pattern).**

Phase F overall: **0 SERIOUS, 0 REAL, 1 COSMETIC.** The reviewer confirmed every §3 signature genuinely proved sorry-free; the sign earned off the imported `hol`/`incr` (audit a); `ws3_destructive` a genuine strict `0 < 2` with `partsWeight` the real `directAmp²+loopAmp²` not a tuned constant (audit c); `amp` honestly `±1`-valued with no complex overclaim (audit d); the fork decided only by the differing attention (audit b); the verdict discriminating across five distinct outcomes; and the strip test surviving on every headline. Zero SERIOUS → the Phase F loop exits; Phase G has no repair. No Tier-1 landing-review finding yet (Tier 1 reviews on landing).

## 5. Deviations from the charter

None yet. Any narrowing between charter and build is disclosed here.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, the classification of the out-of-image imports. Series 2.11 adds none and closes none. If it lands SHAPE-DRAWN or ADDITIVE-ONLY, its question joins the standing catalogue of what the ontology does not yet own.

## 7. Series log

- **2026-07-21 — Series 2.11 (The Phase) chartered.** Tier 1 authored `series-11/charter.md` / `charter-status.md` / `protocol.md`: the decisive quantum test of Phase 3, execution tier 2. Knot: can distinction CANCEL — is there a signed amplitude, read off Series 2.8's holonomy, that produces genuine destructive interference (a combined weight strictly below its parts)? Reuses Series 2.8's signed increment `incr` (the first quantity that cancels) and holonomy `hol`; imports `P2S8` only (not the tier-1 probes). The amplitude must be EARNED (the sharpest no-smuggling test — no bolted-on complex number); interference must be genuinely destructive (`|a+b|² < |a|²+|b|²`), not additive bookkeeping; the scope is disclosed (a real `±1` sign, the complex `U(1)` phase a forward-note). Pre-registered: INTERFERING (the door to quantum, real interference), ADDITIVE-ONLY (the NOT-RECOVERED specification: add a phase), SHAPE-DRAWN. Namespace `P2S11`. Phase B begins now that 2.8 has landed and the tier-1 pair has cleared. Handoff to a fresh Tier-2 executor pending.
- **2026-07-21 — Series 2.11 (The Phase) LANDED: INTERFERING (scoped real/signed).** Tier-2 executor ran Phases B–G. Phase B de-risked on paper (`spec/phase-derisking.md`): the parity sign `amp n = if n%2=0 then 1 else -1` read off the built holonomy is genuinely signed (`-1` on `attTri`'s odd `hol=3`, `+1` on `attStar`'s even `hol=0`), the direct and loop paths cancel on the frustrated world, and the combined squared-modulus weight falls strictly below the parts there (`0 < 2`) while staying additive on the gluable world (`2 ≤ 4`) — earned, no complex number. Six design files committed as one batch. Phase E built `formal/P2S11/ws1..ws5` + `AxiomCheck` first-pass: sorry-free, axiom-clean (standard three or fewer), gate-green (`P2S8|P2S11`), names-clean. Registered in `lake/lakefile.toml` (`P2S11` lean_lib, appended to `defaultTargets`) and `scripts/gate.sh`. Phase F (blind code review) returned 0 SERIOUS / 0 REAL / 1 COSMETIC (F1-S1, the accepted house `True` placeholder for audit (e)); loop exits, no Phase G repair. Verdict computed INTERFERING by `ws5_verdict_eq` (`rfl`), discriminating across all five outcomes. Distinction can subtract: the signed holonomy Series 2.8 built is a genuine phase, and two paths to one outcome cancel — the door to quantum theory open, honestly scoped as real (signed) interference, the complex `U(1)` phase and the Born rule (Series 2.12) the disclosed forward-note. Awaiting Tier-1 independent landing review.
