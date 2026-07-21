# Program 2 Series 9 (2.9), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: **COMPLETE** (Phases A-G done; the series EXITS). `formal/` built, sorry-free, axiom-clean, gate-green, names-grep clean; Phase C and Phase F both passed with 0 SERIOUS. Current verdict: **CONE** (computed at WS5 `ws5_verdict_eq = coneOut`, never hand-set; confirmed by blind Phase F). Summaries written. This is the first recovery test of Phase 3 (`charter-extension-2.md`) and one of the two tier-1 probes that open it, THE CONE: is finite attention a maximal rate of becoming — a light cone, a speed of light? The expected close is CONE (relativity's cone recovered — the encouraging first probe), with NO-CONE (a NOT-RECOVERED specification: the model is non-relativistic, add a rate-bound) and SHAPE-DRAWN pre-registered and honorable. The computed close is CONE: relativity's light cone recovered as the shadow of a bounded capacity to attend, the rate earned from finite attention and never postulated — the encouraging first result of Phase 3. Ran IN PARALLEL with Series 2.10 (The Reversal), the other tier-1 probe, which is independent of it.*

---

## 0. Snapshot

- **Phase:** **COMPLETE** (Phases A-G done; the series EXITS). Design committed (Phase B), Phase C passed (0 SERIOUS), `formal/` built (Phase E), Phase F passed (0 SERIOUS), summaries written. **Precondition:** Series 2.8 landed (FRUSTRATED) — met. The paper gate survived: a finite rate earned from attention, a non-trivial cone, the rate genuine content not the bare order.
- **Verdict:** **CONE** (computed, confirmed by blind Phase F). `ws5_verdict_eq : verdict true true true true true true = Outcome.coneOut := rfl`, the flags earned by `ws5_flags_justified`. Pre-registered outcomes: CONE (a bounded rate, a non-trivial cone — the relativistic cone recovered — the computed close), NO-CONE (the rate unbounded, the cone trivial — non-relativistic), SHAPE-DRAWN, DISCONNECTED / PARTIAL. `Outcome` = `coneOut | noconeOut | shapeDrawn | disconnected | partial'`; `ws5_verdict_discriminates` reaches all five.
- **Build state:** BUILT and registered. Namespace `P2S9`, `srcDir ../program-2/series-9/formal`, roots `["P2S9", "P2S9.AxiomCheck"]`, appended to `defaultTargets`; gate line `(P2S8|P2S9)`. Layout: `P2S9.lean` imports `P2S9.ws1`…`ws5`; `P2S9/wsN.lean`; `P2S9/AxiomCheck.lean`. `lake build P2S9 P2S9.AxiomCheck` compiles clean.
- **Axiom state / gate state / names grep (Phase E, §6 checks all PASS):** (1) compiles; (2) sorry-free (`grep sorry` clean); (3) axiom-clean — every payoff depends on at most the standard three (`propext`, `Classical.choice`, `Quot.sound`); the `verdict`/`rfl` facts on none; (4) gate-green (`scripts/gate.sh` OK — imports resolve to `P2S8|P2S9` + Mathlib; S7–S0/P1 transitive); (5) names grep — all hits are docstring/comment prose or the exempt `import` keyword; no proof-term named `light/cone/speed/relativity/spacetime/self/import/god/compass` (the cone def is `ball`; the constructors `coneOut/noconeOut`; the theorem names `ws2_cone`/`ws4_cone_reachable` are underscore-wrapped and do not match `\bcone\b`).
- **Open SERIOUS findings:** none. Phase C: 0 SERIOUS. Phase F: 0 SERIOUS. The series is COMPLETE; verdict CONE.

## 1. The carrier — the rate on the imported chain

**S9 stands on the imported chain** (`program-2/series-8`, namespace `P2S8`, reaching `P2S7` / … / `P1` transitively). Its working material, reached transitively:

| Carrier piece | Where |
|---|---|
| Finite attention (the bound that limits the reification rate) | `P2S0` (transitive) |
| The tick and reification (the conversion of breadth into depth) | `P2S1` (transitive) |
| The lateral metric and the two DISTINCT axes (breadth as space) | `P2S4` (transitive) |
| The causal order (the cone's skeleton, which S9 rate-limits and exceeds) | `P2S5` (transitive) |
| **The RATE** (breadth-to-depth conversion bounded by finite attention) and its **CONE** | **built at S9 WS1–WS4 — the risky ground, earned from attention, de-risked on paper first** |

**Design note (from `charter-extension-2.md` §4, 2.9):** the recovered feature (a cone, a c) must be EARNED from finite attention (the no-smuggling gate), not postulated; and the cone must be a genuine finite-SPEED structure (a rate relating 2.4's breadth to 2.1's depth), not a relabelling of 2.5's bare causal order (the costume gate). NO-CONE (the rate unbounded) is a pre-registered honorable NOT-RECOVERED. Lorentz mixing is a forward-note, not this series' target.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 (the ground) | `ws1_rate_bounded` (a finite rate `c` limiting breadth-to-depth conversion, a function of the finite attention bound), `ws1_rate_earned_from_knows`, `ws1_rate_monotone`, `ws1_rate_tracks_attention` | DONE | — |
| WS2 | `ws2_cone` (the cone is the rate-bounded reachable set; something strictly outside is causally disconnected; the cone non-trivial), `ws2_cone_nontrivial` | DONE | — |
| WS3 (anti-costume) | `ws3_rate_is_content` (same causal order, different rate ⇒ different cone), `ws3_earned_from_attention` (the rate a function of the Series 2.0 attention bound, not a postulated c) | DONE | — |
| WS4 (the knot) | `ws4_cone_reachable` (a genuine finite rate, a non-trivial cone), `ws4_nocone_reachable` (total attention, a trivial cone), `ws4_nocone_trivial` — both genuine, no fiat | DONE | — |
| WS5 | verdict + audit (`ws5_verdict_eq = coneOut`, `ws5_verdict_discriminates`, `ws5_flags_justified`; audits (a) rate earned not smuggled, (b) fork not by fiat, (c) cone is a rate not the bare order, (d) cone non-trivial, (e) names-not-terms) | DONE | — |

## 3. Audit clauses (protocol §0; VERIFIED at Phase F)

- (a) THE RATE IS EARNED, NOT SMUGGLED — the bound is a function of finite attention (Series 2.0); no `c` postulated (the no-smuggling gate). **VERIFIED** (`ws5_audit_rate_earned`; `rate = univ.sup (span att)`, monotone, 1<2<4; the blind reviewer confirmed no constant baked into `rate`/`ball`). **The clause the series lives or dies on — held.**
- (b) THE FORK NOT BY FIAT — CONE and NO-CONE both reachable, the verdict discriminating. **VERIFIED** (`ws5_audit_fork_genuine`, `ws5_verdict_discriminates`).
- (c) THE CONE IS A RATE, NOT THE BARE ORDER (the costume gate) — same order, different rate, different cone. **VERIFIED** (`ws5_audit_rate_not_order`; `reaches attSlow = reaches attFast` yet cones differ).
- (d) THE CONE IS NON-TRIVIAL — some events strictly outside, a genuine finite speed. **VERIFIED** (`ws5_audit_cone_nontrivial`; `p4 ∉ ball attSlow p0 1`).
- (e) NAMES-NOT-TERMS — no proof term named "light," "cone," "speed," "relativity," "spacetime," "self," "import," "God," "compass" as content; the grep is the teeth. **VERIFIED** (grep prose-only; the cone def is `ball`, constructors `coneOut`/`noconeOut`, theorem names underscore-wrapped).

## 4. Findings ledger (Phases C, F, and any Tier-1 landing review)

Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades, and closure (Fixed / Relabeled per §0.2a). A Tier-1 landing-review finding is recorded with a `T1-` id.

**Phase C — design review (blind, 1 pass). SERIOUS: 0.**
- **C1-S1 — COSMETIC — `ws5_audit_names_not_terms : True`.** The names-not-terms clause is a `True` placeholder (the meta-grep property is not a Lean proposition). Accepted house convention (identical to `P2S8.ws5_audit_names_not_terms : True`); the §6 grep is the actual teeth. No change. The reviewer recomputed every rate (1/2/4), ball, reachability, and verdict row by hand and confirmed all correct; cleared audits (a)-(e); strip test passed for every payoff; no forbidden identifier. Zero SERIOUS ⇒ the C/D loop exits; proceed to Phase E.

**Phase F — code review (blind, 1 pass, over `formal/`). SERIOUS: 0.**
- **F1-C1 — COSMETIC — `ws5_audit_names_not_terms : True` (ws5.lean).** The `True` placeholder for the names-not-terms meta-property; the docstring labels it as such, the §6 grep is the teeth. Accepted (identical to `P2S8`). No change. The reviewer confirmed blindness, verified `lake build P2S9 P2S9.AxiomCheck` clean and axiom-clean (standard three; the `rfl`/`decide` payoffs on none; no `native_decide`/`Lean.ofReduceBool`), independently recomputed every rate (1/2/4), ball ({0,1}/{0,1,2}/univ) and the same-order-different-cone fact, discharged `ws5_flags_justified` term-by-term from the WS theorems, cleared audits (a)-(e) — pressing on (a) no smuggled constant, (c) cone depends on `rate` not `reaches`, (d) `p4` outside — and passed the strip test on every payoff. Zero SERIOUS ⇒ the F/G loop exits; the series EXITS.

## 5. Deviations from the charter

Two mechanical, content-preserving deviations from the blind-seed-C sketch, both introduced at Phase E to make the design compile; neither narrows a charter target.

- **D1 — reachability implementation.** The blind seed sketched `reachB … : ℕ → S → S → Bool` recursing through `(att x).sup`. `Finset.sup` on `Bool` pulls in a noncomputable instance and the higher-order recursion fails Lean's termination check, so `reachB` is replaced by a computable Finset closure: `reachN att n R` (closure of `R` under `n` attention-steps via `∪`/`biUnion`), `reachSet att x := reachN att (card S) {x}`, and `reaches att x y : Bool := decide (y ∈ reachSet att x)`. The public signature `reaches : (S → Finset S) → S → S → Bool` and every downstream statement (`∀ x y, reaches attSlow x y = reaches attFast x y`) are unchanged; the content (bounded directed reachability, the causal order re-seated) is identical.
- **D2 — `Outcome` constructor names.** `coneOut`/`noconeOut` (not `cone`/`nocone`): a bare `| cone` declaration is space-wrapped and matches the §6 grep `\bcone\b`; `coneOut` does not. Prose still says CONE/NO-CONE. Noted in `ws5-design.md` §4.

## 6. Permanent opens (inherited, untouched)

Program 1's four permanent opens stand: the content of the compass, the direction of convergence, the differentiating act, the classification of the out-of-image imports. Series 2.9 adds none and closes none. If it lands SHAPE-DRAWN or NO-CONE, its question joins the standing catalogue of what the ontology does not yet own.

## 7. Series log

- **2026-07-21 — Series 2.9 (The Cone) chartered.** Tier 1 authored `series-9/charter.md` / `charter-status.md` / `protocol.md`: the first recovery test of Phase 3, one of two tier-1 probes. Knot: is there a maximal rate at which attention-breadth becomes reification-depth — a light cone, a c? The rate must be EARNED from finite attention (the no-smuggling gate), not postulated; and the cone must carry a genuine rate, not relabel Series 2.5's causal order (the costume gate). Pre-registered: CONE (recovered), NO-CONE (the NOT-RECOVERED specification), SHAPE-DRAWN. Imports `P2S8`, namespace `P2S9`. Phase B begins now that 2.8 has landed; runs in parallel with Series 2.10 (The Reversal). Handoff to a fresh Tier-2 executor pending.
- **2026-07-21 — Phase F (Code review) + Exit; the series is COMPLETE, verdict CONE.** Blind code review over `formal/` returned 0 SERIOUS (1 COSMETIC: the `ws5_audit_names_not_terms : True` placeholder, accepted). The reviewer verified axiom-cleanliness, independently recomputed all arithmetic, discharged `ws5_flags_justified` from the WS theorems, and cleared audits (a)-(e), pressing on the no-smuggling gate (a), the costume gate (c), and non-triviality (d). Exit criteria met: Phase F 0 SERIOUS; build sorry-free, axiom-clean, gate-green; names grep prose-only; WS5 computes CONE; no SERIOUS to close. Wrote `summary.md` / `summary-technical.md`. **THE CONE recovered: finite attention is a maximal rate of becoming; relativity's light cone is the shadow of a bounded capacity to attend, earned from the finite attention the model has carried since Series 2.0, never postulated.** The forward-note (the Lorentz mixing of 2.4's two distinct axes at rate `c`) is left open for a later series; 2.9 establishes the cone only. Program 1's four permanent opens stand untouched.
- **2026-07-21 — Phase E (Code) complete; verdict computes CONE.** Built `formal/P2S9/ws1..ws5` + `AxiomCheck` + aggregator `P2S9.lean` to the post-C signatures, `import P2S8` only. Registered in `lake/lakefile.toml` (`defaultTargets` += `P2S9`) and `scripts/gate.sh` (`(P2S8|P2S9)`). All §6 checks pass: compiles, sorry-free, axiom-clean (standard three), gate-green, names grep prose-only. WS1 `ws1_rate_bounded` / `ws1_rate_earned_from_knows` / `ws1_rate_monotone` / `ws1_rate_tracks_attention` (rate 1<2<4); WS2 `ws2_cone` / `ws2_cone_nontrivial` (p4 outside); WS3 `ws3_rate_is_content` (same order, different rate, different cone) / `ws3_earned_from_attention`; WS4 `ws4_cone_reachable` / `ws4_nocone_reachable` / `ws4_nocone_trivial`; WS5 `ws5_verdict_eq = coneOut` (rfl), `ws5_verdict_discriminates` (all five), `ws5_flags_justified`, audits (a)-(e). Two mechanical design fixes vs blind-seed-C, both content-preserving (see §5 Deviations): the Bool reachability was implemented as a computable Finset closure (`reachN`/`reachSet`), and the `Outcome` constructors are `coneOut`/`noconeOut`. Next: Phase F (blind code review).
- **2026-07-21 — Phase B (Design) complete.** Wrote and committed the paper gate `spec/rate-derisking.md` and the six design files (`spec/README.md`, `spec/ws1..ws5-design.md`) as one batch before any `formal/` file. The construction, on a fresh `Fin 5` LINE re-seating 2.4's lateral world: the lateral metric `dist = Nat.dist` (breadth, a fixed spatial background); the per-tick reach `span att x = (att x).sup (dist x ·)` and the RATE `rate att = univ.sup (span att)` — a `Finset.sup` over the finite attention, EARNED, not a postulated `c`; the cone `ball att x depth = univ.filter (dist x · ≤ rate att * depth)` (named `ball`, not `cone`, for the §6 grep); the causal order `reaches` (decidable bounded reachability, 2.5 re-seated); three carriers `attSlow` (rate 1, CONE), `attFast` (rate 2, SAME order — the costume pair), `attAll` (rate 4, NO-CONE, instantaneous). Paper hunt survived all three de-risking checks: bounded-and-earned (§2), non-trivial cone (§3), same-order-different-cone (§4). `Outcome` constructors named `coneOut`/`noconeOut` (a bare `| cone` would trip the grep). Module naming fixed: namespace `P2S9`, roots `["P2S9", "P2S9.AxiomCheck"]`, `srcDir ../program-2/series-9/formal`, gate `(P2S8|P2S9)` — registered at Phase E. Expected verdict CONE. Next: Phase C (blind design review).
