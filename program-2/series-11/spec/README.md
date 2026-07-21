# Series 2.11 design index (`spec/README.md`) — THE PHASE

**The design layer for the decisive quantum test. Read `phase-derisking.md` first (the paper gate: a signed sign read off Series 2.8's built holonomy, genuinely destructive on the frustrated cycle and additive on the gluable cycle, earned, no complex number — all survived). This README fixes the imported object, the one added primitive, the discipline, the cross-workstream triage, the outcomes, and the names-in-prose rule. The `wsNN-design.md` files give per-workstream signatures. All files (`phase-derisking.md`, `README.md`, `ws1..ws5-design.md`) are committed as one batch before any `formal/` file exists (the Phase B gate).**

## 1. The imported object (quantified, never named as content)

Series 2.11 imports `P2S8` only; `P2S7 / … / P2S0 / P1` are reached transitively. It does NOT import the tier-1 probes `P2S9`/`P2S10` (their content is not reused). Working material, all built and axiom-checked in Series 2.8:

- **The signed increment** `P2S8.incr att x y := ⟦y∈att x⟧ - ⟦x∈att y⟧ : ℤ`, the first quantity that CANCELS (`incr x y + incr y x = 0`, `ws3_two_body_trivial.1`). Values in `{-1,0,+1}`.
- **The holonomy** `P2S8.hol att x y z := incr att x y + incr att y z + incr att z x : ℤ`.
- **The carriers and holonomies:** `P2S8.attTri` (frustrated ring, `hol attTri p0 p1 p2 = 3`, ODD, `ws4_frustrated_reachable.1`); `P2S8.attStar` (gluable star, `hol attStar p0 p1 p2 = 0`, EVEN, `ws4_gluable_reachable.1`); the population `P2S8.S = Fin 3`, `p0 p1 p2`.
- **The directed knowing-asymmetry** (`P2S0`/`P2S2`, transitive) — the oriented, antisymmetric structure that is the seed of a sign; a symmetric relating carries no holonomy (`ws3_holonomy_model_derived.2.1`), hence no sign to cancel.

## 2. The one added primitive (built FRESH at S11, earned off the built holonomy; `formal/P2S11/ws1..ws5`)

Series 2.11 adds exactly one thing — a parity SIGN read off the holonomy — and its squared modulus (the WEIGHT), together with the reading of destructive interference as a combined weight below its parts.

```
-- THE SIGN read off the holonomy: the parity sign of an integer. A ±1-valued function; no complex number.
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1

-- The two paths to one outcome (the basepoint p0), and their signs:
def directAmp : ℤ := amp 0                                   -- the direct (do-nothing) path, sign +1
def loopAmp (att : S → Finset S) : ℤ := amp (hol att p0 p1 p2) -- the around-the-ring path, sign amp(hol)

-- THE WEIGHT (squared modulus): the two paths combined vs the two paths weighed separately.
def combinedWeight (att : S → Finset S) : ℤ := (directAmp + loopAmp att) ^ 2
def partsWeight    (att : S → Finset S) : ℤ := directAmp ^ 2 + (loopAmp att) ^ 2
```

Everything downstream is a ℤ-arithmetic fact on a finite carrier: `decide` / `omega` / `norm_num`-checkable. `amp` is a function of the built `hol` alone (no free parameter, no complex number); `hol` and `incr` are Series 2.8's, imported. The sign is `±1`-valued (a real sign, not a complex `U(1)` phase — the scope, disclosed).

## 3. The discipline (the no-smuggling gate + the costume gate, first-class, sharpest in the program)

- **The phase is EARNED, no complex number smuggled (audit a, the phase sin, sharpest here).** `amp` is a `±1`-valued function of the built `hol`; the integer it reads is `hol att x y z`, itself the built signed-`knows` sum. No complex number, no postulated phase, no free parameter. `ws3_amp_earned` states `loopAmp` unfolds definitionally to `amp (hol …)`, `hol` to the `incr`-sum, `incr` to the signed `knows` difference.
- **Interference is DESTRUCTIVE, not additive (audit c, the costume gate).** Genuine interference is a combined weight STRICTLY below the parts (`combinedWeight attTri = 0 < 2 = partsWeight attTri`), an inequality no classical mixture satisfies (classically weights add, `combined ≥ parts`). The signed sum being zero (WS2) is necessary but not sufficient; the WEIGHT falling below the parts (WS3) is the whole content. `ws3_destructive_iff` makes it a theorem: destructive IFF the signs cancel IFF the loop holonomy is odd.
- **The scope is disclosed, the complex phase not overclaimed (audit d).** `amp` is a REAL sign (`∀ n, amp n = 1 ∨ amp n = -1`, `ws5_audit_scope`); no theorem claims the full complex `U(1)` phase or that quantum theory is recovered whole. Real (signed) interference is the honest claim; the complex phase and the Born rule (Series 2.12) are the disclosed gap.
- **The sign non-trivial, the fork not by fiat (audit b).** `amp` takes both `+1` and `-1` on the carriers (WS1); interference (`attTri`) and the additive pole (`attStar`) are both reachable from the SAME `amp`/weight, only the directed attention differing; the verdict discriminates.
- **ADDITIVE-ONLY and DISCONNECTED honorable.** If no signed amplitude survived → DISCONNECTED; if no combined weight ever fell below its parts → ADDITIVE-ONLY (the honest NOT-RECOVERED, the specification: add a phase). Neither materialises (§ de-risking), but both are pre-registered and reachable in the verdict function.

## 4. Cross-workstream triage

| WS | Object | Headline(s) | Costume foreclosed |
|----|--------|-------------|--------------------|
| WS1 (ground) | `amp`, `loopAmp` | `ws1_amp_signed` | a real sign to cancel; not constant; the S2.8 fork read up |
| WS2 | `amp` | `ws2_amp_cancels`, `ws2_amp_cancels_general` | genuine subtraction from S2.8 antisymmetry; not two hand-picked values |
| WS3 (anti-costume core) | `combinedWeight`, `partsWeight` | `ws3_destructive`, `ws3_destructive_iff`, `ws3_amp_earned` | strict weight below parts, not additive bookkeeping; earned off `hol`, no complex number |
| WS4 (the knot) | `combinedWeight`/`partsWeight` on carriers | `ws4_interfering_reachable`, `ws4_additive_reachable` | both poles genuine, no fiat; same fork as S2.8 |
| WS5 | `verdict` | `ws5_verdict_eq (= interfering)`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit (a)-(e) | computed, not hand-set |

## 5. The outcomes (WS5)

`interfering` (a signed model-derived amplitude destructively cancels in a weight — combined weight strictly below the parts, both poles reachable → the door to quantum theory, the expected close, real/signed), `additiveOnly` (no combined weight ever falls below its parts — distinction only accumulates, the world classical, the NOT-RECOVERED specification: add a phase), `shapeDrawn` (the fork drawn, neither pole decided), `disconnected` (no signed amplitude survives — no sign to cancel), `partial'` (degenerate; `partial` is a Lean keyword — the amplitude not earned, or the weight rigged).

## 6. Names-in-prose rule (audit e)

The concept-words — phase, amplitude, interference, quantum, superposition, wave, complex, self, import, God, choice — appear only in docstring prose. Every proof term, definition, and discharged obligation carries a NEUTRAL name (`amp`, `directAmp`, `loopAmp`, `combinedWeight`, `partsWeight`, `verdict`, `Outcome`, `ws*`). `amp` is the sanctioned neutral name for the sign (it is NOT the whole word "amplitude"; the charter's own target theorem names — `ws1_amp_signed`, `ws2_amp_cancels`, `ws3_amp_earned` — use it). No headline embeds a forbidden content-word as a whole word (`ws4_interfering_reachable` uses "interfering", not the forbidden whole word "interference"). The §6 grep runs over `formal/` only; docstring/comment prose and the Lean `import` keyword are exempt (they are not proof-term names).
