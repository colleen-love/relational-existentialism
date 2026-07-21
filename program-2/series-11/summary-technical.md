# Series 2.11 — The Phase (technical summary)

**Verdict: INTERFERING** (computed by `ws5_verdict_eq`, `rfl`, axiom-clean). Scoped: real (`±1`) interference; the complex `U(1)` phase and the Born rule are the disclosed forward-note (Series 2.12).

## Imports and carrier

Imports `P2S8` only (reaching `P2S7 / … / P2S0 / P1` transitively); does NOT import the tier-1 probes `P2S9`/`P2S10`. Working material, all built and axiom-checked in Series 2.8:

- `incr att x y := ⟦y∈att x⟧ - ⟦x∈att y⟧ : ℤ`, antisymmetric (`incr x y + incr y x = 0`);
- `hol att x y z := incr att x y + incr att y z + incr att z x : ℤ`;
- carriers `attTri` (`hol attTri p0 p1 p2 = 3`, odd), `attStar` (`hol attStar p0 p1 p2 = 0`, even); population `S = Fin 3`, `p0 p1 p2`.

## The one added primitive (`formal/P2S11/ws1.lean`)

```
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1        -- the parity sign, ±1-valued
def directAmp : ℤ := amp 0                                 -- the direct path, +1
def loopAmp (att) : ℤ := amp (hol att p0 p1 p2)            -- the loop path, amp(hol)
def combinedWeight (att) : ℤ := (directAmp + loopAmp att) ^ 2
def partsWeight    (att) : ℤ := directAmp ^ 2 + (loopAmp att) ^ 2
```

## Results (headline theorems, all sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})

| WS | Theorem | Content |
|----|---------|---------|
| WS1 | `ws1_amp_signed` | `loopAmp attTri = -1 ∧ loopAmp attStar = 1` — the sign takes both values |
| WS1 | `amp_values`, `amp_sq` | `amp n ∈ {1,-1}`; `amp n ^ 2 = 1` (the real-sign disclosure; unit weight) |
| WS2 | `ws2_amp_cancels` | `directAmp + loopAmp attTri = 0` — opposite signs cancel |
| WS2 | `ws2_amp_cancels_general` | `(m+n)%2 = 1 → amp m + amp n = 0` — opposite parity ⇒ cancel (earned, general) |
| WS3 | `ws3_destructive` | `combinedWeight attTri < partsWeight attTri` (`0 < 2`) — destructive interference, strict |
| WS3 | `ws3_destructive_iff` | `(amp m + amp n)^2 < amp m^2 + amp n^2 ↔ amp m + amp n = 0` — below-parts IFF the signs cancel (not a relabelled addition) |
| WS3 | `ws3_amp_earned` | `loopAmp = amp∘hol`, `hol` the `incr`-sum, `incr` the signed membership diff — all `rfl` (no complex number) |
| WS4 | `ws4_interfering_reachable` | `combinedWeight attTri < partsWeight attTri` — the interfering pole (odd holonomy) |
| WS4 | `ws4_additive_reachable` | `partsWeight attStar ≤ combinedWeight attStar` (`2 ≤ 4`); `= 4`, `= 2` — the additive pole (even holonomy) |
| WS5 | `ws5_verdict_eq` | `verdict true true true true true true = interfering` (`rfl`, no axioms) |
| WS5 | `ws5_verdict_discriminates` | the verdict reaches all five outcomes |
| WS5 | `ws5_flags_justified` | the flags discharged by the WS1–WS4 headlines |
| WS5 | `ws5_audit_{earned,fork_genuine,destructive,scope,names_not_terms}` | audits (a)–(e) |

## The construction, precisely

The interference is WITHIN one world, between the direct path (accumulated increment `0`, sign `amp 0 = +1`) and the loop path around `p0 → p1 → p2 → p0` (accumulated increment `hol att p0 p1 p2`, sign `amp (hol …)`) — the honest double-slit analog, two paths to one outcome. The combined weight `(amp 0 + amp (hol att …))²` falls strictly below the parts weight `amp 0 ² + amp (hol att …)²` exactly when the two signs cancel, which (by `ws2_amp_cancels_general` and `ws3_destructive_iff`) happens exactly when `hol att p0 p1 p2` is odd. On `attTri` (`hol = 3`, odd) it does: `0 < 2`, destructive. On `attStar` (`hol = 0`, even) it does not: `2 ≤ 4`, constructive/additive. Same `amp`, same weights, only the imported directed attention differs — the Series 2.8 frustrated/gluable fork read one level up as interference vs classical.

## Discipline discharged

- **No-smuggling gate (a), sharpest in the program.** `amp` is a `±1`-valued function of the imported `hol`; `ws3_amp_earned` witnesses by `rfl` that no verdict-deciding value is a free parameter or a complex number. The strip test leaves `(a+b)^2 < a^2 + b^2` for signs read off the built holonomy.
- **Costume gate (c).** `ws3_destructive` is a STRICT inequality reducing to `0 < 2` with `partsWeight = directAmp² + loopAmp² = 2` (not a tuned constant); `ws3_destructive_iff` proves below-parts is not a relabelled addition (it is exactly the sign cancellation, impossible for a classical mixture where weights add).
- **Scope disclosed (d).** `amp` is a real `±1` (`amp_values`); no theorem claims the complex `U(1)` phase or full quantum theory.
- **Fork not by fiat (b).** Both poles reachable on the two imported attentions from the same `amp`/weight; the verdict discriminates.
- **Names-not-terms (e).** No declared identifier is a forbidden whole word; the §6 grep hits are docstring prose or the `import` keyword only.

## Forward-note

The full complex `U(1)` phase and the Born rule (Series 2.12, The Weight) are the disclosed gap between this real (signed) interference and the whole of quantum mechanics. Series 2.11 proves distinction can subtract — the door to quantum theory is open — but the complex structure and the probability rule remain beyond it. The candidate seed for the complex phase, per the charter, is the two-facing reader of Series 2.2 (an oriented, antisymmetric structure is where a phase is born); 2.11 opens the door, it does not walk through it.
