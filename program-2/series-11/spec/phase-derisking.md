# Phase de-risking — the signed sign off the holonomy, and genuine destructive cancellation, by hand (2.11)

**Phase B gate. This file is written and checked BEFORE any WS design and before any `formal/` file. It hunts, on paper, for a SIGN read off Series 2.8's built holonomy — a function of the built `incr`/`hol` alone, no bolted-on complex number — that (a) is genuinely SIGNED (takes both `+1` and `-1` on Series 2.8's carriers), (b) on the frustrated cycle (`hol = 3`, odd) makes two contributions to one outcome give a combined weight STRICTLY below the sum of the parts (`0 < 2`), and (c) on the gluable cycle (`hol = 0`, even) makes the combined weight the ordinary (constructive) sum, with no cancellation. Only a candidate surviving ALL THREE earns the WS designs. If the cancellation is only additive — no combined weight ever falls below its parts — the series lands ADDITIVE-ONLY (the honest NOT-RECOVERED, the specification: add a phase). Rejected candidates are recorded. The Series 2.10 discipline (the sharpest no-smuggling bar) governs: the sign must be READ OFF the built holonomy, never a complex number added to produce cancellation.**

The whole computation lives at `Cardinal.{0}` on finite carriers; every claim below is an integer arithmetic fact and is `decide`/`omega`/`norm_num`-checkable, so the paper hunt and the build agree by construction.

---

## 0. The imported material this stands on

Series 2.11 imports `P2S8` only; `P2S7 / … / P2S0 / P1` are reached transitively. It does NOT import the tier-1 probes `P2S9`/`P2S10` (their content — the cone, reversibility — is not reused). Working material, all built and axiom-checked in Series 2.8:

- **The signed directed-attention increment** `incr att x y := (⟦y∈att x⟧) - (⟦x∈att y⟧) : ℤ`, the FIRST quantity in the program that cancels: `incr att x y + incr att y x = 0` (`ws3_two_body_trivial.1`, definitional antisymmetry). Values in `{-1, 0, +1}`, a function of the directed attention alone.
- **The holonomy** `hol att x y z := incr att x y + incr att y z + incr att z x : ℤ`, the net translation around the triangle.
- **The two carriers and their holonomies:** the FRUSTRATED directed 3-ring `attTri` with `hol attTri p0 p1 p2 = 3` (`ws4_frustrated_reachable.1`, ODD); the GLUABLE mutual star `attStar` with `hol attStar p0 p1 p2 = 0` (`ws4_gluable_reachable.1`, EVEN).
- **The directed knowing-asymmetry** (`P2S0`/`P2S2`, transitive): `x` may attend `y` without `y` attending `x`. This oriented, antisymmetric structure is the seed of a sign — a symmetric relating carries no holonomy and hence no sign to cancel (`ws3_holonomy_model_derived.2.1`).

Everything Series 2.11 adds is one function of these and its squared modulus. No new carrier, no complex number, no postulated phase.

## 1. The one thing added: the parity SIGN read off the holonomy

Everything below is derived from ONE function of the BUILT holonomy, read off `hol` and nothing else:

```
amp : ℤ → ℤ ,   amp n  :=  if n % 2 = 0 then 1 else -1 .
```

`amp n` is the parity sign of the integer `n`: `+1` when `n` is even, `-1` when `n` is odd. It is the sign `(-1)^n` written without any complex or real power — a bare `±1`-valued function of an integer. Applied to the accumulated increment along a directed path, it is the sign that path contributes. Along a CLOSED path (a triangle) the accumulated increment IS Series 2.8's holonomy, so the sign of the loop path is `amp (hol att x y z)`.

**(A0) `amp` is EARNED — a function of the built `incr`/`hol`, definitionally.** `amp` takes an integer and returns its parity sign; the integer it is applied to is `hol att x y z = incr att x y + incr att y z + incr att z x`, itself the built signed-`knows` sum. There is no free parameter, no complex number, no postulated phase: the only input is the built holonomy. The strip test (delete "phase"/"amplitude"/"interference") leaves the bare fact: *`amp` is a `±1`-valued function of `hol`.* This is `ws3_amp_earned`.

**(A1) `amp` is a real SIGN, values in `{+1, -1}` — the scope, disclosed.** For every `n`, `amp n = 1 ∨ amp n = -1` (parity is `0` or `1`, `Int.emod_two_eq_zero_or_one`). The amplitude this series earns is a REAL sign, not a complex `U(1)` phase; the complex phase and the Born rule (Series 2.12) are the disclosed gap. No claim exceeds `±1`. This is `ws5_audit_scope`.

**(A2) `amp n ^ 2 = 1` for every `n`.** Since `amp n ∈ {+1, -1}`, `(amp n)^2 = 1` (`1^2 = 1`, `(-1)^2 = 1`). The squared modulus of a single sign is `1`; this is the "part" weight each single contribution carries. (Checked: parity cases, `ring`.)

## 2. The two paths to one outcome, and their signs (WS1 de-risking)

The interference is WITHIN one world, between two directed paths that arrive at the SAME outcome — the honest double-slit analog. Fix the basepoint self `p0`. Two paths return to `p0`:

- **The direct path** — stay at `p0`, accumulated increment `0`, sign `directAmp := amp 0`.
- **The loop path** — go around the ring `p0 → p1 → p2 → p0`, accumulated increment `hol att p0 p1 p2`, sign `loopAmp att := amp (hol att p0 p1 p2)`.

Reading `amp` off the two carriers' holonomies:

| carrier | `hol att p0 p1 p2` | parity | `directAmp = amp 0` | `loopAmp = amp hol` |
|---|---|---|---|---|
| `attTri` (frustrated) | `3` | ODD  | `+1` | `-1` |
| `attStar` (gluable)   | `0` | EVEN | `+1` | `+1` |

**(S1) The sign is genuinely SIGNED (takes both values).** `loopAmp attTri = amp 3 = -1` (3 is odd) and `loopAmp attStar = amp 0 = +1` (0 is even): the sign read off the holonomy takes BOTH `-1` and `+1` on Series 2.8's carriers. There is a real sign to cancel — the series is not DISCONNECTED (no signed amplitude). (Checked: `decide` after `hol` rewritten by `ws4_*`.) This is `ws1_amp_signed`.

**Not a constant (the WS1 costume watch).** If `amp` were constant, there would be no sign to cancel and the honest close would be ADDITIVE-ONLY. It is not: the frustrated cycle's odd holonomy and the gluable cycle's even holonomy give opposite signs. The signedness is the SAME S2.8 fork (frustrated vs gluable) read one level up.

## 3. Cancellation: the two paths sum to zero (WS2 de-risking)

In the FRUSTRATED world, the direct and loop paths carry opposite signs, so their contributions SUBTRACT:

```
directAmp + loopAmp attTri  =  amp 0 + amp 3  =  (+1) + (-1)  =  0 .
```

**(C1) Opposite signs sum to zero — genuine subtraction.** `directAmp + loopAmp attTri = 0`. This is the first subtraction in the program's dynamics carried up to a weight-bearing sign: two ways of arriving at `p0` cancel. It is carried from Series 2.8's antisymmetry (`incr x y + incr y x = 0`) — the same signed structure, now read through `amp`. (Checked: `decide`.) This is `ws2_amp_cancels`.

**(C2) The general cancellation criterion (earned, not two hand-picked values).** For any two integers `m, n` of OPPOSITE parity (`(m + n) % 2 = 1`), `amp m + amp n = 0`: one is even (sign `+1`), the other odd (sign `-1`), and they cancel. The concrete `directAmp + loopAmp attTri = 0` is the instance `m = 0, n = 3`. So cancellation is not a coincidence of two chosen carriers; it is forced whenever the two path holonomies differ in parity. (Checked: parity cases, `omega`.) This is `ws2_amp_cancels_general`.

## 4. Interference, not accumulation: the combined weight below its parts (WS3 de-risking, the anti-costume core)

The WEIGHT of a combined contribution is its squared modulus. For a real sign, `|a|² = a²`, so:

```
combinedWeight att  :=  (directAmp + loopAmp att) ^ 2        -- the two paths, combined then weighed
partsWeight    att  :=  directAmp ^ 2 + (loopAmp att) ^ 2    -- the two paths weighed separately, summed
```

Genuine DESTRUCTIVE interference is a combined weight STRICTLY below the sum of the parts — the quantum signature no classical probability can show (classically, weights add, so the combined weight equals the parts and can only grow).

**(I1) DESTRUCTIVE on the frustrated cycle (`hol = 3`, odd).**
```
combinedWeight attTri  =  (directAmp + loopAmp attTri)^2  =  (1 + (-1))^2  =  0^2  =  0
partsWeight    attTri  =  directAmp^2 + (loopAmp attTri)^2  =  1^2 + (-1)^2  =  1 + 1  =  2
```
so `combinedWeight attTri = 0 < 2 = partsWeight attTri`. The combined weight is STRICTLY below the sum of the parts: two ways of reaching `p0`, combined, make the arriving LESS likely than either alone — genuine destructive interference. (Checked: `norm_num` after the sign rewrites.) This is `ws3_destructive` / `ws4_interfering_reachable`.

**(I2) ADDITIVE (constructive) on the gluable cycle (`hol = 0`, even).**
```
combinedWeight attStar  =  (directAmp + loopAmp attStar)^2  =  (1 + 1)^2  =  2^2  =  4
partsWeight    attStar  =  directAmp^2 + (loopAmp attStar)^2  =  1^2 + 1^2  =  2
```
so `partsWeight attStar = 2 ≤ 4 = combinedWeight attStar`: the combined weight is NOT below the parts (it is the parts times a constructive factor, `4 = 2·2`). No destructive cancellation; the aligned/classical pole. (Checked: `norm_num`.) This is `ws4_additive_reachable`.

**(I3) The general interference criterion (earned, the anti-costume theorem).** For any two integers whose amplitudes are `a = amp m`, `b = amp n` (each `±1` by A2), the combined weight falls strictly below the parts IFF the signs cancel:
```
(a + b)^2 < a^2 + b^2  ↔  a + b = 0     ( since a^2 = b^2 = 1, i.e. parts = 2, and (a+b)^2 ∈ {0, 4} )
```
and `a + b = 0` iff `m, n` differ in parity (C2), i.e. iff the RELATIVE holonomy `m + n` (here the loop holonomy against the direct path's `0`) is ODD. So destructive interference happens EXACTLY when the loop holonomy is odd — the frustrated cycle interferes, the gluable cycle does not, and nothing is hand-picked. (Checked: `amp` values, `nlinarith`/`omega`.) This is `ws3_destructive_iff` (the strengthening that makes the fork a theorem, not a coincidence).

**Neither costume front.**
- **Not additive bookkeeping (the costume gate, audit c).** The claim is a STRICT inequality `combinedWeight < partsWeight` (`0 < 2`), not a signed sum relabelled. A combined weight below the parts is impossible for any classical mixture (where weights add, `combined ≥ parts`). The signed sum being zero (C1) is necessary but not sufficient; the WEIGHT falls below the parts (I1) is the whole content.
- **Not a bolted-on phase (the no-smuggling gate, audit a).** `amp` is a `±1`-valued function of the built `hol` (A0); no complex number is added. The strip test leaves `(a+b)^2 < a^2 + b^2` for the signs `a, b` read off the built holonomy.

## 5. The FORK: INTERFERING and ADDITIVE-ONLY both reachable (WS4 de-risking)

Two concrete carriers, both on the built directed-attention model, exhibit the two poles, from the SAME `amp`/weight definitions — only the directed attention differs:

- **INTERFERING-reachable:** the frustrated ring `attTri` (`hol = 3`, odd) → `combinedWeight < partsWeight` (`0 < 2`), genuine destructive interference (I1).
- **ADDITIVE-reachable:** the gluable star `attStar` (`hol = 0`, even) → `partsWeight ≤ combinedWeight` (`2 ≤ 4`), no destructive cancellation (I2).

**Both sides genuine, neither by fiat.** Interference is not built into `amp`/weight (the star gives no cancellation); the additive pole is not built in (the ring cancels): same `amp`, same weight, only the directed attention differs. The verdict discriminates on the built holonomy — the same fork Series 2.8 found (frustrated vs gluable) now decides interference vs classical. This is `ws4_interfering_reachable` + `ws4_additive_reachable`.

## 6. Verdict of the de-risking

- A signed sign read off the built holonomy survives, taking both values (§2, S1): **not DISCONNECTED (no signed amplitude).**
- The signs cancel (§3, C1/C2): **genuine subtraction, carried from Series 2.8's antisymmetry.**
- The combined weight falls STRICTLY below the parts on the frustrated cycle (§4, I1): **genuine destructive interference, not additive bookkeeping — not the costume.**
- The sign is a function of the built `hol`, no complex number added (§1, A0): **the no-smuggling gate cleared, at its sharpest.**
- Both poles reachable on genuine carriers (§5): **the fork is not by fiat.**
- The amplitude is a real `±1` (§1, A1); no complex `U(1)` phase claimed: **the scope disclosed, no overclaim.**

**A signed, earned, genuinely destructive amplitude survives on paper. Phase B proceeds to the WS designs.** The expected computed verdict is **INTERFERING**: the signed holonomy Series 2.8 built is a genuine phase — distinction can SUBTRACT, two paths to one outcome cancel, the combined weight falls below the parts — the door to quantum theory open, honestly scoped as REAL (signed, `±1`) interference, with the complex `U(1)` phase and the Born rule the disclosed forward-note. Nothing before Series 2.8 could cancel; here it does, and the cancellation is genuine destructive interference.

### Rejected candidates (recorded)

- **A bolted-on complex amplitude `e^{iθ}` with `θ` free, then "find" interference.** Rejected as THE smuggle (the no-smuggling gate, sharpest here): a complex number not read off the model decides interference on a gadget beside the world. `amp` is admitted BECAUSE it is a `±1`-valued function of the built `hol` alone — the parity sign of the accumulated increment, no free parameter.
- **The signed sum `directAmp + loopAmp = 0` alone, called "interference."** Rejected as additive bookkeeping (the costume gate): a signed sum being zero is not interference unless the WEIGHT (squared modulus) falls below the parts. The strict inequality `combinedWeight < partsWeight` (`0 < 2`) is required and is what I1 proves; the bare `sum = 0` is only WS2, necessary but not sufficient.
- **`incr` itself as the amplitude (values `{-1,0,+1}`).** Rejected at WS1/WS3: `incr` takes the value `0` (absent/mutual edge), so `|incr|²` is not a constant `1` and the parts weight is not fixed; the clean `(a+b)^2 < a^2+b^2` interference inequality needs unit-modulus contributions. The PARITY sign `amp (hol …)` is `±1`-valued (never `0`), the honest unit amplitude; `incr`'s cancellation is the raw material (WS2), `amp`'s squared modulus is the interference (WS3).
- **A complex `U(1)` phase `amp' : ℤ → ℂ`, `amp' n = i^n`, claiming full quantum interference.** Rejected at scope (audit d): the series earns a REAL sign only; a complex phase would OVERCLAIM the full `U(1)` structure of quantum theory, which this series does not build. The complex phase is the disclosed forward-note (Series 2.12), not this series' target. Real (signed) interference is a genuine step, honestly scoped, never inflated.
- **Rigging the weight (defining `partsWeight` large so `combined < parts` trivially).** Rejected as a rigged fork: `partsWeight` is `directAmp^2 + loopAmp^2 = 1 + 1 = 2` by A2 (each single sign has unit weight), not a free constant; the inequality `0 < 2` is a fact about the squared modulus, not a tuned threshold.
