# Born de-risking — is the weight a probability, and is it forced to be the square, by hand (2.12)

**Phase B gate. This file is written and checked BEFORE any WS design and before any `formal/` file. It hunts, on paper, for the reading of Series 2.11's WEIGHT as a PROBABILITY carried by the imports, and for the CONSISTENCY test that forces (or refutes) the Born form. The two candidate measures on a combined outcome are the CLASSICAL additive (square each path amplitude, then add over the ways) and the BORN (add the amplitudes, then square). The by-hand test on Series 2.11's carriers must decide three things: (a) does the classical additive measure CONTRADICT the interference (does it give a non-zero weight where the interference cancels the outcome to nothing), (b) is the Born measure CONSISTENT with the interference (does it vanish exactly on the cancellation) and non-negative, and (c) do the imports carry a GENUINE non-trivial measure at all (else DETERMINISTIC). Only if the Born form is FORCED by consistency — the classical form genuinely refuted, a non-trivial measure surviving — does BORN earn the WS designs. If the classical form is not genuinely refuted, land STOCHASTIC-NOT-BORN; if no non-trivial measure survives, land DETERMINISTIC (interference without chance, the honest report). The Series 2.11 discipline (the sharpest no-smuggling bar in the program) governs, PROMOTED here: no object DEFINES the probability as `|amp|²`; the squared form is READ OFF the imported weight and shown consistent while the classical is refuted, never asserted.**

The whole computation lives at `Cardinal.{0}` on finite carriers; every claim below is an integer arithmetic fact and is `decide`/`omega`/`norm_num`-checkable, so the paper hunt and the build agree by construction.

---

## 0. The imported material this stands on

Series 2.12 imports `P2S11` only; `P2S8 / P2S7 / … / P2S0 / P1` are reached transitively. It does NOT import the tier-1 probes `P2S9`/`P2S10` (their content — the cone, reversibility — is not reused). Working material, all built and axiom-checked in Series 2.11 (and, through it, Series 2.8):

- **The sign** `P2S11.amp n := if n % 2 = 0 then 1 else -1 : ℤ`, the `±1`-valued parity sign of an integer, a function of the built holonomy alone (`amp_values : ∀ n, amp n = 1 ∨ amp n = -1`; `amp_sq : ∀ n, amp n ^ 2 = 1`).
- **The two path signs** `P2S11.directAmp := amp 0` (the direct/do-nothing path, `= +1`, `directAmp_eq`) and `P2S11.loopAmp att := amp (hol att p0 p1 p2)` (the around-the-ring path).
- **The two candidate combined weights** `P2S11.combinedWeight att := (directAmp + loopAmp att)^2` (the amplitudes SUMMED, then squared — the ADD-then-SQUARE form) and `P2S11.partsWeight att := directAmp^2 + (loopAmp att)^2` (each amplitude SQUARED, then summed — the SQUARE-then-ADD form). These two neutral objects are ALREADY the two candidate measures; Series 2.12 adds no new arithmetic, only the reading and the consistency test.
- **The interference** `P2S11.ws3_destructive : combinedWeight attTri < partsWeight attTri` (the combined weight falls STRICTLY below the parts on the frustrated cycle) and `P2S11.ws2_amp_cancels : directAmp + loopAmp attTri = 0` (the paths cancel on the frustrated cycle). The carriers `P2S8.attTri` (frustrated, `hol = 3`, odd) and `P2S8.attStar` (gluable, `hol = 0`, even), reached transitively.
- **The imports** — the out-of-image differentiator, the program's one genuine freedom (`P2S0` / `P1`, a permanent open, reached transitively). The candidate carrier of chance: the free selection among the outcomes.

Everything Series 2.12 adds is ONE thing: the reading of `combinedWeight`/`partsWeight` as two candidate measures over the outcomes, and the CONSISTENCY predicate that forces the Born (add-then-square) form and refutes the classical (square-then-add) one. No new carrier, no complex number, no postulated probability.

## 1. The two candidate measures, stated as operations (not as interpretations)

A measure assigns a weight to a combined outcome from the amplitudes of the two paths that reach it (the direct path `a := directAmp` and the loop path `b := loopAmp att`). Two orders of operation are possible, and they are the whole of the classical-vs-quantum question:

```
SQUARE-then-ADD  (classical additive) :  a^2 + b^2              =  partsWeight att
ADD-then-SQUARE  (Born)               :  (a + b)^2              =  combinedWeight att
```

Both are already built in Series 2.11 as neutral objects (`partsWeight`, `combinedWeight`); neither is named for its interpretation. The classical additive measure adds the per-path weights (as a classical probability of "either path" would); the Born measure adds the amplitudes first and squares the total (as quantum mechanics does). The question is which one is CONSISTENT with the interference the model actually carries — and that question is decided, not chosen.

**(A0) Neither measure is DEFINED as the probability.** The two objects are the imported `partsWeight`/`combinedWeight`, arithmetic on the imported `amp`. Series 2.12 does not write `probability := combinedWeight`; it writes a form-agnostic consistency predicate (§3) and PROVES the add-then-square object satisfies it while the square-then-add object does not. The squared form is forced by that proof, never asserted. This is the no-smuggling gate, promoted first-class.

## 2. The physical anchor: cancellation is absence

Series 2.11 established (`ws2_amp_cancels`, `ws3_destructive`) that on the frustrated cycle the two paths to the basepoint `p0` cancel: their amplitudes sum to zero, `a + b = 1 + (-1) = 0`, and the combined weight falls to `0`. The interference is precisely this: two ways of arriving, combined, make the arriving NOT happen. The physical content is a single anchor, form-independent:

> **When the amplitudes of the paths to an outcome cancel (`a + b = 0`), the outcome does not occur, so any weight claiming to be the outcome's probability must be ZERO on that configuration.**

This anchor is not the square. It is the demand that a probability respect the interference: a fully-cancelled outcome carries no weight. A candidate measure either satisfies it or contradicts it, and that is the test.

## 3. The consistency test (the primitive Series 2.12 adds)

Read the anchor as a predicate on any candidate measure `μ : (S → Finset S) → ℤ`:

```
respectsCancel μ  :=  ∀ att,  (directAmp + loopAmp att = 0)  →  μ att = 0 .
```

`respectsCancel μ` says: wherever the amplitudes cancel, `μ` assigns weight zero. It mentions no square; it is the bare demand that the measure vanish on the interference. Now test the two candidates on Series 2.11's carriers.

**(B1) The BORN measure is CONSISTENT (add-then-square respects cancellation).** If `directAmp + loopAmp att = 0` then
```
combinedWeight att  =  (directAmp + loopAmp att)^2  =  0^2  =  0 ,
```
so `respectsCancel combinedWeight` holds — for EVERY `att`, not just `attTri`, because the square of zero is zero. The add-then-square form vanishes exactly on the cancellation. And it is NON-NEGATIVE everywhere: `combinedWeight att = (…)^2 ≥ 0` (`sq_nonneg`). A non-negative weight that vanishes on cancellation — a genuine candidate probability. (Checked: `sq_nonneg`; `x = 0 → x^2 = 0`.) This is `ws3_sq_consistent`.

**(B2) The CLASSICAL additive measure is REFUTED (square-then-add contradicts cancellation).** On the frustrated cycle the amplitudes cancel (`directAmp + loopAmp attTri = 0`, `ws2_amp_cancels`), yet
```
partsWeight attTri  =  directAmp^2 + (loopAmp attTri)^2  =  1^2 + (-1)^2  =  1 + 1  =  2  ≠  0 .
```
So `¬ respectsCancel partsWeight`: the classical additive measure assigns weight `2` to an outcome whose amplitude has cancelled to nothing. It CONTRADICTS the interference — it insists the outcome occurs (weight `2`) where the physics says it does not (weight `0`). The classical additive probability is refuted by the built structure, not excluded by fiat. (Checked: `decide` after the sign rewrites, witness `attTri`.) This is `ws3_classical_fails`.

**(B3) The two measures genuinely DIFFER (not one relabelled).** On `attTri`, `combinedWeight attTri = 0` while `partsWeight attTri = 2`; they are distinct functions, and only the add-then-square one survives the consistency test. The squared form is FORCED as the consistent measure — the residue of the test, not its premise. This is `ws3_sq_forced`.

## 4. Is there a genuine measure at all? (the WS1/WS4 chance question)

Genuine chance requires the imports to carry a NON-TRIVIAL measure — a weight that is not constant across the outcomes, so that the possibilities are genuinely weighted differently. Test the Born measure for non-triviality across the two carriers (the two possibilities the free differentiator selects between):

```
combinedWeight attTri   =  (1 + (-1))^2  =  0
combinedWeight attStar  =  (1 +   1 )^2  =  4
```

**(M1) The Born measure is NON-TRIVIAL.** `combinedWeight attTri = 0 ≠ 4 = combinedWeight attStar`: the add-then-square weight takes distinct values on the two configurations the imports select between. The freedom is genuinely WEIGHTED — there is a non-trivial measure over the possibilities, so chance is not empty. (Checked: `decide`.) This is the ground of `ws1_outcomes_nontrivial` (distinct outcomes with distinct amplitudes, `loopAmp attTri = -1 ≠ 1 = loopAmp attStar`) and the `nontrivial` flag of WS4.

**(M2) The classical additive measure is TRIVIAL — a second reason it is not the measure.** Each single sign has unit weight (`amp_sq`), so `partsWeight att = 1 + 1 = 2` for EVERY `att`: the square-then-add form is CONSTANT `2`, blind to which outcome obtains. It carries no information over the possibilities — it is not merely inconsistent (B2) but structureless. The non-trivial measure the imports carry is the add-then-square one. (Checked: `amp_sq`.) 

**(M3) DETERMINISTIC is genuinely reachable, not excluded by fiat.** A structureless freedom — modelled by a CONSTANT weight `fun _ => c` — carries no non-trivial measure (`∀ att att', (fun _ => c) att = (fun _ => c) att'`). Such a measure exists and is a distinct, pre-registered possibility; the DETERMINISTIC pole is not construction-blocked. This world does not land there (the imports' actual weight `combinedWeight` is non-trivial, M1), but the fork is genuine. This is `ws4_deterministic_reachable`.

## 5. The FORK: BORN reachable, DETERMINISTIC reachable, STOCHASTIC-NOT-BORN discriminated

- **BORN-reachable:** the imports carry a NON-TRIVIAL measure (`combinedWeight`, values `0` and `4`, M1) whose CONSISTENT form is the squared amplitude (add-then-square respects cancellation, B1) while the classical additive form is REFUTED (B2). Quantum probability in its rebit form, on directed-attention carriers, no fiat. This is `ws4_squared_reachable`.
- **DETERMINISTIC-reachable:** a constant weight is a trivial measure (M3) — no chance, the deepest NOT-RECOVERED, a genuine and distinct pole.
- **STOCHASTIC-NOT-BORN — discriminated, not witnessed.** A measure that is non-trivial but NOT the squared/consistent form would be chance of the wrong shape. On the rebit ±1 amplitudes the only two natural measures are the square (consistent, B1) and the additive (refuted AND trivial, B2/M2); no non-square measure survives consistency here. So STOCHASTIC-NOT-BORN is a pre-registered outcome the verdict function CAN return (it discriminates), but it is NOT claimed as reachable on these carriers. Honest: this world's consistent measure IS the square. (The general non-square measure, and Gleason/Busch uniqueness among all `|·|^p`, are the disclosed forward-note.)

**Both live poles genuine, neither by fiat.** BORN is not built into the objects (a constant weight gives DETERMINISTIC, M3; the classical additive form is a genuine distinct measure that genuinely fails, B2); DETERMINISTIC is not built in (the actual imported weight is non-trivial, M1). Same `combinedWeight`/`partsWeight`, same consistency predicate; which pole obtains is decided by whether the imports' weight is non-trivial and whether its consistent form is the square — both computed, not chosen.

## 6. Verdict of the de-risking

- The imports carry a NON-TRIVIAL measure (§4, M1): the Born weight takes distinct values `0`/`4` — **genuine chance, not DETERMINISTIC.**
- The Born (add-then-square) measure RESPECTS the cancellation and is non-negative (§3, B1): **a consistent candidate probability.**
- The classical (square-then-add) measure CONTRADICTS the cancellation (§3, B2) and is moreover constant/structureless (§4, M2): **refuted, not excluded by fiat.**
- The two measures genuinely differ and only the square survives (§3, B3): **the squared form FORCED by consistency, not defined.**
- The measure is NON-CLASSICAL — the combined weight falls below the parts (imported `ws3_destructive`): **no classical additive probability can reproduce it.**
- The amplitude is a real `±1` (imported `amp_values`); no complex phase, no Gleason uniqueness claimed: **the scope disclosed as the rebit Born rule, no overclaim.**

**A non-trivial, non-negative, non-classical measure survives on paper, and its consistent form is the squared amplitude — the classical additive form refuted, not excluded. Phase B proceeds to the WS designs.** The expected computed verdict is **BORN (squared)**: the imports carry a measure whose only cancellation-consistent form is the squared amplitude — quantum probability recovered in its rebit form, the second quantum pillar, honestly scoped (the amplitude is Series 2.11's real ±1 sign; the full complex amplitude and Gleason's / Busch's uniqueness are the disclosed forward-note). The Born rule is EARNED from the interference — the square is the residue of the consistency test — never named.

### Rejected candidates (recorded)

- **Defining `probability := combinedWeight` (`|amp|²`) and "recovering" Born.** Rejected as THE smuggle (the no-smuggling gate, sharpest here, audit a): a probability asserted to be the square proves nothing. The squared form is admitted BECAUSE it, alone of the two candidate measures, satisfies the form-agnostic `respectsCancel` predicate while the classical additive form fails it. The square is forced by the consistency proof, never written into a definition.
- **Excluding the classical additive measure by construction (never building it).** Rejected as the fork by fiat (audit d): `partsWeight` is the genuine, imported square-then-add measure; it is REFUTED by an explicit witness (`attTri`: cancellation holds, weight `2 ≠ 0`), not omitted. A classical measure excluded rather than refuted would be a rigged fork.
- **Claiming a Gleason-unique, complex Born rule.** Rejected at scope (audit c): the amplitude is Series 2.11's real ±1 sign; this series earns at most the rebit Born rule (the square is the consistent one of the TWO candidate measures, not the unique one among all `|·|^p`). The complex amplitude and Gleason's / Busch's uniqueness are the disclosed forward-note, never claimed.
- **Asserting genuine chance where the measure is trivial.** Rejected at audit b: chance is claimed ONLY because the imported weight `combinedWeight` is non-trivial (values `0`/`4`, M1). Were the only surviving measure constant (M2/M3), the honest verdict would be DETERMINISTIC — interference without chance — reported in full. The non-triviality is a checked fact, not an assumption.
- **Reading the constant `partsWeight = 2` as a (uniform) probability.** Rejected at WS2/WS3: a constant weight is trivial (M2) and, worse, it is exactly the classical additive form REFUTED by the interference (B2). A uniform "probability" blind to the outcome and inconsistent with the cancellation is not the measure the imports carry; the non-trivial, cancellation-consistent add-then-square form is.
