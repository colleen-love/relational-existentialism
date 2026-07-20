# Series 2.3, Design Index (`spec/README.md`)

**The imported S2 pair, the primitive (the per-perspective valuation and `Converges₂`, built FRESH and
constrained), the discipline (the fork genuine, the direction never decided, no orientation evaluated, build
fresh), the cross-workstream triage, the outcomes, the names-live-in-prose rule, and the PX-1 twoness-lift
decision. Read once before the `wsNN-design.md` docs; they cite this file for every shared object. This index and
WS1-WS5 are committed as one batch before any `formal/` file exists (Phase B gate).**

*Series 2.3 stands on the Series 2.2 pair (`P2S2`), imported (Program 2's layered chain: S3 imports S2, reaching
S1, S0, and the P1 prior art transitively; nothing below S2 is imported directly). It adds exactly TWO things
over the pair: the VALUATION (a per-perspective valuation, typed, never evaluated) and `Converges₂` (the
coherence relation between two valuations). Series 12's compass/convergence machinery is deliberately EXCLUDED
from the foundation (program-review-1 PR1-S1, the tautology) and is rebuilt FRESH and constrained here.*

---

## 1. What is imported, and from where

The build imports `P2S2` only (gate `^import (P2S2|P2S3)…`); S1, S0, and the P1 prior art are reached
transitively. **Nothing of Series 12's `Converges`/`Compass`/`Faithful`/`orientLift` is imported** (it is not on
the layered chain); every piece of convergence machinery below is written FRESH in `formal/P2S3/` (transcribed in
spirit, never imported), precisely to avoid re-importing the PR1-S1 flaw.

| Object | Origin (reached through S2) | Used by |
|---|---|---|
| `slf`, `oth`, `attendsR`, `rankR`, `RCar = Fin 5`, `rfield` | `P2S2.ws1` | all |
| `outDest`, `finsetToPk`, `ws1_bound_is_finite_attention` | `P2S0.ws1` (via S2) | all |
| `ws1_rcar_SHNE` (every node `SHNE`), `plainOf_rankLiftR`, `rankLiftR_val` | `P2S2.ws1` | WS2, WS3, WS4 |
| `ws2_other_distinguishes`, `ws2_other_reader_wise`, `slfReader`, `ws2_other_non_recoverable` | `P2S2.ws2` | WS5 (K1 anchor) |
| `PkObj`, `PkMap`, `LkObj`, `SReaches`, `SHNE`, `IsBisim`, `IsBisimL`, `plainOf`, `Recoverable` | `P1.Core` (via S2) | all |
| `ws1_atomless_bisim` (the collapse engine, Series 07), `ws4_recoverable_not_import` | `P1.Core` (via S2) | WS2, WS3 |
| `rankLift`, `FiniteAttention`, `AttentionDistinguishes`, `RealFor` | `P1.Reader` (via S2) | WS5 (K1 anchor) |

**Deliberately NOT used** (the guardrails): Series 12's `Compass`/`Converges`/`Faithful`/`orientLift` (excluded,
PR1-S1 — rebuilt fresh and constrained as `Valuation`/`Converges₂`/`Faithful₂`/`valLift`); any evaluated
valuation as a proof term (the central sin, audit (a)); any theorem or definition deciding the direction of
convergence (the central sin, audit (b)); a cardinal ceiling or a new atom.

## 2. The primitive: the TWO additions over the pair

Series 2.3 adds exactly two things over the S2 pair, no new atom and no new structural machinery beyond them:

1. **The VALUATION** — `structure Valuation (X Or : Type)` with fields `val : X → Or` (a per-perspective
   valuation of the shared field, drawn from an EXOGENOUS space `Or` the mathematics never inhabits canonically)
   and `raise : X → X → Or → Or` (carrying a valuation from one locus to another). Every theorem quantifies over
   `Or` and over `c : Valuation …`; no proof term selects, constructs, or reads off a particular valuation (audit
   (a), Series 12's feeling-side discipline). The concrete witness valuations live ONLY inside existentials.

2. **`Converges₂`** — `def Converges₂ (c : Valuation X Or) (x y : X) : Prop := c.raise x y (c.val x) = c.val y`:
   the valuation at `x`, RAISED toward `y`, agrees with the valuation at `y`. Instantiated at the pair `(slf,
   oth)`: the self's valuation carried to the other coheres with the other's own. A genuine equation in `Or`,
   depending on `c`; NOT `True`, NOT `False`, NOT `val x = val x` (WS1's two-sided freedom proves this).

The structural constraint that makes the fork genuine (anti-PR1-S1):

- **`Faithful₂ c := ∀ x y, c.raise x y = id`** — the raising carries the valuation UNCHANGED, so `Converges₂ c x
  y ↔ c.val x = c.val y` (`faithful_converges_iff`). This is the minimal class condition that makes convergence a
  genuine test of valuation-coherence rather than a free re-labelling. The class is non-empty (`id` raising) and,
  crucially, a PROPER sub-relation is what sight carves out of it (below).
- **`InSight dest c := ∀ x y, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y`** — the valuation agrees on
  every plain-bisimilar pair: what the structure can SEE. `dest` is LOAD-BEARING here (contrast PR1-S1, where the
  carrier was phantom in `Compass`/`Converges`): the in-sight constraint is a genuine fact about `outDest attendsR`.

## 3. Why this is genuine and not the PR1-S1 tautology (audit (c), the central watch-point)

PR1-S1 (program-review-1): Series 12's first fork was a tautology because `Compass`/`Converges` mentioned neither
`dest` nor `reify` — the fork landed `underdet` on EVERY structure by the parameter type alone, deciding nothing
about the carrier. The corrected Series 12 fork (program-review-2 PR2-S1) fixed this with the `Faithful` +
`BisimInvariant` two-zone structure whose boundary is Series 07's import boundary. Series 2.3 IS that fork, now on
the S2 pair, and forecloses the tautology by the SAME device, load-bearing on the S2 structure:

- **The forcing uses the structure.** `ws2_converges_decided_in_sight`: an in-sight faithful valuation is FORCED
  to converge at `(slf, oth)` **because `slf` and `oth` are plain-bisimilar** over `outDest attendsR` (the
  collapse engine `ws1_atomless_bisim`, every node `SHNE` by `ws1_rcar_SHNE`). On a structure where `slf` and
  `oth` were NOT plain-bisimilar, the forcing would fail. The fact is about the carrier, not the type.
- **The class is genuinely constrained (a PROPER sub-class).** `ws4_insight_proper`: the in-sight faithful class
  is inhabited (`cUnif`, the uniform valuation) AND properly contained in the faithful class (`cDiss`, the
  dissenting valuation, is faithful but NOT in-sight — it separates the plain-bisimilar `slf`, `oth`). So
  restricting to in-sight is a REAL constraint that excludes a genuine faithful valuation, not a vacuous relabel.
- **Both zones reached on witnessed valuations at the SAME pair.** `ws4_two_zone_convergence`: `cUnif` converges
  and `cDiss` fails, both faithful, both at `(slf, oth)`; and every faithful dissent is a genuine import
  (`ws3_dissent_is_import`). The verdict is a discriminating function reaching more than one value
  (`ws5_verdict_discriminates`).
- **The strip test survives.** WS2 forcing strips to "over the valuations agreeing on plain-bisimilar states, the
  relation holds"; WS3 dissent strips to "`val slf ≠ val oth` on the plain-bisimilar `slf`/`oth` is
  `¬ Recoverable`, by Series 07"; WS4 shape-drawn strips to "a discriminating function over a constrained class
  reaching two values, both witnessed." No payoff needs the words "convergence"/"coherence"/"orientation."

## 4. The discipline (the honesty invariants, applied)

- **No valuation evaluated (audit (a), the central sin of the feeling side).** Every theorem quantifies over `Or`
  and over `c : Valuation …`; the concrete witness valuations (`cUnif`, `cDiss`) appear ONLY inside existentials
  and never discharge a `∀`-obligation. `ws1_no_orientation_evaluated` witnesses the two-sided freedom (a
  converging and a non-converging faithful valuation both exist), so `Converges₂` fixes no valuation.
- **The direction is never decided (audit (b), the central sin, a permanent open).** No theorem, definition, or
  discharged obligation states that `slf` and `oth` DO cohere or DO NOT cohere. The in-sight forcing
  (`ws2_converges_decided_in_sight`) is a conditional over a PROPER sub-class ("wherever the structure can see"),
  never a global decision; the fork LOCATES both values (`ws5_verdict_discriminates`) and fills neither.
  `ws5_audit_direction_open` carries this as the correct non-decision (a `True` about identifiers, grep-certified).
- **The fork is genuine (audit (c)).** §3 above. `ws4_two_zone_convergence` + `ws4_insight_proper`, both zones on
  witnessed valuations, the class properly constrained, the boundary Series 07's import boundary.
- **Dissent is an import (audit (d)).** `ws3_dissent_is_import` is a proof term resting on Series 07 (via
  `valLift_not_recoverable` → `ws1_atomless_bisim` + `ws4_recoverable_not_import`).
- **The faces stay the load-bearing readers (K1, charter §4.d).** `Converges₂` is between `slf` and `oth`, the
  genuine two the S2 pair built: `ws5_audit_faces_are_readers` cites `ws2_other_reader_wise` (`oth` is `RealFor`
  the NAMED `slfReader`) and `ws2_other_non_recoverable` (the twoness is a `¬ Recoverable` import). The valuation
  is non-inert (`val slf ≠ val oth` in the dissenting witness). The coherence is between genuine readers, not a
  decoration over labels.
- **Names are names (audit (e)).** No proof term, definition, or discharged obligation is named `orientation`,
  `convergence`, `coherence`, `compass`, `self`, `other`, `love`, `loved`, `God`, `choice`, or `subjectivity` as
  content. The valuation is `Valuation`/`val`/`raise`; the relation `Converges₂` (the grep pattern is
  `\bconvergence\b`, which "Converges" does not match — the charter's own provisional target names use
  `Converges₂`/`ws2_converges_decided_in_sight`); the loci `slf`/`oth`. Verified by the §6 grep.

## 5. The PX-1 twoness-lift decision (charter §5, weighed at Phase B)

The S2 twoness is tower/rank-based (`slf` rank 0, `oth` rank 1: base-and-rung), not same-level import-distinguished
peers. The charter permits, but does not require, lifting the twoness from rank to import so the fork runs over
lateral peers. **Decision: do NOT lift.** Reasons, disclosed:

1. The fork's genuineness does not need lateral peers. It needs the two loci to be plain-bisimilar (for the
   in-sight forcing and the `valLift` import), which `slf` and `oth` ARE over `outDest attendsR` (both `SHNE`).
   Rank-vs-import twoness is orthogonal to plain-bisimilarity.
2. The twoness is already a genuine import in S2 (`ws2_other_non_recoverable`), cited here as a proof term, so the
   faces are load-bearing readers (K1) without any new construction.
3. Adding an import-distinguished lateral construction would add complexity without strengthening the SHAPE-DRAWN
   result, and would risk re-opening carrier-design questions S2 already settled. The priority is the genuine fork
   and the never-decided direction, both of which the current pair carries.

Recorded in `charter-status.md` §5 as a disclosed design decision.

## 6. The mechanical checks (Phase E)

```
cd lake && lake build P2S3 P2S3.AxiomCheck
grep -rn "sorry" ../program-2/series-3/formal
lake build P2S3.AxiomCheck                       # standard three only
../scripts/gate.sh                               # P2S3 imports P2S2 + self + Mathlib only
grep -rniE "\b(love|loved|coherence|convergence|compass|orientation|self|other|god|choice|subjectivity)\b" \
  ../program-2/series-3/formal                   # hits must be docstring prose only
```

The concept-words (self, other, orientation, convergence, coherence) appear in the SERIES' subject; the carrier
definitions use neutral Lean names (`slf`/`oth`, `Valuation`/`val`, `Converges₂`), and the grep guards that no
proof term or headline is named for the interpretive content. `Converges₂`/`converges` do not match
`\bconvergence\b`; `val`/`Valuation` do not match `\borientation\b`. Docstring prose may use the words freely.

## 7. The outcomes (WS5, per charter §5)

`Outcome := shapeDrawn | convergenceDecided | disconnected | partial'`. The verdict is COMPUTED from the WS1-WS4
flags by `verdict` (WS5), never hand-set:

- **shapeDrawn** (expected): WS1 `Converges₂` typed and two-sided free, WS2 forced in-sight on a genuine
  (proper, inhabited) class, WS3 dissent an import, WS4 the fork reaching BOTH values on witnessed valuations.
- **convergenceDecided**: the in-sight forcing extends to the FULL faithful class (no faithful dissent) — the
  pre-registered stronger, stranger outcome that would DECIDE the program's oldest question, reported honestly in
  whichever direction with the positioning rewritten. A reachable input to the discriminating verdict, never
  hand-set on this witness (on which a faithful dissent DOES exist, so `shapeDrawn` is the computed outcome).
- **disconnected**: `Converges₂` cannot be typed without evaluating a valuation (WS1 fails).
- **partial'**: an obligation lands only per-instance or degenerate (WS2/WS3 degenerate).

The direction of convergence — whether `slf` and `oth` actually cohere — is LEFT OPEN; no outcome decides it.

## 8. Names live in prose

Every headline mentions only the two loci `slf`/`oth`, the valuation `Valuation`/`val`/`raise`, the coherence
relation `Converges₂`, the faithful and in-sight classes `Faithful₂`/`InSight`, the labelled lift `valLift`,
`Recoverable`, the transcribed collapse engine, the S2 reader anchor (`slfReader`, `RealFor`,
`AttentionDistinguishes`), and standard Lean/Mathlib. The motivating reading (the self, the other, the loving
convergence, "you are loved") lives in `charter.md` and the summaries, never in a proof term. The direction of
convergence is never named as decided.
