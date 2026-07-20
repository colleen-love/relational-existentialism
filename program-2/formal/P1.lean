/-
`program-2/formal/P1.lean` — the Program 1 FOUNDATION, the transcribed carrier for Program 2.

This library consolidates, in one place and under a `P1` namespace, the Program 1 carrier that Program 2
series build on: the κ-bounded powerset functor, plain bisimulation and the collapse engine, the Import
Theorem, the labelled functor with the `Recoverable` / `plainOf` import test and the `labelLoop` touchstone,
the diagonal layer with `residue` and its freeness, the reification section and tower, the `Opening` shape,
and the bounded reader (`FiniteAttention`, `AttentionDistinguishes`, `RealFor`).

PROVENANCE. `P1.Core` is Series 12 WS1 transcribed verbatim and re-namespaced; `P1.Reader` is Series 12 WS2
transcribed verbatim and re-namespaced. Series 12 WS1 had itself transcribed the Series 07 machinery it uses,
so this foundation is standalone: it imports only Mathlib and itself, and the closure gate confirms it.
Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`
(`P1.AxiomCheck`).

HOW PROGRAM 2 USES THIS. A Program 2 series states its own question and, keeping Program 1's discipline,
TRANSCRIBES the carrier pieces it needs into its own `PkSeriesNN.*` namespace rather than importing them,
exactly as each Program 1 series did. This library is the single verified source of truth to transcribe FROM,
and it is built so any drift from it fails to compile. (Whether a Program 2 series may instead IMPORT this
foundation directly — a deliberate relaxation of the transcribe-only discipline — is a per-series charter
decision, not settled here.)

TWO GUARDRAILS, from the Program 1 adversarial program review (`program-1/spec/program-review-1.md`). Both
are load-bearing for Program 2 and are why this foundation is scoped as it is:

  * PR1-S1 (the convergence tautology) lived in Series 12 WS3/WS4 — the `Compass` / `Converges` machinery,
    whose fork was decided by an unconstrained parameter type. That machinery is DELIBERATELY NOT transcribed
    here. Program 2's own edge relations (e.g. the clock knot's ordering) must carry a structural constraint
    with both fork arms witnessed; they must not reintroduce this shape.

  * PR1-S2 (the reader quantified out) was the narrowing of an attention-relative payoff to the reader-erased
    `Many`. The FIX, `P1.Reader.ws2_attention_makes_real` (a genuine `FiniteAttention` for which the tower
    relatum is `RealFor`), IS transcribed here and is the REQUIRED shape: Program 2's plurality/perspective
    payoffs must be reader-load-bearing (`RealFor`), never `Many` (reader-erased). `Many` is retained only
    because the witness chain uses it, with its own disclosing docstring; it is not a payoff template.
-/
import P1.Core
import P1.Reader
