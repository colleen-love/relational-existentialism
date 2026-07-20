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

HOW PROGRAM 2 USES THIS. Program 2 relaxes Program 1's transcribe-only discipline into a LAYERED IMPORT CHAIN,
`P1 → S0 → S1 → S2 → S3`, each series importing the one before it. This foundation is the base of the chain:
it enters the Program 2 build EXACTLY ONCE, through Series 0 (`program-2/series-0`, namespace `P2S0`), which
`import P1`s it and re-seats its κ-free machinery on the attention carrier (relating is finite attending).
Downstream series import their predecessor (S1 imports S0, and so on) and reach `P1.Core.*` / `P1.Reader.*`
TRANSITIVELY — they do NOT import P1 directly, so all Program 1 machinery stays mediated by S0's ground and
nothing reaches behind it to the raw κ-bounded carrier. This is sound because every layer is built and
axiom-checked before the next imports it: importing a verified layer cannot introduce a gap, and it removes
transcription drift as a failure mode. The closure gate for each series allows its predecessor(s) in the chain
and its own roots (plus Mathlib), and forbids reaching outside the chain.

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
