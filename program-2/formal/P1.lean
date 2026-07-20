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

HOW PROGRAM 2 USES THIS. Program 2 PERMITS importing this foundation directly — a deliberate, recorded
relaxation of Program 1's transcribe-only discipline. A Program 2 series may `import P1` (or `import P1.Core` /
`import P1.Reader`) and use the carrier under its `P1.Core.*` / `P1.Reader.*` names, rather than transcribing
it into the series namespace. This is sound precisely because the foundation is built and axiom-checked here:
importing a verified library cannot introduce a gap, and it removes transcription drift as a failure mode.
Transcription remains available where a series deliberately wants to restate a result at its own strength (as
each Program 1 series did), but it is no longer required. The closure gate for a Program 2 series therefore
allows imports of `P1.*` and the series' own roots (plus Mathlib), and nothing else — importing any OTHER
series' tree is still forbidden. What a series must still supply itself: its own question, its own new
structure (the tick, the stream, the orders), and its own theorems; the foundation is the floor, not the work.

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
