# Repository structure — the six roots (handoff XIII)

Every artifact answers one question: **does it diverge per paper, or is it stable-and-shared?**

- **Diverges per paper, or evolves** (axioms A1–A3/D1, theory-specific lemmas) → lives canonically in
  `theory/`; papers **fork a frozen copy**. The freeze is the value: a paper must mean exactly what it meant
  at review.
- **Stable, shared, mathlib-bound** (the traced-SMC machinery, general infrastructure) → lives in
  `foundation/`; papers **import** it. Safe because `foundation` only moves *toward generality* (an eventual
  mathlib PR), which is backward-compatible.

Flow is one-directional: `scratch → theory → paper` for divergent material; `foundation` sits below
everything. **A paper imports only itself + `foundation/`** — never `theory` (it moves), never another paper
(couples fates).

## The roots

| Root | What | Lean namespace | Imports |
|---|---|---|---|
| [`foundation/`](foundation) | stable, mathlib-bound shared infrastructure (traced-SMC typeclass + JSV axioms) | `Foundation.*` | mathlib only |
| [`theory/`](theory) | the living, theory-specific frontier already beyond paper one | `Theory.*` | `theory/` + `foundation/` |
| [`paper-1/`](paper-1) | frozen, self-contained: paper one's spec + kept formal closure | `Scratch.*`, `RelExist.*` | `paper-1/` + `foundation/` |
| [`paper-2/`](paper-2) | the modular self-relation paper (scoped); forked from `theory/` once shipped | `Paper2.*` | `paper-2/` + `foundation/` |
| [`scratch/`](scratch) | live staging | (free) | `foundation/` + `theory/` |
| [`archive/`](archive) | frozen, superseded/set-aside; cross-links unmaintained | (as moved) | not built |

Each root holds its own `formal/` (Lean) and `spec/` (prose). The lake package and the mathlib cache stay in
[`formal/`](formal); libraries reach each root via `srcDir = "../<root>/formal"` (see
[`formal/lakefile.toml`](formal/lakefile.toml)). `paper-1/` keeps the pre-reorg module names (`Scratch.*`,
`RelExist.*`) so its content is byte-identical; `theory/` is root-prefixed (`Theory.*`) so the four shared
modules it forked do not collide with paper-1's originals.

## Fork-and-freeze, applied lazily

The fork-and-freeze is **not** materialized eagerly. Today `paper-1/` is the **canonical home of its own
closure**; `theory/` holds only what is genuinely already *not* paper one, and **forks forward on demand** —
when a `theory/` module gains a real second consumer of a paper-1 lemma, *that* lemma is forked to `theory/`
(frozen), and the two may then diverge. Four modules have been forked so far
(`Theory.{We,RotatingSpectrum,BandCoincidence,BandFromAxioms}`, consumed by `Priority`/`MutualCoupling`); the
other ~14 paper-one modules have no `theory/` consumer and are **not** duplicated. The eager 22-module
duplication is deliberately deferred until paper two's construction makes specific forks load-bearing.

Provenance / drift notes: [`paper-1/spec/AXIOM-PROVENANCE.md`](paper-1/spec/AXIOM-PROVENANCE.md),
[`theory/spec/PROVENANCE.md`](theory/spec/PROVENANCE.md).

## Cross-paper dependency: cite, don't import

Paper two depends on paper one's *theory* and on its *headline result* (the arrow) as a **cited** prior
result — honored in prose ("by the arrow result of paper one") and through the shared `theory/`/`foundation/`
layers, **never** by a directory import. If a `paper-1/` result turns out to be needed by `paper-2/`, that is
the signal it was never paper-one-specific: hoist it to `theory/` and let both fork it. Citation couples
nothing; import couples fates.

## Gates

[`scripts/gate.sh`](scripts/gate.sh) enforces the closure mechanically (resolution by file location):

- **Closure:** `paper-1/` imports only `Scratch.*`/`RelExist.*`/`Foundation.*`; `paper-2/` only
  `Paper2.*`/`Foundation.*`. Any other cross-root import out of a paper is a leak.
- **Theory:** `theory/` imports only `Theory.*`/`Foundation.*`; references no paper.
- **Foundation:** `foundation/` imports only `Foundation.*` (+ mathlib).

Build: `cd formal && lake build Foundation Paper1 Theory` (green). `lake build` alone builds `Foundation`
(fast, dependency-free, mathlib not triggered).

## mathlib destiny of `foundation/`

`foundation/` is mathlib-*staging*, not yet a PR: the traced-SMC formalization needs more work (generality,
removing bespoke assumptions, matching conventions) before it can be contributed. The matrix `TracedSMC`
*instance* (currently in `paper-1`'s `Scratch.MatrixModel`) is hoisted here **later**, with that
generalization pass — not in this move-only reorg. Its own root makes its different lifecycle explicit: it is
the part that will eventually *leave* the repository.
