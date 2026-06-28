# Repository structure — the six roots (handoff XIII)

Every artifact answers one question: **does it diverge per paper, or is it stable-and-shared?**

- **Diverges per paper, or evolves** (theory-specific lemmas) → lives canonically in `theory/`; papers
  **fork a frozen copy**. The freeze is the value: a paper must mean exactly what it meant at review.
  **(Amended by handoff XX for the axioms — see "The axioms are one canonical layer" below.)**
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
| [`paper-2/`](paper-2) | the modular self-relation paper; the modular slice forked frozen from `theory/` | `Paper2.*` | `paper-2/` (+ `foundation/`; mathlib-direct) |
| [`scratch/`](scratch) | live staging | (free) | `foundation/` + `theory/` |
| [`archive/`](archive) | frozen, superseded/set-aside; cross-links unmaintained | (as moved) | not built |

Each root holds its own `formal/` (Lean), `spec/` (prose), and `README.md`. The Lake package and the mathlib
cache live in the infrastructure directory [`lake/`](lake) (renamed out of its old collision with the per-root
`formal/`, so `formal/` now only ever means "a root's Lean sources"); the libraries reach each root via
`srcDir = "../<root>/formal"` (see [`lake/lakefile.toml`](lake/lakefile.toml)). `paper-1/` keeps the pre-reorg
module names (`Scratch.*`,
`RelExist.*`) so its content is byte-identical; `theory/` is root-prefixed (`Theory.*`) so the four shared
modules it forked do not collide with paper-1's originals.

## Roots vs. infrastructure

The convention is exact: **a root is a top-level directory with `formal/` + `spec/` + `README.md`**, governed
by the import gates. Anything at top level without that shape is **infrastructure**, not a root.

- **Roots (6):** [`foundation/`](foundation), [`theory/`](theory), [`paper-1/`](paper-1),
  [`paper-2/`](paper-2), [`scratch/`](scratch), [`archive/`](archive).
- **Infrastructure (not roots):** [`lake/`](lake) — the Lean package home + mathlib cache (so `formal/` only
  ever names a root's Lean sources); [`agda/`](agda) — the parallel coinductive ν-layer, a *second* proof
  assistant; [`papers/`](papers) — the final manuscripts (all-rights-reserved); [`scripts/`](scripts) — the
  gate and environment setup; and the top-level docs ([`README.md`](README.md), this file, the licenses).

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

## The axioms are one canonical layer (handoff XX — reverses the per-paper freeze, for the axioms)

The fork-and-freeze above protected a per-paper **A3 divergence**: paper one read A3 as the synchronic
eigenform `νΦ_c`, paper two as phase-bearing/modular, paper three as generative — three "readings" that a
frozen copy kept from contaminating one another. **Handoff XX collapsed that divergence.** Reframing **A3 as
a process** — *relations co-direct attention asymmetrically in the relata*, with per-relatum capacity `α`,
the self its **derived** fixed point — makes the three readings **consequences of one process**, proved as
theorems in the canonical axiom layer [`theory/Theory/Axioms.lean`](theory/formal/Theory/Axioms.lean) (prose:
[`theory/spec/AXIOMS.md`](theory/spec/AXIOMS.md)). With the divergence gone, the axioms `{A1, A2, A3, D1}` are
**one canonical, stable, version-pinned layer**, not per-paper forks.

**This reverses spec XIII's per-paper frozen duplication — correctly, because the divergence the duplication
protected is now gone.** The mechanism shifts from *duplication* to **version-pinning**:

- `Theory.Axioms` is a **stable shared layer** (like `foundation/`): it changes **only backward-compatibly**
  (generalization, never redefinition), so a paper's pinned version keeps meaning what it meant.
- Each paper **pins** the canonical-layer commit it was proved against, in its
  `spec/AXIOM-PROVENANCE.md`. The closure gate ([`scripts/gate.sh`](scripts/gate.sh)) now allows a paper to
  import `Theory.Axioms` (only that module, not arbitrary `Theory.*`) and checks the pin.
- **The four `theory/` axiom-base forks** (`We`, `RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`) are
  now *confirmed* non-divergent — their byte-identity with paper one's `Scratch.*` is the **content** of the
  collapse, not a coincidence awaiting divergence.
- **Namespace exception (paper one).** The XIII forks carry paper-one's own `RelExist.*` namespace (so they
  stay byte-identical), which *blocks* a literal `import Theory.Axioms` into paper one (the transitive
  `Theory.*` forks collide with `Scratch.*`). Paper one therefore keeps its byte-identical forks as the
  version-pinned copy and consumes the canonical layer by **citation + pin** (re-proving the eigenform's
  state-half locally in [`Scratch.CanonicalEigenform`](paper-1/formal/Scratch/CanonicalEigenform.lean)) — the
  same citation discipline by which paper two cites paper one's arrow.

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

Build: `cd lake && lake build Foundation Paper1 Theory Paper2` (green). `lake build` alone builds
`Foundation` (fast, dependency-free, mathlib not triggered).

## mathlib destiny of `foundation/`

`foundation/` is mathlib-*staging*, not yet a PR: the traced-SMC formalization needs more work (generality,
removing bespoke assumptions, matching conventions) before it can be contributed. The matrix `TracedSMC`
*instance* (currently in `paper-1`'s `Scratch.MatrixModel`) is hoisted here **later**, with that
generalization pass — not in this move-only reorg. Its own root makes its different lifecycle explicit: it is
the part that will eventually *leave* the repository.
