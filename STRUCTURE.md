# Repository structure — the roots (handoff XIII, reorganized in XXI, papers rotated in I.O)

> **The proof DAG is the file structure** (handoff XXI). Each Lean file is one **node** (a result); the
> `import` edges are the "uses" edges; walk imports back from a headline and you read its proof. The node
> inventory — every node, its `A/F/T0/T1/T2/T3` number, its address — is
> [`theory/spec/NODES.md`](theory/spec/NODES.md).

> **The papers rotated (handoff I.O).** A new foundational **paper one** — *a self arises from the axioms* —
> goes at the front as a **skeleton** (`paper-1/`: spec stubs + an empty `Paper1` Lean root, theorems
> deferred to the formalization pass). The old paper one (time / arrow / energy / seam) is now **paper two**
> (`paper-2/`); the old paper two (modular / thermal time) is now **paper three** (`paper-3/`); and the
> conservation frontier in `scratch/` is now **paper four**. Module names were left unchanged where content
> did not move (`paper-2/` is still `Scratch.*`/`RelExist.*`), so the rotation changed no proof — only the
> old paper-two namespace moved in lockstep with its folder, `Paper2.* → Paper3.*`.

Every artifact answers one question: **is it stable-and-shared, or is it this-paper's-own?**

- **Stable and shared** → lives in a stable layer that papers **import**: `foundation/` (substrate,
  mathlib-bound) or `theory/` (the axioms + the `T0.x` theorems imported by ≥2 papers). Safe because both
  change **only backward-compatibly** (generalization, never redefinition), so a paper's pinned version keeps
  meaning what it meant.
- **This-paper's-own** (`T<paper>.x` — e.g. `T2.x`, `T3.x`) → lives in the paper root; promotes to `theory/`
  (`T0.x`) the day a **second paper's Lean imports it**, never by narrative feel.

Flow is one-directional: `scratch` (the living frontier) `→ theory → paper`; `foundation` sits below
everything. **A paper imports only itself + `theory/` + `foundation/`** — never another paper (citation, not
import, couples nothing). Papers **pin** the `theory/` commit they were proved against in
`<paper>/spec/04-provenance.md`.

## The roots

| Root | What | Lean namespace | Imports |
|---|---|---|---|
| [`foundation/`](foundation) | stable substrate: traced-SMC typeclass + JSV axioms, the matrix arena, the partial-trace operation | `Foundation.*` (`RelExist.*` ns) | mathlib only |
| [`theory/`](theory) | **stable shared layer** (transitional): the canonical axioms + the `T0.x` theorems | `Theory.*` | `theory/` + `foundation/` |
| [`paper-1/`](paper-1) | **skeleton** (paper one, *a self arises from the axioms*): spec stubs + empty root, `T1.x` deferred | `Paper1.*` (empty) | `paper-1/` + `theory/` + `foundation/` |
| [`paper-2/`](paper-2) | thin layer: paper two's own `T2.x` (seam, lived identity, the arrow) | `Scratch.*`, `RelExist.*` | `paper-2/` + `theory/` + `foundation/` |
| [`paper-3/`](paper-3) | thin layer: paper three's own `T3.x`; imports the modular slice from `theory/` | `Paper3.*` | `paper-3/` + `theory/` + `foundation/` |
| [`scratch/`](scratch) | **the living frontier** (paper four: `Conservation` + the generative engine + seeds) | (free) | `foundation/` + `theory/` |
| [`archive/`](archive) | frozen, superseded/set-aside; cross-links unmaintained | (as moved) | not built |

Each root holds its own `formal/` (Lean), `spec/` (prose), and `README.md`. The Lake package and the mathlib
cache live in the infrastructure directory [`lake/`](lake), so `formal/` only ever means "a root's Lean
sources"; the libraries reach each root via `srcDir = "../<root>/formal"` (see
[`lake/lakefile.toml`](lake/lakefile.toml)). `theory/` is uniformly `Theory.*` (handoff XXI normalized its
namespaces off the old `RelExist.*`), so a paper imports the shared `T.x` with **clean `Theory.*` names** and
no collision — the spec-XX namespace block is gone.

## Roots vs. infrastructure

The convention is exact: **a root is a top-level directory with `formal/` + `spec/` + `README.md`**, governed
by the import gates. Anything at top level without that shape is **infrastructure**, not a root.

- **Roots (7):** [`foundation/`](foundation), [`theory/`](theory), [`paper-1/`](paper-1),
  [`paper-2/`](paper-2), [`paper-3/`](paper-3), [`scratch/`](scratch), [`archive/`](archive).
- **Infrastructure (not roots):** [`lake/`](lake) — the Lean package home + mathlib cache (so `formal/` only
  ever names a root's Lean sources); [`agda/`](agda) — the parallel coinductive ν-layer, a *second* proof
  assistant; [`papers/`](papers) — the final manuscripts (all-rights-reserved); [`scripts/`](scripts) — the
  gate and environment setup; and the top-level docs ([`README.md`](README.md), this file, the licenses).

## Theory becomes stable; scratch becomes the frontier (handoff XXI — reverses XIII)

Spec XIII made `theory/` the **living frontier** and had papers **fork frozen copies** of the slices they
needed. Handoff XXI **reverses that role**, because papers are now thin layers that *import* `theory/`: for a
paper's pinned version to keep meaning what it meant, **`theory/` must be stable** (backward-compatible
changes only, like `foundation/`). So:

- **`theory/` is now stable** — the canonical axioms + the `T0.x` theorems, changed only by generalization.
- **`scratch/` is now the living frontier** — paper four (`Conservation`, the generative engine, + seeds)
  develops here.
- **The forks are unified.** The band layer (`RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`) was
  genuinely double-imported (paper-2 **and** paper-3), so it promoted into clean `Theory.*` and both papers
  now **import** it. The old modular paper's six forks are gone — it imports `theory/`'s modular slice. The
  arrow paper dropped its three band forks. Each unification was **drift-checked byte-identical first**, so it
  shifted no meaning, and the arrow paper's headline footprints were diffed identical to pre-reorg at the
  checkpoint.
- **What stays `T2.x`** (single-importer today): the seam spine, lived identity, knowing-is-lossy, and the
  arrow. They promote the day a second paper's Lean imports them — not by feel. `Theory.We` is a deliberate
  byte-identical fork of the arrow paper's lived-identity `We`, kept because `theory/`'s `Priority`/`Axioms`
  need it and `theory/` cannot import a paper.

**`theory/` stays a transitional shared layer (handoff I.O).** The rotation did **not** dissolve `theory/`
into the papers. It remains the one canonical home of the shared axioms + the double-imported `T0.x`
theorems, exactly because the band layer and the axioms are genuinely imported by **both** content papers
(paper two and paper three): collapsing it would force one paper to import the other, breaking closure.
Dissolution — folding each `T0.x` node back into the single paper that will ultimately own it, once the
new paper-one (`T1.x`) is written and the true ≥2-importer set is known — is **deferred to the formalization
pass**. Until then `theory/` is the transitional shared layer, held to the same backward-compatible-only
discipline as `foundation/`.

Provenance / drift notes: [`theory/spec/NODES.md`](theory/spec/NODES.md) (the node inventory),
[`paper-2/spec/04-provenance.md`](paper-2/spec/04-provenance.md),
[`paper-3/spec/04-provenance.md`](paper-3/spec/04-provenance.md),
[`theory/spec/PROVENANCE.md`](theory/spec/PROVENANCE.md).

## The axioms are one canonical layer (handoff XX — reverses the per-paper freeze, for the axioms)

The fork-and-freeze above protected a per-paper **A3 divergence**: the arrow paper read A3 as the synchronic
eigenform `νΦ_c`, the modular paper as phase-bearing/modular, the conservation frontier as generative — three
"readings" that a frozen copy kept from contaminating one another. **Handoff XX collapsed that divergence.** Reframing **A3 as
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
  `spec/04-provenance.md`. The closure gate ([`scripts/gate.sh`](scripts/gate.sh)) now allows a paper to
  import `Theory.Axioms` (only that module, not arbitrary `Theory.*`) and checks the pin.
- **The band-layer forks were unified (handoff XXI).** `RotatingSpectrum`, `BandCoincidence`, `BandFromAxioms`
  were genuinely double-imported, so they promoted to one canonical `Theory.*` copy that **both papers import**;
  the arrow paper (now paper two) dropped its `Scratch.*` band forks. `Theory.We` remains a deliberate
  byte-identical fork of its lived-identity `We` (theory's `Priority`/`Axioms` need it and theory cannot
  import a paper).
- **Namespace collision — resolved (XXI), workaround deleted (XXII).** The spec-XX collision that once blocked
  `import Theory.Axioms` into the arrow paper (the `theory/` forks shared its `RelExist.*` names) was
  dissolved when XXI normalized `theory/` to clean `Theory.*`. That paper now imports the shared `Theory.*`
  directly and cites `Theory.Axioms.eigenform_of_fixed`; the XX-era local mirror `Scratch.CanonicalEigenform`
  was deleted in XXII (redundant, footprint-gated).

## Cross-paper dependency: cite, don't import

Paper three depends on paper two's *theory* and on its *headline result* (the arrow) as a **cited** prior
result — honored in prose ("by the arrow result of paper two") and through the shared `theory/`/`foundation/`
layers, **never** by a directory import. If a `paper-2/` result turns out to be needed by `paper-3/`, that is
the signal it was never paper-two-specific: hoist it to `theory/` and let both fork it. Citation couples
nothing; import couples fates.

## Gates

[`scripts/gate.sh`](scripts/gate.sh) enforces the closure mechanically (resolution by file location):

- **Closure:** `paper-1/` (skeleton) imports only `Paper1.*`/`Foundation.*` (+ `Theory.*`); `paper-2/` only
  `Scratch.*`/`RelExist.*`/`Foundation.*`; `paper-3/` only `Paper3.*`/`Foundation.*` (+ `Theory.*`). Any
  other cross-root import out of a paper is a leak.
- **Theory:** `theory/` imports only `Theory.*`/`Foundation.*`; references no paper.
- **Foundation:** `foundation/` imports only `Foundation.*` (+ mathlib).
- **Scratch:** the free workbench is **exempt** — it may import any paper until the paper-four promotion.

Build: `cd lake && lake build Foundation Paper1 Paper2 Theory Paper3` (green). `lake build` alone builds
`Foundation` (fast, dependency-free, mathlib not triggered).

## mathlib destiny of `foundation/`

`foundation/` is mathlib-*staging*, not yet a PR: the traced-SMC formalization needs more work (generality,
removing bespoke assumptions, matching conventions) before it can be contributed. The matrix `TracedSMC`
*instance* (currently in `paper-2`'s `Scratch.MatrixModel`) is hoisted here **later**, with that
generalization pass — not in this move-only reorg. Its own root makes its different lifecycle explicit: it is
the part that will eventually *leave* the repository.
