# Relational Existentialism

**A machine-checked constitution of a groundless, relation-first ontology, with its hard edges proved rather than smoothed.**

## The claim

Relations cannot exist without relata. And the relata are patterns of relata and relations, all the way down, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality: **objects**, each nothing over and above how it relates to other objects, with relations themselves reified as objects that can be related to in turn. The universe satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)**: the universe of objects is exactly the patterns of relating among those very objects.

The object actually built and machine-checked — sorry-free and on no axioms beyond Mathlib's standard three — is the terminal coalgebra of the κ-bounded powerset functor, with the canonical self-membered inhabitant `Ω = {Ω}` recovered inside it.

## What this series proves

Series 4 studies **restriction-quality**: the proposal that the quality distinguishing two objects — what lets a world of pure relation hold more than one thing without any atom at the bottom — should be drawn from *inside* the relata (the part each turns toward another, its **face**), not imported from an external algebra. The founding motivation is a theorem proved first:

- **The Parmenides collapse.** In the plain, gradeless world, "no atoms" forces "exactly one thing": any two atomless objects are provably equal. A groundless, ungraded relation admits exactly One. So plurality *requires* a second currency of difference — quality — and the imported kind quietly smuggles an atom back in (a zero-quality relation is a relation to nothing). Restriction-quality is the repair that imports nothing.

What restriction-quality genuinely delivers, machine-checked:

- **Plurality without atoms.** On a self-contained labelled carrier, two objects that never bottom out in an atom are told apart purely by the face each turns toward a shared neighbour — the plurality the plain world forbids, recovered.
- **Composition that never leaks.** A real composition operator builds relations from relations, and the quality never drains to the empty object — *unconditionally*, with no side-condition. Because the quality is internal, there is no external zero to reach. This is strictly stronger than a weighted (imported-quality) construction, which genuinely leaks.
- **A second, coinductive incompleteness.** The self-relating point Ω faces all of itself yet is self-membered, so its self-portrait is complete in extent but closed at no finite depth — the intuition that *the self is a paradox*, made a theorem.

And two commitments hold as **impossibility theorems**, which is what the philosophy predicted and wanted:

- **Global groundlessness is incompatible with plurality.** Insist that *nothing anywhere* bottoms out and the whole world collapses to a single point. Groundlessness and plurality coexist only locally.
- **The imported-weight leak is located exactly at zero-divisors** — so any external quality with a zero either leaks an atom under composition or is atom-free only by external fiat.

## The load-bearing finding

The charter's central bet was that internal faces would also make the world **bound and position itself from within** — that its finite size would be the world's own grain rather than a fence, and every standpoint genuinely positioned. Two rounds of adversarial review established, and the Lean now records honestly, that this is **not** delivered on the present carrier:

- *No-top* is a plain cardinality wall (a thing's relations are fewer than the world is large), not a face-counting one — the proof goes through with faces stripped out, and faces provably *cannot* supply the bound (they tame quality, not branching).
- *No-view-from-nowhere* is not a real coincidence: "a view is positioned" is true by definition, and its forced partner does not exist.
- The grand unification is a **conjunction** of the payoffs, not a derivation of them from one finitude.

So the genuine result of Series 4 is a sharp localization: **where faces do local, constructive work — distinguish, compose, resist collapse — the results are solid; where the charter wanted faces to do totality-work — bound, position, unify — the mathematics substitutes a cardinality fact or a bare definition, and on this carrier it provably cannot do otherwise.** Drawing that line precisely is the contribution.

Machine-checked claims and interpretive glosses are kept strictly apart throughout. That distinction is load-bearing; please preserve it when citing.

## Series 4 (live)

Start here:

- **[Plain-language summary](./series-4/summary.md)**: what was asked, what was found, what it means.
- **[Technical summary](./series-4/summary-technical.md)**: status against the success criteria, verification details, and the precise map of what restriction-quality can and cannot do.
- **[Charter](./series-4/charter.md)** and **[charter status](./series-4/charter-status.md)**: the stable program document, and its mutable companion tracking every discharge, downgrade, and open obligation.
- **[Formalization](./series-4/formal/)**: the Lean 4 development, workstreams WS1 through WS7. `AxiomCheck.lean` imports the whole build and emits a `#print axioms` record for every headline theorem.
- **[Specs](./series-4/spec/)**: per-workstream design documents, two adversarial project reviews, and the committed [axiom-check log](./series-4/spec/axiom-check-log.md).

### Verification status

- No `sorry` anywhere in the development; no custom axioms. All 41 headline theorems rest only on Mathlib's `propext`, `Classical.choice`, `Quot.sound` — machine-run and recorded in the [axiom-check log](./series-4/spec/axiom-check-log.md).
- The development is **self-contained**: nothing is imported from earlier, archived series.
- Toolchain and Mathlib are pinned in [`lake/`](./lake/). To build:

```
cd lake
lake build
```

Reproducibility claims in any publication should cite the specific commit hash and a clean-build log.

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the [Series 4 technical summary](./series-4/summary-technical.md) and the [charter](./series-4/charter.md). Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning.*
