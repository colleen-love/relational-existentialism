# Relational Existentialism

**A machine-checked constitution of a groundless, relation-first ontology, with its hard edges proved rather than smoothed.**

## The claim

Relations cannot exist without relata. And the relata are patterns of relata and relations, all the way down, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality with two kinds of entity: **relations**, which are fundamental, and **objects**, which are patterns of objects and relations and which do the relating. The universe of objects satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)**: the universe of objects is exactly the patterns of relating among those very objects.

The object actually built and machine-checked, sorry-free and on no axioms beyond Mathlib's standard three, is a **bounded reconstruction**: the terminal coalgebra of the κ-bounded powerset functor. The unbounded universe the philosophy first names is proved too big to exist *as a set* (the same wall that forbids a set of all sets); the bounded carrier is what exists, and the canonical self-membered inhabitant `Ω = {Ω}` is recovered inside it.

**Three** of the framework's commitments hold as **impossibility theorems**, which is what the philosophy predicted and wanted: no strict top-down-and-bottom-up master law can exist (composition of relations-as-objects is inherently non-strict); no bounded observer can enumerate its own space of self-descriptions; and — surfaced by an external audit — in the *unlabeled* carrier, atomlessness and plurality are jointly unsatisfiable, so a groundless, ungraded relation admits exactly one point. The convergence of attention, the last dynamical question, is now **stratified** rather than asserted: it provably converges on explicit parameter bands, provably fails to converge uniquely outside them (exact multistable and oscillating witnesses), with the boundary located at a named pitchfork.

The deepest finding is about the enterprise itself: **the bound that lets the object exist as a set is what weakens every sweeping claim about the totality** — and the audit sharpened it, showing that even a *local* commitment (atomlessness) prices against plurality unless the relations carry weights, so genuine plurality has to be bought with grading. No-outer-edge, no-view-from-nowhere, no-collapse-anywhere: each global claim softens exactly where the existence-buying bound is imposed. Whether a class-sized or otherwise unbounded mechanization could recover the global claims is open; within a set-sized, machine-checked carrier, the trade-off is proved.

Machine-checked claims and interpretive glosses are kept strictly apart throughout. That distinction is load-bearing; please preserve it when citing.

## Series 3 (live)

The current work. Start here:

- **[Plain-language summary](./series-3/summary.md)**: what was asked, what was found, what it means.
- **[Technical summary](./series-3/summary-technical.md)**: status against the seven success criteria, verification details, the fracture analysis.
- **[Charter](./series-3/charter.md)**: the program document, with its full revision history (REV-A through REV-G).
- **[Formalization](./series-3/formal/)**: the Lean 4 development, workstreams WS1 through WS10. `AxiomCheck.lean` imports the whole build and emits a `#print axioms` record for headline theorems across every workstream.
- **[Specs](./series-3/spec/)**: per-workstream conceptualize / design / execute / review documents, and an [external audit](./series-3/spec/ws9/03-project-review.md) of the gap between formal statements and prose claims, which WS9 and WS10 address.

### Verification status

- No `sorry` anywhere in the development; no custom axioms. Every headline theorem rests only on Mathlib's `propext`, `Classical.choice`, `Quot.sound`.
- Toolchain and Mathlib are pinned in [`lake/`](./lake/). To build:

```
cd lake
lake build
```

Reproducibility claims in any publication should cite the specific commit hash and a clean-build log.

## Series 2 (closed)

Series 2, including Spec 2.0 and its formalization, is frozen under [`archive/`](./archive/). It remains readable as the origin of the axiom-ledger approach and the Mirror/collapse findings, but it is superseded: Series 3 rebuilt the foundation after review, and nothing in the archive is normative for the live development.

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the [Series 3 technical summary](./series-3/summary-technical.md) and the [charter](./series-3/charter.md). Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning.*
