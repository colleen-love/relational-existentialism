# Relational Existentialism

**A machine-checked mathematical foundation for priority relationalism.**

## The claim

Relations cannot exist without relata. And the relata are patterns of relata and relations, ad infinitum, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality with two kinds of entity: **relations**, which are fundamental, and **objects** — patterns of objects and relations, coalesced with varying degrees of closure — which do the relating. Nothing is eliminated and nothing is atomic. Formally, the universe of objects Ω satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)** — the universe of objects is exactly the patterns of relating among those very objects.

The framework has **one primitive** — observation, which is what relating is: lossy, transmissible witnessing — and **one axiom** governing it. Everything classically asserted about objects (that they exist, self-relate, compose, and are constituted by what they relate to) is *proved*, not posited.

**One primitive, one axiom. Objects are theorems.**

## The spec

The document of record — ontology, arena, axioms, every load-bearing decision with its rationale, theorem targets, and open questions — is:

**[Spec 2.0. — Ontology, Arena, and Axioms](./series-2/2-0.md)**

**[Spec 2.1. — Signature, Dyad Reduction, and Construction of Ω](./series-2/2-1.md)**

**[Spec 2.2. — π Ratified, Witnessing, and Comparative Composition Theory](./series-2/2-2.md)**

**[Spec 2.3. — The Mirror: the Collapse Finding, the F(1) Test, and the Correction Program](./series-2/2-3.md)**

**[Spec 2.4. — The Correction: the Corrected Functor, νF_C, and the Plural Universe](./series-2/2-4.md)**

**[Spec 2.5. — The Naming: D19, the Residue of Self-Reference, and the Closing Theorems](./series-2/2-5.md)** · **[Series 2 — Closing Note](./series-2/series-2-closing.md)**

Reading path for the argument only: §1 (the axioms) → §2.2 (the closure operator: how objects are given by their relations) → §3 (the ledger: what is primitive, what is proved) → theorems T1 and T2 in §5.

Three results to know before diving in:

- **T1 (The One).** Strip observation of all quality and the entire universe provably collapses to a single self-relating point. Without graded observation, nothing distinguishes anything: observation is what individuates. *Not bang, but becoming.*
- **T2 (Objects exist).** Any pattern of relating whatsoever determines, via a unique closure map, exactly one object. Objecthood is emergence made exact — attractor, not axiom.
- **T6 (No ground floor).** The universe has no well-founded elements: decomposition never terminates, and its coherence is machine-checked. As a side effect, this is a formal consistency model for non-well-founded grounding.

## Status

**Series 2 is closed.** The arc ran from the axioms (2.0) through finality and construction (2.1), witnessing and composition (2.2), the Mirror — the collapse *finding* — and the correction program (2.3), the corrected functor and the plural universe νF_C (2.4), to the naming of the one irreducible loss and the closing theorems (2.5). What landed, machine-checked: the universe **exists** (T2), is **many** (the anti-Mirror), is **bridged** (C1 — *we are born as bridges*), its identity is **the limit of observer-local equalities** (T7), and its residue of self-reference (**D19**) is named with every feature proved. What is still owed — chiefly the κ-loan (T11) — walks into Series 3 in the open. The one-page door is the **[Series 2 Closing Note](./series-2/series-2-closing.md)**; open problems and their end-states are in spec 2.5 §7–8.

Contributions and objections are welcome; the spec's decision log (§4) records what has already been weighed, including the strongest objection we know ("you're building this out of objects") and its three-part answer (D12).

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, Agda, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-writing)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

If this work is useful to you, cite the repository and Spec 2.0 until a paper exists. Machine-checked claims are marked as such in the spec; interpretive glosses are labeled as interpretation. That distinction is load-bearing — please preserve it when citing.

---

*Before there was voice, there was turning.*
