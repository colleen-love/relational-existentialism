# Relational Existentialism

**An ungrounded constitution of a relation-first reality — priority relationalism, built and machine-checked in Lean 4 as a bounded reconstruction whose hard edges are proved, not smoothed.**

## The claim

Relations cannot exist without relata. And the relata are patterns of relata and relations, ad infinitum, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality with two kinds of entity: **relations**, which are fundamental, and **objects** — patterns of objects and relations, coalesced with varying degrees of closure — which do the relating. Nothing is eliminated and nothing is atomic. Formally, the universe of objects Ω satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)** — the universe of objects is exactly the patterns of relating among those very objects.

The framework has **one primitive** — observation, which is what relating is: lossy, transmissible witnessing — and **one axiom** governing it. What is classically *asserted* about objects (that they exist, self-relate, compose, and are constituted by what they relate to) is here *proved*.

**And the honest result is sharper than the dream — and better.** The literal, unbounded Ω is proved *too big to exist* as a set (the same wall that forbids a set of all sets). So what is built and machine-checked — sorry-free, on no axioms beyond Mathlib's standard three — is a **bounded reconstruction**: the terminal coalgebra of the κ-bounded powerset functor, inside which `Ω ≅ F(Ω)` genuinely holds and the canonical `Ω = {Ω}` is recovered. Of the seven commitments, six are discharged — **two of them as impossibility theorems** (nothing can completely know itself; there is no strict top-down-and-bottom-up master law) — and the seventh, non-collapse, has its structural half discharged and its dynamical half, the **convergence of attention**, now characterized: it converges on explicit bands, provably fails to converge uniquely outside them, with the boundary a named pitchfork.

The deepest finding is a theorem about the enterprise itself: **the very bound that lets the object exist is what weakens every sweeping claim about the totality.** You can have a relation-first world that genuinely *exists*, or the fully unbounded, no-edges-anywhere version that stays a beautiful idea — the mathematics says not both. That trade-off is the price of existence, and it is machine-checked.

**One primitive, one axiom. Objects are theorems — and the theorems include their own limits.**

## Series 3

**[The Series 3 Summary](./series-3/summary.md)**

**[The Series 3 Technical Summary](./series-3/summary-technical.md)**

**[The Series 3 Charter](./series-3/charter.md)**

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, Agda, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-writing)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

If this work is useful to you, cite the repository and Spec 2.0 until a paper exists. Machine-checked claims are marked as such in the spec; interpretive glosses are labeled as interpretation. That distinction is load-bearing — please preserve it when citing.

---

*Before there was voice, there was turning.*
