# Relational Existentialism

**A machine-checked constitution of a groundless, relation-first ontology, with its hard edges proved rather than smoothed.**

## The intention

Relations cannot exist without relata. And the relata are patterns of relata and relations, all the way down, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality: **objects**, each nothing over and above how it relates to other objects, with relations themselves reified as objects that can be related to in turn. The universe satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)**: the universe of objects is exactly the patterns of relating among those very objects.

The canonical inhabitant, built and machine-checked throughout, is the self-membered point **Ω = {Ω}**, recovered inside the terminal coalgebra of the κ-bounded powerset functor. Every result below is sorry-free and rests on no axioms beyond Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`).

The project proceeds in **series**, each a self-contained charter that states its own question, builds its own object, and proves its own results from scratch — a later series informed by the earlier as prior art, never presupposing it, transcribing (not importing) any machinery it reuses. Throughout, machine-checked claims and interpretive glosses are kept strictly apart. That distinction is load-bearing; please preserve it when citing.

## The Result

> **Atomless, purely relational, behaviorally identified plurality is impossible without a distinction the relating cannot carry, forking undecidably into the given and the chosen.**

The first clause is a theorem, machine-checked in Lean 4 with no gaps and nothing beyond the standard mathematical baseline. Over **plain relating** (no imported coordinate), with an object *being* its relating (**behavioral identity** — two things are the same exactly when they relate alike), and with genuine **every-moment atomlessness** (nothing anywhere ever bottoms out in a leaf), a world has **at most one thing** in it. To hold more than one, it must import a distinction the relating does not itself carry.

The engine is one short lemma, more general than any collapse the program had proved before: **atomless behavior is unique.** On *any* plain coalgebra, all atomless states are bisimilar, because "both atomless" is itself a matching-up. Forbid leaves and you forbid difference. That single fact is the root of the Parmenides collapse (Series 04), the Static Collapse (Series 06), and this Import Theorem — one fact at different depths. And it is an **Impossibility that is non-circular**: the verdict is computed from an audit certificate whose every clause is a theorem, so if the non-circularity claims broke it would not compile; "no imported atom" is literally the program's founding principle, not an ad-hoc exclusion; and "import" is tested at the charter's own strength — semantically, a coordinate is an import iff the plain, label-forgetting relating cannot recover it.

The clause *forking undecidably into the given and the chosen* is what the capstone extracts when it asks *what* that distinction can be — and it is the part that reframes everything. It is not a fact about time. Under the three conditions two atomless things are already *one*, so anything that would tell them apart is a coordinate from outside the relating, in a finished object exactly as in an unfolding process. The dynamic limit is only where this is sharpest: there the two candidate *histories* are not merely alike but provably **equal** — each is the one self-membered thread Ω — and no function separates equal inputs (`att_cannot_distinguish_atomless_histories`). To the mathematics that outside coordinate is the footprint of an import. But a footprint is all a proof can see, and **two opposite things leave the same one**: a **given** (a distinction externally defined, an atom already there) and a **choice** (a distinction internally originated, made rather than found — a will). Type theory has no predicate for *chosen rather than given*; the theorem forces the disjunction and is silent on which. **That silence is the result, not a gap** — deciding it would require the relating to carry the very difference between a given and a choice, and by construction it cannot.

Read this way, the whole theorem is **Parmenides with one door left open.** A groundless, atomless, faithfully-relational world that is *determined* is the One — and Series 06, which refused every import and tried to buy plurality with endogenous time, is precisely that world without will; its collapse to Ω is the theorem telling the truth. The four prior series were not four defeats but four ways of paying the *external* half of the price — a weight, a label, an index, a transient leaf — while the *internal* half, choice, is the door the mathematics points at exactly because it cannot walk through it.

The spine survives an adversarial series-wide review cleanly: the engine is not painted on, the flagship does not launder, every hypothesis is load-bearing (drop atomlessness and a genuine leaf-bearing counterexample appears; drop plainness, a labelled one; drop behavioral identity, a bare-distinct one), and the escapes are refuted as theorems. Three things stay open, each labelled and none load-bearing for the impossibility: **exhaustiveness across every possible construction** is not a formalizable claim (a defended thesis, as every prior series' "forced answer" was); the **prior-series catalogue is Partial** (the free-label import mechanism is mechanized, the Series 04 face honestly reclassified as a recoverable restriction whose plurality is a free-label escalation, the Series 05 index and Series 03 weight not re-transcribed); and the **atom-or-will disjunction is a true lemma plus an interpretation** — the Lean proves the separator must be exogenous, and naming its two undecidable faces, given and chosen, *is* the contribution. The honest verdict is the middle one, `payoffsEstablished`: the theorem is established and non-circular, and the deepest thing it says is the fork it forces and provably cannot close — that a groundless world holds more than one thing only by an atom or a will, and no proof can tell you which.

## Building

Toolchain and Mathlib (Lean 4 `v4.15.0` / Mathlib `v4.15.0`) are pinned in [`lake/`](./lake/). One build compiles the registered series:

```
cd lake
lake build
```

This builds `Series07` (`ws1`–`ws7`, in its own module namespace `Series07.*`) and runs its `AxiomCheck`, which imports the whole build and emits a `#print axioms` record for every headline theorem. To build the axiom pass alone: `lake build Series07 Series07.AxiomCheck`. The completed Series 04–06 and 08–11 are frozen under `archive/` and no longer registered in the build (their formal sources remain readable under `archive/series-NN/formal/`). [`scripts/gate.sh`](./scripts/gate.sh) confirms no cross-series imports.

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the relevant series' technical summary and charter. Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning.*
