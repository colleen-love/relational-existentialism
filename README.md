# Relational Existentialism

**A machine-checked constitution of a groundless, relation-first ontology, with its hard edges proved rather than smoothed.**

## The intention

Relations cannot exist without relata. And the relata are patterns of relata and relations, all the way down, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality: **objects**, each nothing over and above how it relates to other objects, with relations themselves reified as objects that can be related to in turn. The universe satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)**: the universe of objects is exactly the patterns of relating among those very objects.

The canonical inhabitant, built and machine-checked throughout, is the self-membered point **Ω = {Ω}**, recovered inside the terminal coalgebra of the κ-bounded powerset functor. Every result below is sorry-free and rests on no axioms beyond Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`).

The project proceeds in **series**, each a self-contained charter that states its own question, builds its own object, and proves its own results from scratch — a later series informed by the earlier as prior art, never presupposing it, transcribing (not importing) any machinery it reuses. Throughout, machine-checked claims and interpretive glosses are kept strictly apart. That distinction is load-bearing; please preserve it when citing.

## The arc, in one breath

The program spent six series trying to build a relational world that holds more than one thing without paying for it with an atom, and the seventh proves why it always had to pay.

- **Series 4** told two atomless things apart with a **quality drawn from inside them** — the *face* each turns toward another — because any quality imported from outside smuggles an atom back in. It delivers plurality, leak-free composition, and a coinductive incompleteness; but the hope that internal faces would also make the world *bound itself* fails, and is proved to fail.
- **Series 5** takes up exactly that totality-work from a new direction: stop being one world, and build a **tower of levels** with no first and no last. It genuinely earns the endogenous "grain, not wall" bound Series 4 could not reach — while the grander hope that every payoff reduces to one fact stays an honest conjunction.
- **Series 6** refuses every import — no weight, no label, no level — and tries to buy plurality with **endogenous time**, a diagonal-driven process. The purchase fails: the process collapses to a single point, moment by moment. A sharp negative, honestly reported.
- **Series 7** proves why, in one theorem, and reads the whole program backward. **Atomless plurality is impossible without an import.** The four prior worlds were not four achievements and one defeat; they were four forced payments of a price that was always mandatory.

Each series' motivating engine is itself a proved **impossibility** — the Parmenides collapse (4), the Explosion Dilemma (5), the Static Collapse (6), the Import Theorem (7) — because in this program proving what *cannot* be done is first-class work.

---

## Series 4 — quality from inside the relata

Series 4 studies **restriction-quality**: the quality distinguishing two objects should be drawn from *inside* the relata (the part each turns toward another, its **face**), not imported from an external algebra. The founding motivation, proved first, is the **Parmenides collapse**: in the plain, gradeless world, "no atoms" forces "exactly one thing." So plurality requires a second currency of difference, and the imported kind smuggles an atom back in (a zero-quality relation is a relation to nothing).

**What restriction-quality genuinely delivers, machine-checked:** plurality without atoms (two objects told apart purely by their faces); composition that never leaks (unconditionally, because an internal quality has no external zero to reach — strictly stronger than a weighted construction, which genuinely leaks); and a second, coinductive incompleteness (Ω faces all of itself yet is self-membered — the self is a paradox, made a theorem).

**The load-bearing negative.** The charter's bet that faces would also make the world *bound and position itself from within* is **not** delivered, and the Lean records it honestly: *no-top* is a plain cardinality wall (the proof goes through with faces stripped out, and faces provably cannot supply the bound), *no-view-from-nowhere* is true by definition, and the unification is a **conjunction**, not a derivation. The contribution is the sharp line: **where faces do local work — distinguish, compose, resist collapse — the results are solid; where the charter wanted totality-work — bound, position, unify — the mathematics substitutes a cardinality fact or a bare definition, and on this carrier provably cannot do otherwise.**

## Series 5 — boundlessness by refusing to be one world

Series 5 takes up the totality-work Series 4 could not do: **can a relational world be genuinely boundless — no top, no imposed size — while still holding more than one thing?** The motivating theorem, proved first, is the **Explosion Dilemma**: on any single carrier, boundless-and-plural is unsatisfiable — you either fix a size from outside (a wall) or demand groundlessness everywhere and collapse to a point. Naive boundlessness is not too big; it is *unbuildable*.

The repair: build not a world but a **tower** of levels, each honestly bounded in its own grain, with **no first and no last level**, the world the colimit, objects relating across the levels. **What stratification genuinely delivers — including the totality result Series 4 could not reach:** a genuinely built doubly-unbounded tower (a real object with a proper-class index and cardinals outrunning every cap); **boundlessness without a wall, earned** — no object relates to everything, *forced by no-last-level* (strip that fact out and the proof collapses), the endogenous "grain, not wall" bound Series 4 proved unreachable on one carrier; leak-free cross-level composition; and a new tower-unknowability incompleteness.

**What the tower does not buy, each labelled honestly** (three review passes, the third clean): a face-load-bearing no-view (it is no-top read positionally), a carrier-level no-first-level (proved at the index only), relating-is-composition as a proved identity (one definition), a genuine graded distributive law (a coherence was built; the matching *impossibility* — no strict such law — is fully proved), attention as more than vocabulary (**Trivialized**), and a reduction of all payoffs to one fact (a **conjunction with one derivation**). Series 5 is the mirror of Series 4: it converts the central totality *failure* into a success by refusing to be one carrier, while the unifying hope stays an honest conjunction.

## Series 6 — dynamism as groundlessness, and the collapse that forced the next question

Series 6 refuses all three imports — weight, label, level — and asks whether a world can be **genuinely globally atomless and plural** by becoming a **process** rather than a finished object: a diagonal-driven unfolding where plurality is carried by *endogenous time* and the transition is the residue of a self-survey that (by the Cantor/Lawvere diagonal) can never close. Its motivating theorem, the **Static Collapse**, generalizes Parmenides: any *static* (behaviorally-identified) genuinely-atomless world is a single point; every static plurality is bought by an imported atom.

**What it earns, machine-checked:** the Static Collapse itself (with the escapes diagnosed as imports); a **genuinely diagonal-driven engine** — the successor state IS the Cantor diagonal, the sole definiens, so the engine is not painted on (`ws3_diagonal_drives`); the lossy survey / one-to-many residue and a strict arrow; agreement-is-collapse; and groundlessness-from-the-diagonal and no-view-from-nowhere.

**The central finding is a sharp negative.** On the honestly atom-free stagewise carrier, each finite approximation is *finite*, and hereditary non-emptiness forces a unique value — so **Ω is the unique productive thread** (`ws1_productive_unique`) and genuine atomless plurality is **impossible** (the achievement flips to an Impossibility). The engine is genuine, but the plural world it was meant to carry collapses moment by moment; the endogenous arrow needs an imported depth axis, and the relativity launders. The honest verdict is `payoffsEstablished`, and the collapse — the Static Collapse reaching into every finite approximation — is exactly what set Series 7's question.

## Series 7 — the Import Theorem (the capstone)

Series 7 proves why every prior world had to pay. **Atomless plurality is impossible without an import.** Over plain relating (no imported coordinate), with an object *being* its relating (behavioral identity), and with genuine every-moment atomlessness, a world has **at most one thing** in it. The engine is one short lemma, more general than any prior collapse: **atomless behavior is unique** — on *any* plain coalgebra, all atomless states are bisimilar, because "both atomless" is itself a bisimulation. That single fact is the root of the Parmenides collapse (4), the Static Collapse (6), and the Import Theorem (7); they are one fact at different depths.

The result is an **Impossibility, and — the part that matters — it is non-circular.** The verdict is computed from an audit *certificate* whose every clause is a theorem, so if the non-circularity claims broke, the verdict would not compile. "No imported atom" is literally the program's founding principle, not an ad-hoc exclusion. And "import" is tested at the charter's own strength — *semantically*: a coordinate is an import iff the plain, label-forgetting relating cannot recover it. A genuine labelled world is exhibited whose two atomless things are indistinguishable to the plain relating yet carry different labels — so the label is a real import (dropping *plainness*), distinct from a plain non-reduction killed by the quotient (dropping *behavioral identity*).

**The program is explained** — with a sharpening a second, alignment-focused review forced, which makes the story deeper rather than weaker. The mechanized imports are *free labels*. The Series 4 face, by contrast, is a *restriction of the relatum*, hence recoverable, hence — by the charter's own definition — **not an import**: it is a leaf, a *faced boundary*. So Series 4, the series that imported nothing, reached plurality only by **escalating** its internal restriction into a free external label, and that escalation is the genuine import. The price was still paid — even the internal-quality world paid — just not with the coordinate the charter named. The leftover, a boundary that bottoms out *and* carries a quality, is a fourth kind of difference the leaf/import split does not enumerate, and the seed of a possible Series 8.

**The one real escape** — limit-atomlessness, transient atoms that heal only in a limit the world never reaches — is isolated and adjudicated *import-in-time*. What stays open, each labelled: exhaustiveness across *every possible construction* is not a formalizable claim; the metric family for the loophole is characterized but not built; and the faced-boundary fourth kind and the endogenous prior-series carriers are named opens. Two review passes — one at the level of the proofs and one at alignment-to-charter, with an interim four-reviewer review (a reviewer tasked solely with a counterexample could not build one) discounted between them because, clean as it was, it missed the alignment issue — leave the **plain collapse** at the honest, attack-tested verdict `payoffsEstablished`, with the prior-series catalogue honestly re-classified. The sharpest single thing the program can now say: **a relational world can be atomless, or plural, or faithful to "an object is its relating" over plain relating — any two, never all three** — so every world that holds more than one thing has already paid for it with an atom, and the only freedom is which atom, and whether you are honest that you paid.

---

## The series

Each series is self-contained and machine-verified: no `sorry`, no custom axioms, every headline theorem on Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`), recorded in a committed axiom-check log and regenerated against the addressed build. Each series' formal sources live in their own module namespace (`SeriesN.*`), transcribing any reused machinery so nothing is imported across series (confirmed by [`scripts/gate.sh`](./scripts/gate.sh)).

| Series | Question | Motivating impossibility | Verdict | Docs |
|---|---|---|---|---|
| **4** (complete) | quality from inside the relata (the face) | the Parmenides collapse | local success, totality failure — both proved | [summary](./series-4/summary.md) · [technical](./series-4/summary-technical.md) · [charter](./series-4/charter.md) · [status](./series-4/charter-status.md) · [formal](./series-4/formal/) · [spec](./series-4/spec/) |
| **5** (complete) | boundlessness by refusing to be one world | the Explosion Dilemma | the endogenous bound, earned; unification a conjunction | [summary](./series-5/summary.md) · [technical](./series-5/summary-technical.md) · [charter](./series-5/charter.md) · [status](./series-5/charter-status.md) · [formal](./series-5/formal/) · [spec](./series-5/spec/) |
| **6** (complete) | dynamism as groundlessness (endogenous time) | the Static Collapse | the process collapses; engine genuine — `payoffsEstablished` | [charter](./series-6/charter.md) · [status](./series-6/charter-status.md) · [protocol](./series-6/protocol.md) · [formal](./series-6/formal/) · [spec](./series-6/spec/) |
| **7** (complete) | is atomless plurality impossible without an import? | the Import Theorem | plain collapse holds, non-circular — `payoffsEstablished`; catalogue re-classified | [summary](./series-7/summary.md) · [technical](./series-7/summary-technical.md) · [charter](./series-7/charter.md) · [status](./series-7/charter-status.md) · [formal](./series-7/formal/) · [spec](./series-7/spec/) |

Earlier work (Series 1–3) is frozen under [`archive/`](./archive/) — readable as origin, normative for nothing. Each series' `spec/` holds its design docs, its committed axiom-check log, and its adversarial review passes.

*Verification, per series (the AxiomCheck run emits a `#print axioms` record for every headline theorem, all on the standard three): Series 4 — 42; Series 5 — 48; Series 6 — 44; Series 7 — 45.* A publication should cite the specific commit hash and a clean-build log.

## Building

Toolchain and Mathlib (Lean 4 `v4.15.0` / Mathlib `v4.15.0`) are pinned in [`lake/`](./lake/). One build compiles all four series:

```
cd lake
lake build
```

This builds `Series4`, `Series5`, `Series6`, and `Series7` (each `ws1`–`ws7`, in its own module namespace `SeriesN.*`) and runs each series' `AxiomCheck`, which imports that series' whole build and emits a `#print axioms` record for every headline theorem. To build a single series' axiom pass: `lake build Series7 Series7.AxiomCheck` (and likewise for `Series4` / `Series5` / `Series6`). [`scripts/gate.sh`](./scripts/gate.sh) confirms no cross-series imports.

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the relevant series' technical summary and charter. Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning.*
