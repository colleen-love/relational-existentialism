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

---

## The series

Each series is self-contained and machine-verified: no `sorry`, no custom axioms, every headline theorem on Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`), recorded in a committed axiom-check log and regenerated against the addressed build. Each series' formal sources live in their own module namespace (`SeriesN.*`), transcribing any reused machinery so nothing is imported across series (confirmed by [`scripts/gate.sh`](./scripts/gate.sh)).

| Series | Question | Motivating impossibility | Verdict | Docs |
|---|---|---|---|---|
| **04** (complete, archived) | quality from inside the relata (the face) | the Parmenides collapse | local success, totality failure — both proved | [summary](./archive/series-04/summary.md) · [technical](./archive/series-04/summary-technical.md) · [charter](./archive/series-04/charter.md) · [status](./archive/series-04/charter-status.md) · [formal](./archive/series-04/formal/) · [spec](./archive/series-04/spec/) |
| **05** (complete, archived) | boundlessness by refusing to be one world | the Explosion Dilemma | the endogenous bound, earned; unification a conjunction | [summary](./archive/series-05/summary.md) · [technical](./archive/series-05/summary-technical.md) · [charter](./archive/series-05/charter.md) · [status](./archive/series-05/charter-status.md) · [formal](./archive/series-05/formal/) · [spec](./archive/series-05/spec/) |
| **06** (complete, archived) | dynamism as groundlessness (endogenous time) | the Static Collapse | the process collapses; engine genuine — `payoffsEstablished` | [charter](./archive/series-06/charter.md) · [status](./archive/series-06/charter-status.md) · [protocol](./archive/series-06/protocol.md) · [formal](./archive/series-06/formal/) · [spec](./archive/series-06/spec/) |
| **07** (complete) | is atomless plurality impossible without an import? | the Import Theorem | plain collapse holds, non-circular — `payoffsEstablished`; the import forks into externally-defined or internally-chosen | [summary](./series-07/summary.md) · [technical](./series-07/summary-technical.md) · [charter](./series-07/charter.md) · [status](./series-07/charter-status.md) · [formal](./series-07/formal/) · [spec](./series-07/spec/) |
| **08** (complete, archived) | what makes the One many, moving, and layered? | the no-god's-eye theorem (finite perspective) | spine an Impossibility (no god's-eye node); plurality free, dynamics forced, depth = narrowing; conservation **Refuted**, bound is mere boundedness — `perspectiveEstablished` | [charter](./archive/series-08/charter.md) · [status](./archive/series-08/charter-status.md) · [protocol](./archive/series-08/protocol.md) · [formal](./archive/series-08/formal/) · [spec](./archive/series-08/spec/) |
| **09** (complete, archived) | can one self, alone, already be divided? | the diagonal (self-reference cannot close) | spine an **Impossibility, independent of relational identity** (no self-total hold, a Cantor/Lawvere diagonal, not a bisimulation); plurality free from one position, dynamics forced, depth = residue-motion; monotonicity **Refuted**, residue moves not grows — `selfReferenceEstablished` | [summary](./archive/series-09/summary.md) · [technical](./archive/series-09/summary-technical.md) · [charter](./archive/series-09/charter.md) · [status](./archive/series-09/charter-status.md) · [formal](./archive/series-09/formal/) · [spec](./archive/series-09/spec/) |
| **10** (complete, archived) | does reifying relations into relata grow the many? | the reification tower (growth vs bookkeeping) | reified relatum carries its pattern but bisim-embeds into the prior carrier — plain engine sees no growth; **Bookkeeping** (proved), the pre-registered terminus; CLOSE forbidden (a top would be a self-total hold); fold Partial, κ deferred — `bookkeeping` | [summary](./archive/series-10/summary.md) · [technical](./archive/series-10/summary-technical.md) · [charter](./archive/series-10/charter.md) · [status](./archive/series-10/charter-status.md) · [formal](./archive/series-10/formal/) · [spec](./archive/series-10/spec/) |
| **11** (complete, terminal, archived) | is finite attention the reader that makes the many real and the bound that holds the tower? | attention as reader-and-bound | **the bound is real** (no hold holds the whole — the diagonal at tower scale, an Impossibility, κ-free, holding-not-size); **the reader is not** — attention was the free label again, so the many-rescue is **Bookkeeping re-hit**; crown **Partial** floored on the genuine bound — `bookkeepingReHit` | [summary](./archive/series-11/summary.md) · [technical](./archive/series-11/summary-technical.md) · [charter](./archive/series-11/charter.md) · [status](./archive/series-11/charter-status.md) · [formal](./archive/series-11/formal/) · [spec](./archive/series-11/spec/) |

Earlier work (Series 01–06, 08–11) is frozen under [`archive/`](./archive/) — readable as origin, normative for nothing; the completed Series 04–06 and 08–11 live under `archive/series-04/`…`archive/series-06/` and `archive/series-08/`…`archive/series-11/`. Each series' `spec/` holds its design docs, its committed axiom-check log, and its adversarial review passes.

*Verification, per series (the AxiomCheck run emits a `#print axioms` record for every headline theorem, all on the standard three): Series 04 — 42; Series 05 — 48; Series 06 — 44; Series 07 — 50; Series 08 — 29.* A publication should cite the specific commit hash and a clean-build log.

## The arc: Series 07–11

The Series 07–11 arc forms one argument, proved at deepening levels — **the differentiation of the One into the many, and where it runs out.**

- **07 — Parmenides.** A groundless, atomless, *determined*, purely relational world is the One. Symmetric relating cannot differentiate; the only escape is a distinction the relating cannot carry, forking undecidably into the given (an atom) and the chosen (a will).
- **09 — the diagonal.** A self rich enough to refer to itself cannot completely hold itself (`ws1_no_self_total_hold`, a Cantor/Lawvere fixed-point contradiction, machine-verified independent of relational identity). The residue it cannot close on is the first difference — free, and internal to *one* self, so it escapes Series 08's circularity of assuming two.
- **10 — reification.** The gap, made into an object (`reify : F(Ω) → Ω`), grows a tower of relata. But the Series 07 engine merges the new relatum with the old: `Ω_{α+1}` bisim-embeds into `Ω_α`. The plain world cannot see the growth. **Bookkeeping**, proved.
- **11 — attention, and the bound.** A reader that would make the growth real turned out to be the free label again — **Bookkeeping re-hit**. But the same incompletability that opens the gap also *bounds* the tower: no hold holds the whole (the diagonal at tower scale), so the world is held finite from within, κ-free, with no imported wall.

The through-line, proved four times: **a structural feature is shared by every relatum, so it cannot differentiate; and an import is exogenous, so it does not count.** The differentiator that would break the One into a genuine, self-read many is therefore neither — it must be *within* and *non-structural*, an act rather than a property. The diagonal (Series 09) proves the self has exactly one such place: the uncloseable interior where its own structure runs out — the same site where *choice* and the *hard problem of consciousness* have always been said to begin. The program does not fill that site (Series 10 and 11 prove twice that structure cannot fill it); it **sites** it, mechanically, and proves the many must be grounded there if anywhere. That siting — the many bounded from within (earned) but not differentiated from structure alone (the honest edge) — is the terminal result of the arc.

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
