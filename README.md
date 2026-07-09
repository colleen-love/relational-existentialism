# Relational Existentialism

**A machine-checked constitution of a groundless, relation-first ontology, with its hard edges proved rather than smoothed.**

## The intention

Relations cannot exist without relata. And the relata are patterns of relata and relations, all the way down, with no atom.

This repository makes that position mathematically exact and mechanizes it in Lean 4. There is one layer of reality: **objects**, each nothing over and above how it relates to other objects, with relations themselves reified as objects that can be related to in turn. The universe satisfies a single fixed-point equation:

> **Ω ≅ F(Ω)**: the universe of objects is exactly the patterns of relating among those very objects.

The object actually built and machine-checked — sorry-free and on no axioms beyond Mathlib's standard three — is the terminal coalgebra of the κ-bounded powerset functor, with the canonical self-membered inhabitant `Ω = {Ω}` recovered inside it.

The project proceeds in **series**, each a self-contained charter that states its own question, builds its own object, and proves its own results from scratch — the later series informed by the earlier as prior art, never presupposing it. Throughout, machine-checked claims and interpretive glosses are kept strictly apart. That distinction is load-bearing; please preserve it when citing. Two series are live below: **Series 4** (restriction-quality) and **Series 5** (stratification-as-boundlessness).

---

## Series 4 findings — quality from inside the relata

Series 4 studies **restriction-quality**: the proposal that the quality distinguishing two objects — what lets a world of pure relation hold more than one thing without any atom at the bottom — should be drawn from *inside* the relata (the part each turns toward another, its **face**), not imported from an external algebra.

The founding motivation is a theorem proved first — **the Parmenides collapse.** In the plain, gradeless world, "no atoms" forces "exactly one thing": any two atomless objects are provably equal. A groundless, ungraded relation admits exactly One. So plurality *requires* a second currency of difference — quality — and the imported kind quietly smuggles an atom back in (a zero-quality relation is a relation to nothing). Restriction-quality is the repair that imports nothing.

**What restriction-quality genuinely delivers, machine-checked:**

- **Plurality without atoms.** On a self-contained labelled carrier, two objects that never bottom out in an atom are told apart purely by the face each turns toward a shared neighbour — the plurality the plain world forbids, recovered.
- **Composition that never leaks.** A real composition operator builds relations from relations, and the quality never drains to the empty object — *unconditionally*, with no side-condition. Because the quality is internal, there is no external zero to reach. This is strictly stronger than a weighted (imported-quality) construction, which genuinely leaks.
- **A second, coinductive incompleteness.** The self-relating point Ω faces all of itself yet is self-membered, so its self-portrait is complete in extent but closed at no finite depth — the intuition that *the self is a paradox*, made a theorem.

And two commitments hold as **impossibility theorems**, which is what the philosophy predicted and wanted: global groundlessness is incompatible with plurality (insist that *nothing anywhere* bottoms out and the world collapses to a point), and the imported-weight leak is located exactly at zero-divisors.

**The load-bearing negative.** The charter's central bet was that internal faces would also make the world **bound and position itself from within**. Two rounds of adversarial review established, and the Lean records honestly, that this is **not** delivered on the present carrier: *no-top* is a plain cardinality wall (a thing's relations are fewer than the world is large), not a face-counting one — the proof goes through with faces stripped out, and faces provably *cannot* supply the bound. *No-view-from-nowhere* is true by definition, carrying no force. And the grand unification is a **conjunction** of the payoffs, not a derivation from one finitude.

So the genuine result of Series 4 is a sharp localization: **where faces do local, constructive work — distinguish, compose, resist collapse — the results are solid; where the charter wanted faces to do totality-work — bound, position, unify — the mathematics substitutes a cardinality fact or a bare definition, and on this carrier it provably cannot do otherwise.** Drawing that line precisely is the contribution.

---

## Series 5 findings — boundlessness by refusing to be one world

Series 5 takes up exactly the totality-work Series 4 could not do, from a new direction. Its question: **can a relational world be genuinely *boundless* — no top, no size imposed from outside — while still holding more than one thing?**

The motivating theorem, again proved first — **the Explosion Dilemma.** A world that tries to be boundless naively explodes: on any *single* carrier, boundless-and-plural is unsatisfiable — you either fix a size from outside (a wall, not the world's own grain) or demand groundlessness everywhere and collapse to a point again. Naive boundlessness is not too big; it is *unbuildable*.

The repair is to stop building a world and build a **tower**: a directed system of levels, each honestly bounded in its own grain, arranged with **no first level and no last level**, with the world taken as the colimit and objects relating *across* the levels. No last level means nothing tops the world and no size caps it; no first level means nothing bottoms it out into atoms. Boundlessness becomes a relation between levels.

**What stratification genuinely delivers — including the totality result Series 4 could not reach:**

- **The doubly-unbounded tower is genuinely built** — an actual object with a proper-class index that has no first and no last level and cardinals outrunning every cap — and the flagship payoffs hold of *it*, not of an unmet hypothesis.
- **Boundlessness without a wall, earned.** In the tower, no object relates to everything, and this is *forced by no-last-level*: strip that fact out of the proof and it collapses, because the escaping object exists only because there is always a higher level. This is the endogenous "grain, not wall" bound Series 4 proved unreachable on one carrier — here delivered, and it survives the strip test Series 4's no-top failed.
- **Cross-level composition never leaks.** A thing relates to arbitrarily finer things by composing relations down the tower, and the quality never drains to nothing — holding even on a walled tower, so it is a genuinely independent fact.
- **Incompleteness, inherited and extended.** The two Series 4 incompletenesses transport, and the tower adds a new one: no level can survey the whole, since a total survey would need a first or last level and there is neither.

**What the tower does *not* buy, each labelled honestly** (three adversarial passes, the third clean):

- *No view from nowhere* does not earn its face — its content is the no-top result read through an inert wrapper; the gain over Series 4 is that no-top is now forced by no-last-level, not that the facing structure is load-bearing.
- *No first level* is proved about the index, not yet about the built objects (a carrier-level descent is open).
- *Relating-to = being-composed-of* is currently one definition, not a proved identity.
- The cross-level *distributive law* is delivered only as a weaker grade-shift coherence; the genuine law is open, while the matching **impossibility** (no *strict* such law exists) is fully proved.
- *Attention as grade-shift* is **Trivialized** — definable, but not shown to coincide with any independent notion.
- The grand unification is a **conjunction with one genuine derivation**, not a reduction of every payoff to the single fact of double-openness. The honest verdict is the middle one: the payoffs are *established*, but they are not one fact wearing four hats.

So Series 5 is the **mirror image** of Series 4: where Series 4 found a local success and a totality *failure*, Series 5 converts the central totality failure — the endogenous, grain-not-wall bound — into a genuine, machine-checked success, by refusing to be a single carrier; while the further hope that the whole picture reduces to one fact stays an honest conjunction, and the finest cross-level identifications remain open. The Explosion Dilemma is what makes the achievement non-trivial: it proves the bound *cannot* be had on any one carrier, so building the tower is the only way to have it. Locating exactly what stratification earns and what it only relabels is the contribution.

---

## Series 4 (complete)

- **[Plain-language summary](./series-4/summary.md)**: what was asked, what was found, what it means.
- **[Technical summary](./series-4/summary-technical.md)**: status against the success criteria, verification details, and the precise map of what restriction-quality can and cannot do.
- **[Charter](./series-4/charter.md)** and **[charter status](./series-4/charter-status.md)**: the stable program document and its mutable companion.
- **[Formalization](./series-4/formal/)** and **[specs](./series-4/spec/)**: the Lean 4 development (WS1–WS7), design docs, two adversarial reviews, and the committed [axiom-check log](./series-4/spec/axiom-check-log.md).

*Verification:* no `sorry`, no custom axioms; all **41** headline theorems rest only on Mathlib's `propext`, `Classical.choice`, `Quot.sound`. Self-contained — nothing imported from earlier, archived series.

## Series 5 (live)

- **[Plain-language summary](./series-5/summary.md)**: the boundlessness question, the tower, and what it earns versus relabels.
- **[Technical summary](./series-5/summary-technical.md)**: status against the success criteria, the endogenous-bound result, and the honest open ledger.
- **[Charter](./series-5/charter.md)** and **[charter status](./series-5/charter-status.md)**: the stable program document and its mutable companion (open-obligations register, per-workstream status, three review passes).
- **[Formalization](./series-5/formal/)** and **[specs](./series-5/spec/)**: the Lean 4 development (WS1–WS7), design docs, three adversarial reviews, and the committed [axiom-check log](./series-5/spec/axiom-check-log.md).

*Verification:* no `sorry`, no custom axioms; all **43** headline theorems rest only on Mathlib's `propext`, `Classical.choice`, `Quot.sound` (two on none) — machine-run and recorded, regenerated against the addressed build. Self-contained — nothing imported from `series-4/` or `archive/` (confirmed by `scripts/gate.sh`).

### Building

Toolchain and Mathlib are pinned in [`lake/`](./lake/). The lake build targets the live series (Series 5):

```
cd lake
lake build
```

This builds `Series5` (`ws1`–`ws7`) and runs `AxiomCheck.lean`, which imports the whole build and emits a `#print axioms` record for every headline theorem. Series 4 is complete prior art under [`series-4/`](./series-4/). Reproducibility claims in any publication should cite the specific commit hash and a clean-build log.

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the relevant series' technical summary ([Series 4](./series-4/summary-technical.md), [Series 5](./series-5/summary-technical.md)) and charter. Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning.*
