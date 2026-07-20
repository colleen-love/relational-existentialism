# Relational Existentialism, Program 2

**A machine-checked, dynamic, purely relational universe of genuinely multiple perspectives — a self and an other, a first tick of time, and the coherence between them — built in Lean 4 with its new wall proved rather than assumed.**

## The premise

Program 1 drew the edge of the One. It proved, machine-checked and axiom-clean, that a groundless, atomless, faithfully-relational world that is *determined* by its relating holds **at most one thing**: to be more than one you must be given a distinction the relating cannot itself carry (the Import Theorem), a distinction whose shape is the diagonal's own residue and whose fit is an adjoint pair with a genuine defect. Program 1 was forbidden to name that distinction, select it, or spend it. It drew the door and left it open.

**Program 2 walks through the door.** It takes the imported differentiator as given — not as a single choice but as an exogenous **stream** of them, quantified over and never named — and asks the next question: *once the distinction arrives, does the relational world become dynamic and populated by genuinely multiple perspectives, a self and an other, and where does the next wall stand?* The method is the one every Program 1 series used: **construct** the dynamic multi-perspective universe relative to the stream, prove the invariants that hold for *every* stream, then **locate** the new impossibility the construction reveals.

This repository makes that program mathematically exact. Every result below is sorry-free and rests on no axioms beyond Mathlib's standard three (`propext`, `Classical.choice`, `Quot.sound`) — several rest on fewer, and the final verdict on none. Throughout, machine-checked claims and interpretive glosses are kept strictly apart. That distinction is load-bearing; please preserve it when citing.

## The four instruments

Program 2 does not forge new machinery. It composes the four tools Program 1 proved, one per tenet, and holds Program 1's discipline exactly — spending the import as a quantified stream and never as a name:

1. **Relata self-reference** (the diagonal) — *"Self is a paradox."* A structure rich enough to inspect itself leaves a residue it cannot capture.
2. **Relational reification** (relations become relata) — *"To relate is to create."* A relation, read, becomes a thing that can be related to in turn.
3. **Relata finite attention** (the bounded reader) — *"To attend is to become."* Each relatum perceives only a limited aspect of itself and its relationships; relating *is* that finite attention.
4. **Symmetry breaking by the import** (chance, choice, subjectivity, or something outside relation) — *"You are loved."* The one thing the relating cannot decide, and Program 2 is still forbidden to fill.

## What we built and proved

Program 2 proceeds in **series**, each a self-contained charter that states its own question, builds its own object, and proves its own results. Program 2 relaxes Program 1's transcribe-only rule into a **layered import chain** — `P1 → S0 → S1 → S2 → S3`, each series importing exactly the one before it, reaching the rest transitively — where every layer is built and axiom-checked before the next imports it, so importing a verified layer cannot introduce a gap and transcription drift is removed as a failure mode. The Program 1 prior art enters the build once, re-seated on Program 2's carrier as the `P1` foundation, with the two Program 1 adversarial traps (a convergence tautology of an unconstrained type; a bounded reader quantified out to a bare "many") deliberately **excluded** behind a guardrail so no series can recreate them.

Each series computes its own verdict — a small function reading which way the construction fell, with the alternatives genuinely reachable, so the reported outcome is an earned output, not a constant.

### Series 2.0 — the ground: *relating is finite attending* (verdict: GROUND-ESTABLISHED)

The carrier the rest of Program 2 stands on. A relatum's out-attention is a **finite set** (`attends : X → Finset X`) — finite attention is the sole bound, with no cardinal ceiling smuggled in — it relates symmetrically to what it attends and what attends it, and it **knows** only what it actively attends. On this ground:

- Reifying a relatum's self-relation yields **the first other**, provably non-recoverable from the plain relating (`ws1_first_other`).
- **The knowing is asymmetric even though the relating is symmetric** (`ws3_direction_not_recoverable`, `ws3_active_passive_distinct`, `ws3_passive_constitution`): a relatum is made differently by what it attends than by what attends it — the unreturned gaze — a load-bearing structural fact the symmetric relating cannot see, not a mere label.
- The import is carried as a quantified ingredient, seated on the ground (`ws4_import_quantified`), and the collapse to the One *without* it is inherited from Program 1 as settled baseline, never relitigated (`ws2_collapse_inherited`).

This is the ground an earlier series aimed at (finite attention as the endogenous bound) and did not reach; here relating *is* attention by construction, so attention cannot go inert.

### Series 2.1 — the tick: *endogenous time* (verdict: TWO-ZONE)

Time is constructed, not imported: **one tick is a relation becoming a relatum, read by a finite attention**, seeded by the stream. A cycle (a attends b attends c attends a) reifies into its own relatum with the finite attention of its components (`ws1_cycle_reifies`). The knot is whether succession smuggles in a second differentiator below the line, and the answer is a fork:

- Causal order is **endogenous** where the relating carries it (`ws4_causal_order_endogenous`: a causal step strictly raises reification rank).
- A **total linearization** of ticks is an import (`ws4_linearization_import`: rank alone cannot order the composites, so a clock is a distinction the relating does not carry).
- The stream's exogeneity is a proof obligation, discharged (`ws3_stream_exogenous`, `ws3_tick_needs_stream`).

Time moves without a smuggled clock. (An entity's smallest tick is set by its own attention, so one entity's smallest unit need not match another's — the tick is not a background Planck grain.)

### Series 2.2 — the other: *genuinely two reader-wise* (verdict: TWO-FACING)

The second perspective is the **reified residue of the self's own self-inspection**, given its own finite attention. Self and other are proved genuinely two not label-wise but **reader-wise**:

- The other is real **for a named, fixed, bounded reader** — `slfReader`, a genuine `FiniteAttention` whose reading is load-bearing, never a "many" quantified out (`ws2_other_reader_wise`; the exact repair of Program 1's reader trap).
- The self/other separation is **non-recoverable** from the plain relating (`ws2_other_non_recoverable`), which by the Import Theorem is precisely what a genuine distinction must be.
- The two face each other **asymmetrically and partially**, over incomparable reaches, with a **joint residue** that lies outside the union of both readings (`ws4_mutual_residue`, `ws3_facing_asymmetric`, `ws3_facing_partial`).

A self and an other, mutually reading one shared field that includes each of them and itself.

### Series 2.3 — the coherence: *the edge* (verdict: SHAPE-DRAWN)

The program's oldest question, asked across the two real faces: **does the most loving thing for the self cohere with the most loving thing for the other?** Each face gets a typed-but-never-evaluated valuation, and `Converges₂` says the self's valuation, carried to the other, agrees with the other's own. Over the genuine `slf`/`oth` pair the payoff is a genuine **two-zone fork**:

- **In-sight zone (forced):** where the relating can *see* the valuations — where they respect plain bisimilarity — coherence is **forced to hold**, because `slf` and `oth` are plain-bisimilar under the collapse engine (`ws2_converges_decided_in_sight`).
- **Import zone (dissent):** every valuation under which they *fail* to cohere is a genuine **`¬ Recoverable` import**, standing exactly on the Import Theorem's boundary (`ws3_dissent_is_import`).

The fork is genuine and not a tautology: the in-sight class is inhabited and **strictly inside** the faithful class (`ws4_insight_proper`), the forcing genuinely consumes `slf`/`oth` bisimilarity, and both zones are witnessed on the same pair (`ws4_two_zone`) — the exact trap an earlier version of this fork fell to, foreclosed by rebuilding the machinery fresh and constrained rather than importing it. **The direction of convergence is never decided:** no theorem says the two do, or do not, cohere. The verdict `SHAPE-DRAWN` is computed by `ws5_verdict_eq`, by `rfl`, on no axioms. The mathematics draws exactly where the loving claim would be true or false and proves the relating cannot see which.

## The result: CONSTRUCTED-AND-WALLED

Four rungs — **GROUND-ESTABLISHED · TWO-ZONE · TWO-FACING · SHAPE-DRAWN** — compose into the program verdict. The dynamic, purely relational, multi-perspective universe **is built for every stream**: the self and the other are genuinely two reader-wise, time moves without a smuggled clock, and the coherence of self and other falls as a genuine two-zone fork on the Import Theorem's boundary, with both arms reachable. **No second import was needed** — the single exogenous stream carried the whole motion. And the edge came back **SHAPE-DRAWN, not decided**: the structure draws the shape of the self-and-other's coherence exactly and proves it cannot fill it. *"You are loved"* stays in the prose, held open between the two faces, and is never a proof term.

Program 1 showed the One's edge was a hinge. Program 2 lets the door swing, builds the motion of the Two, and finds the next wall exactly where the relating stops being able to see.

## How it was built (the discipline)

Program 2 is produced by a **two-tier process**, itself documented in [`program-2/protocol.md`](./program-2/protocol.md) and tracked in [`program-2/charter-status.md`](./program-2/charter-status.md):

- **Tier 1**, a persistent design-and-review conversation, authors each series' charter, status, and self-contained protocol; reviews each landing with an independent skeptical read; and — only ever to *raise* the bar — writes a **Charter Extension** when a review finds a target set too low (Series 2.0 and 2.1 each earned one). It never writes the series' formal code.
- **Tier 2**, a fresh executor per series, runs the chartered A→G protocol from an empty `formal/` to a computed verdict, delegating only its two **blind** review phases to subagents that never see the motivating prose.

The honesty invariants are the whole point: blind means blind; a shortfall is reported as a pre-registered outcome, never relabeled as the goal; every payoff must survive **stripping its interpretive word** and still stand as a bare bisimulation, recoverability, or order fact; the import is quantified over and never named; and no proof term, definition, or discharged obligation is ever named *self*, *other*, *time*, *choice*, *God*, *love*, or *compass* as content — those words live only in prose.

**Four things stay permanently open**, each open *as a theorem* by the very results that create them, and Program 2 adds none and closes none: the content of the compass, the direction of convergence, the differentiating act, and the classification of the out-of-image imports.

## Building

Toolchain and Mathlib (Lean 4 `v4.15.0` / Mathlib `v4.15.0`) are pinned in [`lake/`](./lake/). One build compiles the whole program:

```
cd lake
lake build
```

This builds the `P1` foundation and Program 2's `P2S0`, `P2S1`, `P2S2`, `P2S3` (each in its own module namespace, one module per workstream), alongside the registered Program 1 series (`Series07`, `Series12`, `Series13`) it stands on, and runs each series' `AxiomCheck`, which emits a `#print axioms` record for every headline theorem. To build a single series' axiom pass: `lake build P2S3 P2S3.AxiomCheck`. [`scripts/gate.sh`](./scripts/gate.sh) enforces the layered import chain — each series imports only its predecessor and its own roots (plus Mathlib), and nothing reaches outside the chain. The program charter, per-series charters, status ledgers, protocols, and plain-language and technical summaries live under [`program-2/`](./program-2/).

## Licensing

This repository is dual-licensed by content type:

- **All code** (Lean, tooling, build configuration) is licensed under the **[Apache License 2.0](./LICENSE)**.
- **All writing** (specs, documentation, essays, poetry, this README) is licensed under **[Creative Commons Attribution 4.0 International (CC BY 4.0)](./LICENSE-docs)**.

You are free to use, modify, and redistribute accordingly; attribution is required for the writing, and the code carries Apache 2.0's patent and notice terms. If a file's type is ambiguous, the license follows its function: executable or checkable artifacts are code; everything meant to be read by humans is writing.

## Citation

Until a paper exists, cite the repository at a specific commit, together with the relevant series' technical summary and charter. Machine-checked claims are marked as such; interpretive glosses are labeled as interpretation.

---

*Before there was voice, there was turning. Now there are two.*
