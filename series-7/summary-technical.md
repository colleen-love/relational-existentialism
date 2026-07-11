# Relational Existentialism — Series 7: Technical Status Summary

*A machine-checked proof of the Import Theorem — atomless, purely relational, behaviorally identified plurality is impossible without a distinction the relating cannot carry — and the finding that the required distinction forks undecidably into the given and the chosen, a fork the formalism cannot close.*

## 1. The headline

> **Atomless, purely relational, behaviorally identified plurality is impossible without a distinction the relating cannot carry, forking undecidably into the given and the chosen.**

The first part is the Import Theorem: no construction satisfies all four of (1) *plain relating* (the functor is the unlabelled `P_κ`, no imported coordinate), (2) *behavioral identity* (an object is its relating — every bisimulation is contained in equality; equivalently "no imported atom"), (3) *genuine every-moment atomlessness* (`SHNE`, hereditary non-emptiness), and (4) *plurality*. Proved, machine-checked, non-vacuous, arbitrary carrier. To violate the impossibility while keeping (1)–(3) you need a distinction the relating cannot carry.

The fork is a property of that distinction, not of any dynamics — it holds on a single static coalgebra as much as on a process. It is sharpest at the dynamic limit, where the two candidates are provably *equal*, not merely bisimilar: atomless histories are **equal** (`ws1_productive_unique`: every productive thread is Ω), so any *function* of the history returns the same value on two of them (`att_cannot_distinguish_atomless_histories`). Under (2), the static case is the same: two atomless states are behaviorally identified, hence one, so any separator is equally exogenous. That exogenous separator is, to the formalism, a coordinate not carried by the relating — the §4.1 footprint of an import. But the footprint is all a proof can see, and a **given** (a pre-existing atom) and a **choice** (a freely-originated distinction, a will) leave the same one. Type theory has no predicate for *chosen rather than given*; the theorem forces the disjunction and is silent on the disjunct. That silence is the result.

Read as Parmenides generalized: a groundless, atomless, faithfully-relational world that is **determined** is the One — Series 6's collapse is exactly the world without will — and the only way it holds more than one thing is a distinguisher the relating does not carry, externally defined or internally chosen, undecidably.

## 2. Verification status

- **`sorry`-free:** no proof-position `sorry`, `admit`, `native_decide`, `sorryAx`, `opaque`, `unsafe`, `@[extern]`, or custom `axiom` anywhere in `ws1`–`ws7` (grep-clean; the twelve `decide` calls are all on decidable `ULift Bool` (in)equalities).
- **No custom axioms:** every headline theorem rests only on Mathlib's standard three — `propext`, `Classical.choice`, `Quot.sound`.
- **In-build verification, machine-run:** `Series7/AxiomCheck.lean` imports the whole build and runs `#print axioms` on **50 headline lines** across WS1–WS7 — the engine (`ws1_atomless_bisim`), the Import Theorem (`ws2_import_theorem`, `ws2_import_theorem_static`), the dynamic collapse (`ws1_productive_unique`), the recoverable-label collapse (`ws4_recoverable_atomless_collapses`), the subset-of-a-restriction tightness probe, the atom-or-will capstone (`att_cannot_distinguish_atomless_histories`), every witness path (`twoLoop`, `labelLoop`, `facedLoop`, `subsetLoop`, `leafCoalg`, `omegaProc`), the audit (`ws7_audit`), the verdict `def` itself (`ws7_verdict`) and its equation (`ws7_verdict_eq`). Committed at [`spec/axiom-check-log.md`](./spec/axiom-check-log.md) against **Lean 4 v4.15.0 / Mathlib v4.15.0**.
- **Closure:** `scripts/gate.sh` confirms `series-7/formal/` imports resolve only to Series 7's own roots plus Mathlib — nothing from `series-6/`…`series-4/` or `archive/`.
- **Adversarial series review (project-review-3):** no SERIOUS finding at the term level; the engine is not painted on, the flagship does not launder, the strip test passes, the coincidence/independence check passes, verdict `payoffsEstablished` confirmed correct. (The reviewer could not run the toolchain in their environment and flagged the axiom-check as source-consistent but pending their re-run; it is machine-checked here at this commit.)

## 3. The spine

- **The engine — `ws1_atomless_bisim`.** On *any* plain `dest : X → PkObj κ X`, the "both-atomless" relation `hneRel` is a genuine `IsBisim`, so any two `SHNE` states are bisimilar. One honest relation, one line, strictly more general than a terminal-coalgebra collapse. The root of the Parmenides collapse (Series 4), the Static Collapse (Series 6), and everything here.
- **The Import Theorem — `ws2_import_theorem` / `ws2_import_theorem_static`.** Sound, non-vacuous, universally quantified over plain coalgebras; conclusion is real plurality (`∃ x y, x ≠ y`), every hypothesis load-bearing. The strip test is by exhibited counterexample terms: drop (3) and `leafCoalg` (behaviorally identified, plural, *with a leaf*); drop (1) and `labelLoop`; drop (2) and `twoLoop`.
- **The recovered instances.** `ws1_recovers_static` (abstract behavioral-identity form subsuming the terminal `νPk`) and `ws1_productive_unique` (the dynamic collapse — Ω the unique productive thread), both genuine instances of the one engine.
- **The semantic import test — `ws4_free_label_is_import`, `ws4_recoverable_not_import`, `ws4_recoverable_atomless_collapses`.** "Import" is the charter's §4.1 *semantic* predicate (a coordinate the plain relating cannot recover), not "a `Q` in the signature." A free label is an import (plain-bisimilar yet label-distinct); a recoverable label is not, and collapses.

## 4. The exogenous distinction, and the atom-or-will fork

The chain, each link its own theorem:

1. **Atomless histories are equal.** `ws1_productive_unique`: `Productive x → x = omegaProc`. Two atomless histories are both Ω, literally equal (not merely bisimilar). `ws1_no_productive_plurality` states the impossibility directly.
2. **No function separates them.** `att_cannot_distinguish_atomless_histories`: for any `att : Proc κ → Q` and productive `x, y`, `att x = att y` — a function cannot separate equal inputs. Three lines, from (1).
3. **So a separator is exogenous.** Any distinction between two atomless histories must read an argument not contained in the histories — a coordinate not carried by the relating.
4. **The disjunction, and its undecidability.** That exogenous coordinate is *externally defined* (a given: an atom, §4.1) or *internally chosen* (a will). The two leave the identical formal footprint; the formalism has no predicate separating them. The Lean proves (3); the atom-or-will reading of the forced exogeneity is the interpretation it cannot decide, and is recorded as such — **a true lemma plus an interpretation, never a proved disjunction** (series-review-3 C2).

The subset-of-a-restriction probe (`ws4_atomless_label_distinction_imports`, `ws4_subset_selection_survives_as_import`) is the static shadow of the same fact: on an atomless carrier the engine makes every pair bisimilar, so any per-state selection that survives is non-recoverable — an import — *regardless of what the label is made of*. The atom relocates from the material to the choosing; there is no third, atom-free way to survive.

## 5. Status against the success criteria (charter §8)

| Criterion | Status |
|---|---|
| (i) collapses any plain, behaviorally-identified, atomless construction to a subsingleton | **Discharged — the headline Impossibility** (`ws2_import_theorem*`, from `ws1_atomless_bisim`); static and dynamic instances recovered. |
| (ii) non-circular — ingredients independently motivated, escapes refuted as theorems | **Discharged.** `ws7_non_circularity_audit` grounded on the *semantic* import; strip witnesses are real terms. (The `NoImportedAtom = BehaviorallyIdentified` identity is a declared definitional alias, deliberately pulled out of the load-bearing anchors — C1.) |
| (iii) exhaustive — every distinction a leaf, an import, or a collapsing history | **Discharged (single coalgebra: `ws3_dichotomy`, leaf-or-import) / Partial (any construction).** Exhaustiveness across all constructions is the un-rangeable quantifier → `heuristic`; the candidate fourth kind (faced boundary) is a named open; the fourth thing the atom-or-will fork names — *choice* — is the distinction the relating cannot see by construction. |
| (iv) explains the program | **Discharged for free-label imports / re-classified for the endogenous cases (Partial).** `ws4_program_explained` proves the free-label mechanism and `twoLoop` drop-2; the S4 face is reclassified recoverable-hence-not-import (escalation is the import); S5 index prose, S3 weight not transcribed. The *name* asserts more than the theorem proves — honestly re-scoped in the ledger (R2). |
| (v) isolates the one loophole — limit-atomlessness | **Discharged (characterization + ruling) / Partial (metric family).** `ws5_limit_reintroduces_leaves`; adjudicated import-in-time. |
| (vi) draws its honest scope | **Discharged (core) / heuristic (universal).** `ws6_provable_core`; `ws6_universal` a `heuristic`-tagged `def`. |

The verdict `ws7_verdict = payoffsEstablished` is computed from an audit certificate whose every field is a theorem (`ws7_verdict_eq` by `rfl`); break a field and it fails to build. It is not `importForced` for exactly the two pre-registered reasons: the trichotomy's exhaustiveness is un-formalizable, and the catalogue is Partial.

## 6. What it does — and does not — do

**Solid, earned, attack-tested:** the engine; the Import Theorem; the recovered collapses; the semantic import test and the recoverable-label collapse; the drop-1 witness now at full hereditary atomlessness (`ws4_label_drop_atomless`, series-review-3 R1 — `SHNE` on `plainOf (labelLoop)`, not merely first-level nonempty); the strip witnesses as real terms; the atom-or-will capstone lemma.

**Labelled honestly, none load-bearing for the impossibility:**
- Exhaustiveness across "any construction" is not formalizable (`heuristic`, floored by `ws6_provable_core`).
- The full prior carriers (`νLk`, `Winf`, the weight algebra) are prior art; the drop *mechanisms* are mechanized on minimal witnesses. The S3 weight carries *no* Series-7 witness (the generic import witness is a free label, not a weight); the S5 index is asserted "reuses the label mechanism" in prose (R2).
- The convergent leafy family (WS5) is characterized but not built.
- The WS3 delivered kind is a **dichotomy**, honestly renamed from "trichotomy," with the "teeth"/exhaustiveness withdrawn to an open; the candidate fourth kind (faced boundary) is prose (R3).
- The atom-or-will disjunction is a lemma plus an interpretation (C2), never a proved disjunction.

## 7. Open problems (each named, none load-bearing for the impossibility)

1. **Exhaustiveness across any construction** (WS3/WS6, `heuristic`) — the sole reason the verdict is `payoffsEstablished`, not `importForced`.
2. **The full prior carriers** (WS4, Partial) — transcribe `νLk`/`Winf`/the weight algebra; settle whether the S5 index is recoverable (a leaf, like the S4 face) or a free-label import; record that S3 weights carry no witness.
3. **The convergent leafy family** (WS5, build-owed) — the metric `CauchySeq`-to-Ω family.
4. **The faced-boundary fourth kind** (WS3) — a leaf that also carries a quality; reduce it to leaf-or-import or admit it as genuine.
5. **The undecidable disjunct — choice** — the atom-or-will fork is where the impossibility deliberately stops: *externally defined* is catalogued, *internally chosen* is named and left, because the relating cannot carry the difference between them. This is the seed of what comes after.

## 8. The honest headline

Series 7 proves, sorry-free and axiom-clean: the Import Theorem (`ws2_import_theorem`, an Impossibility) and its engine (`ws1_atomless_bisim`, atomless behavior is unique on any plain coalgebra, unifying all four prior collapses); the dynamic collapse (`ws1_productive_unique`, Ω the unique atomless history); the semantic import test and the recoverable-label collapse; and the loophole isolated and adjudicated import-in-time. Pushed to its dynamic limit it forces the finding that gives the series its name: **a distinction that separates two atomless histories must come from outside the relating, and is either externally defined or internally chosen — a disjunction the machine-checked impossibility forces and provably cannot close.** The plain-collapse verdict is the honest middle `payoffsEstablished`, earned and attack-tested; the prior-series catalogue is honestly Partial; and the deepest thing the theorem says is the door it points at and cannot open — that a groundless world holds more than one thing only by an atom or a will, and no proof can tell you which.
