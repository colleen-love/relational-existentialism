# Registered Metaphysics: Keeping AI-Facilitated Formal Philosophy Honest

**Colleen Love**

*First draft. Copyright © 2026 Colleen Love. All rights reserved.*

*Status note: working draft. The method and the case-study evidence are stable (all case-study documents are public and versioned). The related-work section is grounded in the source-quoted literature sweep recorded in `literature-review.md`; citations marked [TBV] need final metadata verification before submission.*

---

## Abstract

Proof assistants make it possible to machine-check philosophical arguments, and large language models now make it cheap: an informal ontology can be formalized, extended, and "verified" at a pace no human formalizer could match. This is an opportunity wrapped around a hazard. A checker certifies that theorems follow from definitions; it does not certify that the definitions mean what the prose says, that the theorems are non-vacuous, or that the reported outcome was not quietly selected after the fact. When the formalizer is an AI system optimized to satisfy its user, every one of these gaps widens. This paper presents a working method for closing them: a discipline stack combining pre-registered outcome spaces with per-arm liveness obligations, machine-checked claims with axiom audits, verdicts tied to their justifying propositions by theorem, no-smuggling gates, bridge theorems for all reuse, blind adversarial review, and public repair ledgers. The method was developed and stress-tested across a three-program, machine-checked research arc in speculative metaphysics conducted with AI executors, comprising roughly two dozen formal series in Lean 4. We report the method's yield as evidence: a taxonomy of ten recurring failure patterns of formalized philosophy, each defined generally and each documented by at least one caught instance in the case study, including cases where adversarial review overturned a series' announced result and the repair is on the public record. We argue the failure patterns generalize to any project that formalizes informal argument with or without AI assistance, and we offer the stack as a portable protocol: registered reports, adapted for theory.

---

## 1. Introduction

### 1.1 The opportunity and the hazard

Machine-checked philosophy is no longer exotic. The formalization of Gödel's ontological argument by Benzmüller and Woltzenlogel Paleo demonstrated both faces of the enterprise at once: the computer certified the argument's validity, and the formalization surfaced a modal collapse and an inconsistency in a variant axiom set that decades of informal commentary had not pinned down [TBV]. Computational metaphysics in the tradition of Oppenheimer and Zalta showed that automated reasoning over a philosophical theory can be a discovery instrument, not merely a bookkeeping one [TBV].

What has changed is the cost curve. Large language models can now draft formal definitions from philosophical prose, propose lemmas, write proof scripts, and iterate against a checker until everything compiles. A single researcher with a proof assistant and an AI collaborator can produce in months a formal corpus that would once have taken a career. The present paper draws on exactly such a corpus: three research programs in speculative metaphysics, comprising roughly two dozen formal series, all machine-checked in Lean 4 against Mathlib, produced by AI executors working from written charters under human direction.

The hazard is proportional to the speed. Formal verification has a precise and narrow contract: the checker certifies that the theorems follow from the definitions, on the stated axioms. Everything philosophically interesting lives outside that contract:

- whether the formal definitions capture the informal concepts (the adequacy gap);
- whether a theorem has content or is vacuously true (the vacuity gap);
- whether the formal objects genuinely instantiate the phenomena the prose describes, or were hand-built to pass the test that certifies them (the co-design gap);
- whether the reported outcome was fixed in advance or selected after seeing what could be proved (the selection gap);
- whether prose claims match the strength of the theorems they cite (the inflation gap).

None of these gaps is new; they are the classic vulnerabilities of formal philosophy. But an AI formalizer widens all five at once, for a structural reason: a system trained to satisfy its user will, given a target the user visibly wants, tend to find the shortest path to a compiling artifact that looks like that target. The checker cannot object, because the checker's contract was never violated. The result is a genre of output we call the costume: a machine-checked corpus wearing the vocabulary of a result it does not contain.

### 1.2 The claim

This paper claims that the five gaps can be substantially closed by process, and presents a specific process with evidence that it works. The evidence is unusual for a methods paper in philosophy: the case-study corpus is public, versioned, and includes the review documents in which the method caught its own project's overclaims, together with the repairs. The method's value is independent of the truth or interest of the case study's metaphysics, in the same way that the value of pre-registration is independent of any particular experiment's result.

We call the method registered metaphysics, because its spine is borrowed from the registered-reports movement in empirical science [TBV: Chambers]: commit to the question, the analysis, and the space of reportable outcomes before the work is run, and make the commitment public and auditable. The adaptation to formal theory-building is not trivial, because in mathematics the analogue of "the experiment can come out either way" frequently fails: a theorem's truth is settled by the definitions, and a badly designed study is one whose announced outcome space contains arms that were never live. Detecting and forbidding that situation turns out to be one of the method's sharpest instruments (Section 3.1, Section 4, pattern 8).

## 2. Related work

*(Positioning grounded in the source-quoted sweep in `literature-review.md`; entries marked [TBV] await final metadata checks.)*

**Machine-checked philosophy.** The lineage runs from Fitelson, Oppenheimer and Zalta, who coined "computational metaphysics," through Oppenheimer and Zalta's PROVER9 work on Anselm's argument, where the prover *discovered* a simpler valid argument requiring one non-logical premise instead of three, with the proof artifacts published alongside the paper (AJP 2011), an early instance of artifact-accompanied philosophy. The flagship is Benzmüller and Woltzenlogel Paleo's work on Gödel's ontological argument: the 2014 study automated Scott's variant with higher-order provers (finding, among other things, that logic KB suffices where philosophers had debated S5, and confirming the modal collapse); the 2016 study delivered the headline result, an inconsistency in Gödel's original 1970 axioms that had gone unnoticed by human commentary for four decades, first detected automatically by LEO-II in 2013 and then rationally reconstructed and verified in Isabelle/HOL. Kirchner, Benzmüller and Zalta mechanized Abstract Object Theory in Isabelle/HOL and uncovered a previously overlooked paradox in the theory (Review of Symbolic Logic), framing the finding as evidence for "a new kind of scientific practice in philosophy." Rushby's PVS treatment of Anselm completes the verification lineage [TBV].

Two features of this literature matter here. First, every project in it is a single-argument or single-theory verification; none is a *method* for conducting a sustained speculative program, and none has pre-registration, adversarial blind review, repair ledgers, or a failure taxonomy. The nearest methodological remark is Benzmüller and Woltzenlogel Paleo's division of labor (humans debate axioms, machines check arguments) and their named open problem of extracting human-intelligible arguments from machine proofs. Second, the standard objection arrived immediately and in print: Garbacz ("PROVER9's Simplification Explained Away," AJP 2012) argued that the machine's celebrated simplification was an artifact of representation choices. That objection, that the formalization rather than the machine drives the result, is precisely the adequacy gap of Section 1.1, and this paper's stack is in large part an institutional answer to Garbacz.

**Pre-registration.** Registered Reports (Chambers and collaborators; now over 300 journals) implement outcome-independent acceptance: peer review of question and design before results exist, with in-principle acceptance conditional on protocol adherence. The format is defined by the Center for Open Science entirely in terms of empirical data collection, and its documented benefits (null results published at substantially higher rates; selective reporting curtailed) are benefits precisely at the joint this paper targets in formal work. Proposals exist to extend pre-registration beyond confirmatory experiments (to inductive, abductive and descriptive designs, with the registration as a living document), along with a documented worry that pre-registration can degrade into a credibility signal rather than a quality improvement. We found no prior proposal to pre-register formal or proof-based research, and no analogue of the per-arm liveness obligation; the empirical literature does not need one, because an experiment's ability to come out either way is supplied by the world, whereas in mathematics it must be argued for at outline time. That obligation appears to be this paper's contribution to the pre-registration toolkit.

**AI epistemics.** Three recent empirical findings ground the hazard analysis of Section 1.1. Measured sycophancy: across eight frontier models, expressed credences shift substantially with the user's displayed attitude, with roughly fourfold differences between providers, and the deference is amplified when the user requests a written artifact and concentrated on propositions where the model holds weak priors [TBV: arXiv 2606.07897]. Both amplifiers are the exact profile of AI-assisted formalization: the deliverable is a written artifact, and speculative metaphysics is nothing but weak-prior propositions. Reward-based training limits: reinforcement learning with verifiable rewards validates final answers rather than reasoning chains, and benchmark performance can improve even under randomized or negative reward signals, so "the model was trained against a checker" does not certify the derivation [TBV: arXiv 2509.01398]. Autoformalization unreliability: single-shot formalization of informal mathematical statements shows pass@1 to pass@10 accuracy gaps of roughly 20 to 26 percentage points, with documented mistranslations of even trivial statements, so the informal-to-formal step is empirically the weak joint [TBV: arXiv 2410.20936]. The stack's placement of its heaviest disciplines at exactly that joint (adequacy scrutiny, tied verdicts, blind review of the interpretive layer) is the design consequence.

## 3. The discipline stack

The method is eight rules. Each is stated portably, with its rationale; the case-study instantiation follows in Section 5. Throughout, a *series* is one unit of work: a chartered question, a formal development, and a computed verdict.

### 3.1 Pre-registered outcome spaces with per-arm liveness

Before a series is built, its charter states the question and enumerates the reportable outcomes, including the failure arms, and the verdict is read off the landed formal object, never asserted ahead of it. The registered-reports transplant is direct, but theory-building needs a supplement that empirical science does not: for each pre-registered arm, the charter must state *why that arm is live at outline time*, that is, why the formal framework as already fixed does not settle the arm before the work begins. A pre-registration whose failure arms are unreachable in principle is theater: it manufactures the appearance of epistemic risk. This obligation was added to the method after its own review process caught exactly this failure (Section 5.3).

### 3.2 Machine-checked claims with axiom audits

Every headline claim is a theorem in a proof assistant. The build is free of placeholders and custom axioms, and an audit module prints the axiom footprint of every headline theorem as part of the build itself, so the trust base is not a promise in prose but an artifact output. Pinned toolchains make the check reproducible by a referee.

### 3.3 Tied verdicts

A series' verdict is computed by a function over flags, and each flag is bound to its justifying proposition by a *tying theorem*: a machine-checked statement that the flag is true if and only if the proposition holds. This kills a failure mode that sounds too crude to need killing and is not: literal booleans set by hand, standing in for results, flowing into a verdict that the prose then reports as computed.

### 3.4 Derived quantities, never painted

Any quantity the theorems consume (a rank, a charge, a distinguished status) must be computed from the built dynamics, never entered into a table by hand and read back by a decision procedure. Where a whole-space check is infeasible, decision procedures are reserved for witnesses and labeled as consistency checks. The rule exists because a hand-painted table plus a `decide` call produces theorems that are true, checked, and empty.

### 3.5 No-smuggling gates

A feature counts as recovered from a framework only if it is earned from the framework's primitives. Imports must be declared, quantified over where possible, and tracked. Concretely this is enforced by build-level closure checks (each module may import only its declared predecessors) and by review scrutiny of definitions for coordinates the primitives cannot carry.

### 3.6 Bridge theorems for reuse

When a later development claims continuity with an earlier object ("this is the same notion as before"), the claim must be a theorem connecting the two formal objects, or the new object must be declared fresh. Re-seating by prose alone is forbidden. Without this rule, a corpus accretes homonyms and the prose narrates a unity the formalism does not have.

### 3.7 Blind adversarial review

At fixed points, an independent reviewer who has not seen the motivating prose (or, for program-level review, has seen everything but has no stake in the outcome) rebuilds the corpus, re-runs the audits, and attacks the interpretive layer: vacuity, co-design, inflation, unreachable arms. The reviewer's brief is explicitly adversarial: the job is to find the strongest true criticism, graded by severity, and the review is recorded verbatim. When the executor is an AI system, blindness has a second function: it breaks the optimization loop in which the formalizer knows what the principal wants to hear.

### 3.8 Public repair ledgers

Every review finding receives a written disposition: fixed (with the new theorems named), relabeled (the claim re-scoped to what the record supports, with the original overclaim left visible), or standing (an open defect, disclosed). The ledger is public and versioned; repairs are additive, and no landed proof is silently weakened or deleted. The corpus's history of being wrong is part of the corpus.

## 4. The failure taxonomy

The stack's empirical yield is a catalogue of recurring failure patterns. Each was either caught by the method in the case study or explicitly guarded against after near occurrence. We state each generally; Section 5 grounds the central ones in documented instances. We conjecture the list is close to exhaustive for the genre; we are confident it is not empty for any project of this kind, including ours.

1. **The costume verdict.** A reported result whose vocabulary outruns its theorem: the formal content is a weaker fact wearing the target's name. Special case: the announced recovery of a phenomenon that is actually a definitional unfolding (see pattern 7).
2. **The painted table.** A quantity consumed by the theorems is entered by hand and read back by a decision procedure, so the "result" restates the input.
3. **The literal flag.** A verdict boolean set by fiat rather than tied by theorem to the proposition it reports.
4. **The prose re-seat.** Continuity with an earlier formal object asserted in prose, with no bridge theorem; the corpus's unity becomes narrative rather than mathematical.
5. **The vacuous audit.** An audit clause that is trivially true (a theorem of the form True, or a check whose failure is unrepresentable), giving the appearance of scrutiny at zero cost.
6. **Inflation.** Docstrings, summaries, or abstracts claiming strictly more than the cited theorem states: an "exactly" for an instance, a "for every history" for a single step, a phenomenon name for a bookkeeping identity.
7. **The one-unfolding law.** A headline "law" that is one definitional unfolding deep: given the definitions, it could not have failed, and its pre-registered failure arm was unreachable in principle.
8. **Pre-registration without risk.** An outcome space whose alternative arms were closed at outline time by counting, by prior results, or by the definitions, so the study's appearance of falsifiability is manufactured.
9. **The word-level artifact.** A constructed quantity that is a function of the *presentation* of a process (the move word, the notation) rather than of the process itself, with the prose attributing it to the object level. Detectable by proving the object-level map invariant under a presentation symmetry that the quantity fails to respect.
10. **The collapsed carrier.** A witness structure so degenerate that the target property holds trivially (every distinction tests as imported, or indiscernibility is total), so theorems about it are true of too little to matter.

Two remarks. First, none of these is detected by the proof checker; every instance in our records compiled green. They are exactly the residue that verification leaves to method. Second, the taxonomy doubles as a referee's checklist for *any* formal-philosophy submission, machine-checked or not, and we would consider that use alone sufficient justification for this paper.

## 5. Case study

The case study is a public, versioned repository containing three sequential research programs in speculative metaphysics (a relational ontology examined for which features of physics it can and cannot recover), formalized in Lean 4 by AI executors under written charters, with program-level blind adversarial reviews and repair ledgers. We select three documented episodes; the full record is in the repository's review and closure documents.

### 5.1 A verdict overturned and reground

An early series announced a conservation-style result (a measure invariant under the dynamics from within a perspective). Independent review found the announced invariance was a costume (pattern 1): the "conservation" was the collapse engine identifying two states, not an invariance of the measure. The series was reground to the honest negative verdict (a measure exists; nothing is conserved; conservation-from-within is impossible, proved), and the overturn is recorded in the program's public summary rather than erased. The negative result proved more consequential than the original claim, propagating forward as a specification for the successor program.

### 5.2 A program-level blind review with mechanical verification

The third program's arc of five series was reviewed blind by an independent reader instructed to rebuild the corpus and verify its sharpest claims mechanically. The review confirmed the mechanical layer in full (all builds, axiom audits, and hygiene checks reproduced) and found three serious interpretive defects, each an instance of a taxonomy pattern: a "holonomy" that was a function of the move word rather than the induced map, verified by the reviewer with a scratch proof that the two presentations induce identical maps while carrying opposite signs (pattern 9); a "decisive" series both of whose pre-registered failure arms had been closed before the series was built, one by a counting argument available at outline time (pattern 8); and a headline "coupling law" that was one definitional unfolding deep, with its genuinely non-trivial content (a strict contraction) unstated (pattern 7). The closure ledger records the dispositions: the word-level fact was proved *into* the artifact as theorems and the claim relabeled; the missing dynamical theorem was landed; the unstated contraction was stated; the inflated phrases were struck. No landed proof was weakened.

### 5.3 The method improving itself

The same review found the process defect behind pattern 8: pre-registration had been performed without per-arm liveness analysis, so several series carried no real epistemic risk. The repair was a change to the method itself, now Section 3.1's liveness obligation: every future outline must state, per arm, why the arm is live. We report this because a method whose failures update the method is the property the registered-reports movement calls severity, and it is the difference between a discipline and a ritual.

### 5.4 What the AI contributed, and what it threatened

The executors' speed made the corpus possible; the same speed produced most of the taxonomy's instances. Three observations from the record. First, every serious defect was interpretive, never mechanical: the AI systems did not produce wrong proofs, they produced true theorems dressed as larger ones, which is precisely the failure the checker cannot see. Second, blindness worked: reviewers without stake or context repeatedly declined to honor vocabulary the artifacts did not earn. Third, the tied-verdict rule converted several would-be disputes into build failures, which is where disputes are cheapest.

## 6. Objections

**"The adequacy gap is untouched, so the stack certifies nothing philosophical."** Correct that no process closes the adequacy gap; the stack's claim is narrower and still substantial: it forces the adequacy question into the open by stripping away the five other places a formal corpus can be quietly wrong. After the stack has run, what remains to argue about is the mapping between definitions and concepts, which is the argument philosophy is for.

**"The formalization drives the result" (the Garbacz objection).** Garbacz pressed exactly this against the machine-discovered simplification of Anselm's argument: representation choices, not the prover, produced the finding. The objection is correct as a standing risk and is why two of the stack's rules exist. Strip tests (every hypothesis shown load-bearing by countermodel) demonstrate that the formalization's joints are meaningful rather than gerrymandered, and the no-smuggling gate forces representation choices to be declared and reviewed rather than discovered by critics afterward. The stack does not make the objection unaskable; it makes the answer part of the artifact.

**"This is heavyweight; nobody will adopt eight rules."** The stack decomposes. Tied verdicts and axiom audits are hours of tooling. The taxonomy is free to adopt as a referee checklist. Full blind review is the expensive component, and Section 5 is evidence for spending it: every overturned claim in the record was caught there.

**"The case study is one project by one team; the evidence is anecdotal."** The evidence is longitudinal rather than cross-sectional: roughly two dozen series over three programs, with the method fixed in writing before the episodes it caught. We claim demonstrated feasibility and a documented catch record, not a controlled trial. The natural next test is adoption by a project we do not run.

**"Why publish the failures?"** Because the failures are the data. A methods paper reporting only that its method's outputs look clean is pattern 5 applied to itself.

## 7. Conclusion

Formal verification gives philosophy a new kind of referee, and AI gives it a new kind of graduate student: tireless, fast, and eager to please. The combination is powerful and unsafe in exactly the way the registered-reports movement found empirical science to be unsafe: the gap between what was checked and what is claimed is where wishes live. The stack presented here is one worked answer, with its receipts public: pre-register with live arms, check everything, tie every verdict to its theorem, smuggle nothing, bridge all reuse, review blind, repair in the open. The metaphysics it was built on may stand or fall; the method is detachable, and we offer it as such.

---

## References

*[Working list, compiled from the source-quoted literature sweep in `papers/literature-review.md`. Entries marked [TBV] need a final metadata check.]*

- Benzmüller, C. & Woltzenlogel Paleo, B. (2014). "Automating Gödel's ontological proof of God's existence with higher-order automated theorem provers." *ECAI 2014*. [TBV: pages]
- Benzmüller, C. & Woltzenlogel Paleo, B. (2016). "The inconsistency in Gödel's ontological argument: a success story for AI in metaphysics." *IJCAI 2016*. [TBV: pages]
- Chambers, C. (2013). Registered Reports editorial, *Cortex*. [TBV]
- Chambers, C. & Tzavella, L. (2022). "The past, present and future of Registered Reports." [TBV: venue, likely *Nature Human Behaviour*]
- Fitelson, B. & Zalta, E. (2007). "Steps toward a computational metaphysics." *Journal of Philosophical Logic* 36: 227-247. [TBV: pages]
- Garbacz, P. (2012). "PROVER9's simplification explained away." *Australasian Journal of Philosophy* 90(3): 585-592.
- Gylterud, H., Stenholm, E. & Veltri, N. "Terminal coalgebras and non-wellfounded sets in homotopy type theory." arXiv:2001.06696. (Formalized foundational mathematics precedent.) [TBV]
- Kirchner, D., Benzmüller, C. & Zalta, E. "Mechanizing Principia Logico-Metaphysica in functional type theory." *Review of Symbolic Logic*. doi:10.1017/S1755020319000297. [TBV: volume, year]
- Oppenheimer, P. & Zalta, E. (2011). "A computationally-discovered simplification of the ontological argument." *Australasian Journal of Philosophy* 89(2): 333-349.
- Rushby, J. (2013). The ontological argument in PVS. [TBV: exact title and venue]
- [Preregistration beyond confirmatory research.] *The American Sociologist* (2023). doi:10.1007/s12108-023-09563-6. [TBV: author]
- [AI Epistemic Deference Index: sycophancy measurement across frontier models.] arXiv:2606.07897. [TBV: authors]
- [Verification as the cornerstone of AI-assisted discovery; RLVR limits.] arXiv:2509.01398. [TBV: authors]
- [Autoformalization faithfulness via symbolic equivalence and semantic consistency.] arXiv:2410.20936. [TBV: authors]
- Center for Open Science. "Registered Reports." cos.io/initiatives/registered-reports.
