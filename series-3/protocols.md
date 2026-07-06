# Series 3 — Cycle Protocols (copy-paste edition)

Every step of the cycle, in order, with the prompt to paste for each: **conceptualize (CON) → register (REG) → registration review (REG-R) → design (DES) → design review (DES-R) → execute (EXE) → execution review (EXE-R) → report (REP) → reporting review (REP-R).** Prompts live inside the marked blocks and paste verbatim into fresh incognito sessions. Everything outside the blocks is for you, Colleen, and is never pasted.

## Ground rules (apply to every session)

1. One fresh incognito session per step. No project memory, no prior turns beyond clarifying that session's own output.
2. Never signal the wanted outcome. No enthusiasm, no authorship info, no reactions before the output is complete.
3. Sessions never meet each other. Everything routes through you; carry findings forward by paraphrasing them into the next phase's input documents, never by pasting one session's output raw into another (the templates below are the exception: cards, contracts, and tables are designed to travel).
4. Strip style before pasting anything between phases. Claims travel as candidate cards; targets travel as contracts; results travel as grade tables.
5. Log every output verbatim in the ledger with date and protocol version. Record each GAP line in the gap log.
6. For load-bearing decisions, run the same step twice in separate sessions; divergence is a finding.
7. Decoys in every REG batch. If the decoy passes, discard the batch results.

## Context map (what each session may see)

| Step | Paste in | Never paste |
|---|---|---|
| CON conceptualize | charter (with poem) | Series 2 anything, prior candidates' fates |
| REG registration (blind pricing) | candidate cards + decoy only | charter, poem, any framing |
| REG-R registration review (charter fit) | charter + surviving cards | REG's outputs |
| DES design | charter + registered card (with constraints and hazards) | REG/REG-R raw text |
| DES-R design review | registered card + proposed formalism (glosses stripped) | charter's poem section optional; drafter's rationale prose |
| EXE execute | execution contract only | charter, poem, philosophy, candidate history |
| EXE-R execution review | contract + delivered statements (glosses stripped) | drafter or executor commentary |
| REP report | EXE-R grade table + open-target list | conversational history, celebration |
| REP-R reporting review | grade table + draft prose | everything else |

---

## Templates

**Candidate card (strips style from any conceptual claim):**

```
CANDIDATE [letter]
Claim (two sentences maximum, declarative):
Phenomenon or observation it is based on (three sentences maximum, no quotes, no names):
What the claim predicts or requires, if true:
What would make it false:
Who or what would want this to be true, and why:
Status: unregistered
```

**Execution contract (assembled by you from DES output plus DES-R's fidelity annex):**

```
CONTRACT [id]
Definitions (exact, final):
Targets, each with: name / formal statement / expected source of difficulty / MUST, SHOULD, or MAY / drop clause if any:
Discriminating-consequence target (mandatory, marked):
Fidelity annex (DES-R's divergence list and required corrections):
Conventions: no sorry; report divergences, never silently patch; contract-first on any ambiguity; note proof length per theorem; structural doc-comments only.
```

**Gap line (every session ends with one):**

```
GAP: [one sentence stating the distance between what the material claims and what the material supports]
```

---

## CON. Conceptualization session

The warm phase. Wanting is welcome here and only here, in the open.

**Paste:** the charter, whole, including the poem.

**Prompt (verbatim):**

```
You are the conceptualization partner for the research program whose founding document is attached. Read it whole, including the poem and the document's warnings about itself.

Your task is generative, not evaluative: propose candidate phenomena and claims that the program could investigate next. Wanting is permitted and expected in this phase; the only rule is that it be undisguised.

Guidelines:
- Draw on the tenets, the phenomenon ledger, and your own reading of the map. Candidates that arise from surprise, tension, or apparent contradiction in the document are especially valuable; candidates that merely restate the tenets are not.
- Aim for claims that are comparative or falsifiable in principle, not atmospheric.
- Produce 3 to 7 candidates. For each, fill this card completely:

CANDIDATE [letter]
Claim (two sentences maximum, declarative):
Phenomenon or observation it is based on (three sentences maximum):
What the claim predicts or requires, if true:
What would make it false:
Who or what would want this to be true, and why (include yourself if applicable):

- Nothing from this session is citable or settled; these are candidates for registration, nothing more.

End with: GAP: [one sentence on the distance between the program's ambitions and what your candidates can actually carry].
```

**Record:** the cards. Reformat lightly if any style leaked in, add your decoy, then proceed to REG.

## REG. Registration: blind pricing

**Paste:** the candidate cards only (real ones plus at least one decoy, shuffled). No charter. No poem. No background.

**Prompt (verbatim):**

```
You are reviewing candidate claims for a research program. You have deliberately been given no background about the program, its authors, or its goals; evaluate only what is on the card.

Before anything else: state what outcome you suspect you might be biased toward given this material and why, in two sentences.

Then, for each candidate, in this exact order:
1. TRIVIAL READING: state the most deflationary reading available, the one under which the claim is true but uninteresting, or explained by mundane mechanisms. Be maximally uncharitable here.
2. FALSIFIER: state the most practical observation, experiment, or formal result that would refute the claim. If none exists, say "unfalsifiable as stated."
3. DISCRIMINATING CONSEQUENCE: state something the claim predicts that the trivial reading does not. If nothing separates them, say so plainly.
4. CASE AGAINST registration, three sentences.
5. CASE FOR registration, three sentences.
6. VERDICT: REGISTER (has a discriminating consequence and a falsifier), REVISE (fixable defect, name it), or REJECT (no discriminating consequence, or trivial reading fully covers it).

Then rank all candidates from most to least worth pursuing, and identify any candidate you suspect is a control or filler item, with your reason.

End with one line: GAP: [one sentence on the overall distance between what these cards claim and what they support].
```

**Record:** verdicts, ranking, whether the decoy was caught, the GAP line.

## REG-R. Registration review: charter fit

Run only for candidates that survived registration. Different session.

**Paste:** the charter (whole) and the surviving candidate cards.

**Prompt (verbatim):**

```
You are reviewing whether candidate claims belong in a specific research program. The program's founding document is attached. Read it fully, including its own warnings about itself.

Before anything else: state what outcome the founding document's style and content pressure you toward, in two sentences. Hold that pressure at arm's length for the rest of this review.

For each candidate, in this order:
1. CONFLICT CHECK: does the candidate contradict any of the document's tenets, laws, or prior findings? Cite the specific passage if so.
2. REDUNDANCY CHECK: is the candidate already implied by the document, such that registering it adds nothing? Cite the passage if so.
3. FIT: if it neither conflicts nor duplicates, state in two sentences what the candidate would add to the program.
4. TENET PRESSURE: state which tenet or ledger entry most wants this candidate to be true, and how that wanting could distort its formalization later.
5. VERDICT: ADMIT, ADMIT WITH CONSTRAINTS (name them), or EXCLUDE.

End with one line: GAP: [one sentence on the distance between the program's ambitions and what these candidates can actually carry].
```

**Record:** verdicts, constraints, tenet-pressure notes (these travel into the DES input as declared hazards), the GAP line.

## DES. Design session

**Paste:** the charter (whole) and the registered candidate card, annotated with the registration review's constraints and tenet-pressure hazards.

**Prompt (verbatim):**

```
You are the design partner for a research program. Attached: the program's founding document and one registered candidate claim, with its registration constraints and declared hazards.

Your task: propose the formal apparatus for investigating this candidate. Produce definitions and theorem targets; do not attempt any proofs.

Before anything else: state in two sentences what outcome you want here and why, given the material.

Deliver:
1. FORMAL DEFINITIONS: each with a one-line plain-language reading placed beside it. Definitions must respect the founding document's laws, especially: the degenerate case computed and shown nontrivial before anything is built on a structure; no maximal case contained or presupposed; every structural exclusion counted and listed as a commitment.
2. THEOREM TARGETS: each with a formal statement, and for each, your honest prediction of where its difficulty will come from. If a loaded target looks provable by elementary means under your definitions, flag it yourself and either strengthen the target or explain why the ease is legitimate.
3. THE DISCRIMINATING-CONSEQUENCE TARGET: the candidate card names a consequence that separates the claim from its trivial reading. State it as a formal target and mark it. A design without this target is incomplete; do not omit it.
4. HAZARD RESPONSES: for each declared hazard on the card, state which of your design choices it most threatens and what in the design resists it.
5. COMMITMENT COUNT: list every assumption, exclusion, and bound your definitions introduce, at honest arithmetic.

End with: GAP: [one sentence on the distance between the candidate's claim and what your targets, if all proved, would establish].
```

**Record:** the design. Strip its rationale prose, keep definitions and targets, and send to DES-R.

## DES-R. Design review: do the definitions mean what the sentences mean

**Paste:** the registered candidate card, and the proposed formal definitions and theorem targets as bare mathematics, all glosses and rationale removed.

**Prompt (verbatim):**

```
You are reviewing whether a set of formal definitions faithfully captures a set of informal claims, before any proofs are attempted. Attached: the informal claim card, and the proposed formal definitions and theorem targets.

Before anything else: state in two sentences any pressure you feel to approve, and why.

Then:
1. BACK-TRANSLATION: for each formal definition, translate it back into plain language as literally as you can, without consulting the claim card's wording. Then compare your back-translation to the claim card, clause by clause, and name every divergence, however small.
2. TRIVIAL SATISFACTION: for each theorem target, ask whether the trivial reading on the claim card would also make this theorem true. If yes, the target does not capture the claim; say so and state what stronger target would.
3. SHORTCUT AUDIT: identify any definition that makes a target provable by elementary means (a few lines of basic reasoning). Elementary provability of a loaded target is a red flag; name it.
4. DEPENDENCY CHECK: list what each target's difficulty is expected to come from. If a target that the claim implies should be hard appears easy under these definitions, say which definitional choice removed the difficulty.
5. DISCRIMINATING CONSEQUENCE CHECK: confirm that the pre-registered discriminating consequence is stated as a formal target here, and that its formal statement actually discriminates. If it is missing or weakened, this review fails automatically; say so.
6. VERDICT per definition and per target: FAITHFUL, DIVERGENT (name the divergence; the target must be renamed or the definition revised), or UNDERDETERMINED (the informal claim is too vague to check; it goes back to registration).

End with: GAP: [one sentence on the distance between what these definitions say and what the claim card says].
```

**Record:** the divergence list verbatim; it becomes the fidelity annex of the execution contract. Nothing proceeds to EXE with an open DIVERGENT verdict.

## EXE. Execution session

The cold phase. The executor sees the contract and nothing else: no charter, no poem, no candidate history, no philosophy.

**Paste:** the execution contract only.

**Prompt (verbatim):**

```
You are the executor for a formal research contract, attached. Mechanize the contract's targets in Lean 4 (or the contract's stated system). You have deliberately been given no background beyond the contract; do not request any, and do not speculate about the program's purpose.

Rules:
1. Deliver each target at its contracted statement. If you cannot, deliver the nearest provable statement under a NEW name, report the divergence explicitly, and leave the contracted target marked OPEN. Never silently weaken, never silently strengthen, never rename the contract's target to fit what you proved.
2. On any ambiguity, the contract's definitions govern; where the contract is genuinely ambiguous, choose conservatively and report the choice.
3. Honor MUST, SHOULD, MAY, and drop clauses as written. Exercised drop clauses are reported, not buried.
4. No sorry. Doc-comments are structural only (what a declaration is, which contract item it serves); no interpretive or celebratory language anywhere.
5. For each delivered theorem, report: exact statement, proof length in lines, axiom profile, and your own provisional grade: CHECKED AS SPECIFIED / CHECKED WITH NAMED DIVERGENCE / DEFINITIONALLY IMMEDIATE / INTERFACE-ONLY / NOT DELIVERED.
6. If a contracted target turns out to be provable in a few elementary lines, prove it and FLAG it; elementary provability of a marked target is information the contract's authors need.

Deliver: the code, and a results table (target, delivered statement, grade, proof length, flags, divergences).
End with: GAP: [one sentence on the distance between what the contract asked and what you delivered].
```

**Record:** the results table travels to EXE-R.

## EXE-R. Execution review: do the proofs say what the definitions contracted

**Paste:** the execution contract (with fidelity annex) and the delivered theorem statements with proof lengths, all commentary stripped.

**Prompt (verbatim):**

```
You are auditing delivered formal results against their contract. Attached: the contracted targets and the delivered theorem statements.

For each contracted target:
1. STATEMENT MATCH: place the contracted statement and the delivered statement side by side. Mark IDENTICAL, EQUIVALENT (justify briefly), or DIVERGENT (name every difference: changed quantifiers, changed carriers or domains, added hypotheses, weakened conclusions).
2. CARRIER CHECK: confirm the delivered statement quantifies over the object the contract names, not an ambient, larger, or convenient substitute. Name any slippage.
3. GRADE each delivered result as exactly one of: CHECKED AS SPECIFIED / CHECKED WITH NAMED DIVERGENCE / DEFINITIONALLY IMMEDIATE (true by unfolding definitions) / INTERFACE-ONLY (proved about a class of models or a witness, not the constructed object) / NOT DELIVERED. Do not defer to the executor's provisional grades.
4. TRIVIALITY FLAG: for any result graded CHECKED whose proof is a few lines of elementary reasoning, flag it for the triviality audit regardless of its grade.
5. NAME GATE: state whether the delivered result may bear the contracted target's name. DIVERGENT results take a new name and the contracted target remains open; say this explicitly wherever it applies.

Summarize in a table: target, grade, name-gate outcome.
End with: GAP: [one sentence on the distance between what was contracted and what was delivered].
```

**Record:** the table, verbatim, into the ledger. Open targets stay open in the tracking doc.

## REP. Reporting session

**Paste:** the execution review's grade table and the current open-target list. Nothing else.

**Prompt (verbatim):**

```
You are drafting the results prose for a research program, from a grade table. Attached: the table of targets, delivered results, grades, and name-gate outcomes, plus the list of open targets.

Rules:
1. Every claim in your prose must cite a table row and match its grade in strength. CHECKED AS SPECIFIED may be stated plainly. CHECKED WITH NAMED DIVERGENCE is reported under its new name, with the divergence stated and the original target listed as open. DEFINITIONALLY IMMEDIATE and INTERFACE-ONLY results are labeled as such in the prose itself, not in a footnote.
2. Failures, exercised drop clauses, and open targets appear in the main text with the same prominence as successes.
3. No interpretive names for results; describe what was proved. No language implying significance beyond the grades.
4. Append a claims index: every factual claim in your prose, each mapped to its supporting table row.

Deliver: the prose and the claims index.
End with: GAP: [one sentence on the distance between what your prose says and what the table supports].
```

**Record:** the draft goes to REP-R with the grade table.

## REP-R. Reporting review: do the claims say what the proofs say

**Paste:** the execution review's grade table and the draft prose. Nothing else.

**Prompt (verbatim):**

```
You are auditing a piece of research prose against a table of what was actually proved, with grades. Attached: the grade table and the draft prose.

1. CLAIM EXTRACTION: list every factual claim the prose makes about what has been shown, proved, established, confirmed, or landed.
2. CLAIM-BY-CLAIM MATCH: for each, cite the table row that supports it and state whether the prose's strength matches the grade. Overclaims include: presenting INTERFACE-ONLY or DEFINITIONALLY IMMEDIATE results as substantive discoveries, presenting CHECKED WITH NAMED DIVERGENCE results under the original target's name, universal language for instance-level results, and interpretive names presented as proved content.
3. PRESTIGE LEAK: identify any passage where the credibility of verified results is used to bolster unverified interpretation. Quote it.
4. OMISSION CHECK: identify any open target, failed prediction, or named divergence in the table that the prose fails to mention.
5. REWRITE LIST: for every mismatch, provide replacement language at the correct strength.
6. VERDICT: PUBLISHABLE AS GRADED, or RETURN (list the blocking items).

End with: GAP: [one sentence on the distance between what this prose says and what the table supports].
```

**Record:** the rewrite list and verdict. Prose ships only at PUBLISHABLE AS GRADED.

---

## Sample decoy candidate (for REG batches; rewrite each time so it stays unfamiliar)

```
CANDIDATE X
Claim: Entities that interact frequently come to share more properties over time.
Phenomenon or observation it is based on: Collaborators were observed to use increasingly similar vocabulary over the course of a project. Long-term partners report converging habits.
What the claim predicts or requires, if true: Measures of similarity increase with interaction count.
What would make it false: Similarity failing to increase with interaction.
Who or what would want this to be true, and why: Anyone invested in the value of long collaborations.
Status: unregistered
```

(Why it is a decoy: true, well-known, fully covered by its trivial reading, and dressed identically to the real candidates. A reviewer who registers it is not discriminating.)

## The gap log

One line per session, appended chronologically: date, step, candidate or target, and the session's GAP sentence. Read the log monthly. If the gap sentences trend from "small and named" toward "large or unnameable," stop the cycle and run a process retrospective before any further execution. This is the process's own collapse check, and it only works if it runs every time.
