# UCM Protocol — Ungrounded Constitution Mechanization

A machine-checked workflow for bringing *An Ungrounded Constitution of Objects and Relations* to life in Lean 4, one proof obligation at a time.

All work runs in **incognito sessions** (no memory, no cross-session state). Every phase's context must therefore be reconstructed from the registers described below, carried into the session by hand. Nothing persists that you do not explicitly paste in.

---

## 0. Core principle

The charter is realized one **proof obligation** at a time. An obligation is a single commitment-or-criterion turned into a Lean 4 theorem (or a precise impossibility). Each obligation runs the full seven-phase cycle before the next begins.

The cycle alternates **blind** phases (charter framing withheld, to keep work honest and review adversarial) with **against-charter** phases (artifact explicitly bound back to commitments and success criteria). Blindness is not a metaphor: in an incognito session a "blind" phase must be given the Blind Register *only*, with no charter prose in context.

---

## 1. The two registers

Keep these physically separate. Each is a standalone file you paste into a session as needed.

### Charter Register (CR)
The source of truth: commitments, success criteria, and workstream specs. If the charter changes work that is upstream of what has been completed, the process must be restarted.

### Blind Register (BR)
What a blind phase is allowed to see. For a given obligation, the BR contains **only the mathematical statement** at stake — functor, carrier, monad, distributive law, target property — with all charter-motivating prose stripped out. No mention of ROSR, "view from nowhere," metaphysics, or which commitment this serves.

### Execution Register (ER)
What a execution phase is allowed to see. For a given obligation, the ER contains the github repository.

The BR is what makes blindness enforceable across incognito sessions: it is the entire context a blind phase receives.

---

## 2. Process overview

One obligation runs seven phases in order:

| Phase | Name | Mode |
|---|---|---|
| 1 | Conceptualize | against charter |
| 2 | Design | against charter |
| 3 | Blind Design Review | blind |
| 4 | Charter Design Review | against charter |
| 5 | Execute | against repository |
| 6 | Blind Report | blind |
| 7 | Charter Report | against charter |

Every phase runs on Opus, and every phase runs in a **fresh incognito session**. Blind phases (2, 3, 6) are seeded with the BR only, so no memory of the charter or of prior rationale leaks in. This is what gives blindness teeth; without a fresh context the review collapses into self-justification.

---

## 3. The seven phases

Each phase lists its **context in** (what you paste into the incognito session) and its **output** (what you save out to carry forward).

### Phase 1 — Conceptualize (against charter)
- **Context in:** CR, the workstream to be built, Lean artifacts from previous workstreams (if applicable), **fresh session**.
- **Instructions:** Working from the charter, state what mathematical object/property is at stake and why it is non-trivial for **WS${X}**. Generate **3–7 candidate framings** of the obligation — different ways to cash out the commitment/criterion as something provable — and for each, sketch a candidate proof strategy. Note the trade-offs between them. Do not include charter prose in your output; these should be mathematical descriptions. For each candidate include the exact Lean 4 signature to be proved; the ambient theory (ZFC/AFA encoding choice, functor `F`, monad `T`, distributive law `λ` if relevant); the success condition; and explicitly **what would count as this obligation failing** (collapse, non-existence, no distributive law, non-convergence). (This phase reads the charter but emits blind, charter-free output — that output becomes the BR for downstream phases.)
- **Output:** 3–7 candidates, each with its registered signature + failure conditions. **Timestamp and hash the selected candidate.** This is the guard against post-hoc reframing of a failed proof as a success.

### Phase 2 — Design (against charter)
- **Context in:** CR, Phase 1 output, **fresh session**.
- **Instructions:** Run a triage that is *decidable on paper per candidate* and collapse the framing decision into a table. The framing choice is downstream of the triage, not a substitute for it. Select the best candidate and turn it into a full mathematical design: the proof architecture, the definitions and lemmas needed, and the dependencies on imported upstream theorems.
- **Output:** Mathematical design + any gap notes.

### Phase 3 — Design Review (blind)
- **Context in:** BR, Phase 2 design, **fresh session**.
- **Instructions:** Check the mathematics of the design: well-formed signature, sound strategy, hidden assumptions?
- **Instructions (part 2):** Can you update the design and address the problems that you found?
- **Output:** Mathematical design + any gap notes.

### Phase 4 — Design Review (against charter)
- **Context in:** Phase 3 blind design review context, charter.
- **Instructions:** Check the design against the charter. Does it accurately represent the active workstream? Bind the design to its commitment(s) and criterion(criteria), and confirm the signature discharges the charter obligation without drift.
- **Instructions (part 2):** Can you update the design and address the problems that you found?
- **Output:** Mathematical design + any gap notes.

### Phase 5 — Execute (Claude code, against repo)
- **Context in:** ER, **fresh session**.
- **Instructions:** Please merge in main and write the Lean 4 proof for series-3/spec/ws${X}/04-charter-design-review.md in series-3/formal/ws${X}.lean. Import the new lean file in series-3/formal/Series3.lean so that the build compiles the new file, too. `sorry`-free is the bar for this design. Ignore the archive directory as it is irrelevant. Once you are finished, please ensure that the build compiles and run `#print axioms` and flag any classical/choice or AFA-encoding axioms.
- **Output:** Lean file for this obligation.

### Phase 6 — Blind Report (blind)
- **Context in:** BR, executed Lean file, charter design review, **fresh session**.
- **Instructions:** Verify the artifact — is it `sorry`-free, does it prove **the registered signature** (not a weakened variant) of the design? Please classify the mathematical outcome. A failed or partial result triggers a **methodology note, not a reframe**. Please evaluate the **Outcome classes:** **Discharged** — theorem proves the registered signature. **Impossibility proved** — a sharp negative result; counts as success per charter §5. **Partial** — with the obstruction to the rest made precise. **Failed** — registered signature not achieved; document why.
- **Output, sent to Claude code if not discharged:** Mathematical outcome + axiom list + ledger row (signature-level fields). 

### Phase 7 — Charter Report (against charter)
- **Context in:** Phase 6 blind report context, charter.
- **Instructions:** Map the verified theorem back to the charter. Classify the outcome at the workstream level. A failed or partial result triggers a **methodology note, not a reframe**. Please evaluate the **Outcome classes:** **Discharged** — theorem discharges the workstream obligation. **Impossibility proved** — a sharp negative result; counts as success per charter §5. **Partial** — with the obstruction to the rest made precise. **Failed** — workstream obligation not achieved; document why.
- **Output, sent to Claude code if not discharged:** Ledger row (charter-level fields) + outcome classification.

---

## 4. Charter-specific guards

**Split the Goldilocks band.** Do not make richness-vs-boundedness one obligation. Register three separate obligations: (a) `νF` non-degenerate (branching ≥ 2 survives); (b) `νF` exists as a set (κ-bounded / finite powerset); (c) joint satisfiability for a specific `F`. Registering separately prevents declaring the band non-empty by conflating two half-proofs.

**Poles invariant.** At every WS6 report phase, check a standing invariant: the terminal-coincidence (zero-object) must never be definitionally entangled with an inconsistent universal set. Conflating them sinks the program (§8).

**Obligation zero.** There is no standard mechanized non-well-founded set theory in Lean 4. WS1 must register "build/justify the AFA carrier" as obligation zero before any downstream obligation can proceed. Its Phase 1 registration must pin the encoding choice and the axioms it introduces.

---

## 5. Iteration and workstream dependencies

The seven workstreams are not independent; later ones consume the *discharged theorems* of earlier ones. The unit that crosses a workstream boundary is not prose but a **named, verified Lean artifact** — a theorem that made it to `discharged` in the ledger. Downstream obligations import these as hypotheses or definitions, never re-deriving them.

**Dependency order.** The rough topological order is:

- **WS1 (groundless carrier)** — including obligation zero (the AFA carrier) — has no upstream dependency. It produces the ambient theory + carrier that *every* downstream obligation's BR must reference.
- **WS2 (object = relations, coinductively)** consumes WS1's carrier; produces `νF` existence + bisimulation characterization.
- **WS3 (bidirectional constitution)** consumes WS2's `νF` and the functor `F`; produces the bialgebra + distributive law `λ`.
- **WS4 (graded parthood)** consumes WS2/WS3; produces the enriched containment, reused by attention weights.
- **WS5 (finite attention)** consumes WS2 (final coalgebra as metric space) and WS4 (weights); produces the incompleteness theorem + convergence conditions.
- **WS6 (no poles, no outside)** consumes WS2's `νF`; produces the coincidence/impossibility results.
- **WS7 (non-collapse)** consumes WS2, WS5, WS6; produces the Goldilocks-band results. It is terminal — it depends on the most.

**How an output becomes an input.** When obligation A is `discharged`, its ledger row records the `lean_file` and the theorem name. A downstream obligation B that depends on A does three things:

1. **Phase 1 (Conceptualize/register)** of B names A's theorem in its ambient-theory declaration and lists it as an imported hypothesis. B's registered signature is stated *relative to* A holding.
2. **Phase 5 (Execute)** of B `import`s A's Lean file and uses the theorem directly. Because A is machine-checked and `sorry`-free, B inherits that guarantee rather than re-proving it.
3. **B's BR** includes the *statement* of A's theorem (not its charter motivation), so blind phases can use it without seeing why it matters.

**When an upstream result changes.** If A is later revised (re-registered under a new signature hash, or reclassified from `discharged` to `partial`), every obligation whose ledger row names A is **stale** and must re-run from Phase 1. Track this with a `depends_on` field (below): a changed hash upstream invalidates every row that points to it. This is the incognito-safe substitute for a build system's dependency graph — since no session remembers the graph, the ledger *is* the graph.

**Partial upstream results.** A downstream obligation may proceed on a `partial` or `impossibility` upstream result, but only if B's Phase 1 registration explicitly states which part of A it relies on and confirms that part is the discharged part. An impossibility result is often a *usable* input: e.g. WS6's "no maximal everything" (Cantor) is a hypothesis WS7 leans on, not an obstacle.

---

## 6. The ledger

One checked-in file, one row per obligation. Because sessions are incognito, **the ledger is the only durable state** — it must be maintained by hand outside the sessions.

| Field | Meaning |
|---|---|
| `obligation_id` | e.g. WS5-crit-v |
| `commitment` | C1–C6 |
| `criterion` | (i)–(vii) |
| `registered_sig_hash` | hash from Phase 1 |
| `cr_hash` | charter version this ran against |
| `outcome` | discharged / impossibility / partial / failed |
| `axioms_used` | from Phase 6 `#print axioms` |
| `blind_review_pass` | Phase 3 and Phase 4 verdicts |
| `lean_file` | path to the artifact |
| `depends_on` | list of upstream `obligation_id` + `registered_sig_hash` this row consumes |

---

## 7. Incognito session discipline

Because no session remembers any other:

1. **Every phase is a cold start.** Paste in only the declared "context in" for that phase — never more. Pasting the charter into a blind phase breaks the protocol.
2. **Carry state by hand.** Phase outputs are saved by you and pasted into the next phase. The ledger and the two registers live outside the sessions.
3. **Hash before you cross a blind/against-charter boundary.** The Phase 1 registration hash and the CR hash are what let you prove, later, that the blind work was not retrofitted to the charter.
4. **Reviews get their own cold sessions.** Reusing the execution session for review reintroduces the memory that blindness is meant to remove.
