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
The frozen source of truth: commitments C1–C6 (§2), success criteria (i)–(vii) (§7), and workstream specs WS1–WS7 (§4). **Hash it once and never edit mid-cycle.** If the charter changes, that is a new CR version with a new hash, and in-flight obligations either complete against the old hash or restart.

### Blind Register (BR)
What a blind phase is allowed to see. For a given obligation, the BR contains **only the mathematical statement** at stake — functor, carrier, monad, distributive law, target property — with all charter-motivating prose stripped out. No mention of ROSR, "view from nowhere," metaphysics, or which commitment this serves.

The BR is what makes blindness enforceable across incognito sessions: it is the entire context a blind phase receives.

---

## 2. Model choice

Opus at most. Do not exceed Opus for any phase.

| Phase | Rationale |
|---|---|
| 1 Conceptualize (blind) | Open-ended mathematical framing |
| 2 Register (blind) | Precise signature + failure conditions |
| 3 Design (against charter) | Binding to charter is high-stakes |
| 4 Review (blind) | Adversarial math check |
| 5 Execute (blind) | Lean proof authoring |
| 6 Review (blind) | Verification of the artifact |
| 7 Report (against charter) | Charter mapping + ledger update |

Review phases (4, 6) should run in a **fresh incognito session** seeded with BR only, so the reviewer has no memory of the design or execution rationale. This is what gives blindness teeth; without a second context the review collapses into self-justification.

---

## 3. The seven phases

Each phase lists its **context in** (what you paste into the incognito session) and its **output** (what you save out to carry forward).

### Phase 1 — Conceptualize (blind)
- **Context in:** BR for this obligation.
- **Do:** State what mathematical object/property is at stake and why it is non-trivial. Guess a proof strategy.
- **Output:** One-paragraph problem statement + candidate strategy. No charter language.

### Phase 2 — Register (blind)
- **Context in:** BR + Phase 1 output.
- **Do:** Pre-register, *before any design*: the exact Lean 4 signature to be proved; the ambient theory (ZFC/AFA encoding choice, functor `F`, monad `T`, distributive law `λ` if relevant); the success condition; and explicitly **what would count as this obligation failing** (collapse, non-existence, no distributive law, non-convergence).
- **Output:** Registered signature + failure conditions. **Timestamp and hash it.** This is the guard against post-hoc reframing of a failed proof as a success.

### Phase 3 — Design (against charter)
- **Context in:** CR + Phase 2 registration.
- **Do:** Open the charter. Bind the registered statement to its commitment(s) and criterion(criteria). Confirm the Lean signature actually discharges the charter obligation and has not drifted. If design reveals the blind statement was underspecified, **record the gap** rather than silently patching it.
- **Output:** Explicit binding (e.g. "theorem = criterion (v), incompleteness of self-knowledge via Lawvere, C5") + any gap notes.

### Phase 4 — Review (blind)
- **Context in:** BR + Phase 3 design, **fresh session**, CR withheld.
- **Do:** Check the design *as mathematics only*: well-formed signature, sound strategy, hidden assumptions? Blindness here stops charter-sympathy from waving through a bad proof.
- **Output:** Pass / revise verdict with specific objections.

### Phase 5 — Execute (blind)
- **Context in:** BR + reviewed design.
- **Do:** Write the Lean 4 proof. `sorry`-free is the bar. Charter stays closed so you prove what was registered, not what you wish were true.
- **Output:** Lean file for this obligation.

### Phase 6 — Review (blind)
- **Context in:** BR + registered signature + Lean file, **fresh session**.
- **Do:** Verify the artifact: does it compile? Is it `sorry`-free? Does it prove **the registered signature** (not a weakened variant)? Check axiom leakage with `#print axioms` — flag any classical/choice or AFA-encoding axioms not declared in Phase 2.
- **Output:** Verification verdict + axiom list.

### Phase 7 — Report (against charter)
- **Context in:** CR + verified artifact + registration.
- **Do:** Map the verified theorem back to commitment + criterion. Classify the outcome. Update the ledger. A failed or partial result triggers a **methodology note, not a reframe**.
- **Outcome classes:**
  - **Discharged** — theorem proves the registered signature.
  - **Impossibility proved** — a sharp negative result; counts as success per charter §5.
  - **Partial** — with the obstruction to the rest made precise.
  - **Failed** — registered signature not achieved; document why.
- **Output:** Ledger row + outcome classification.

---

## 4. Charter-specific guards

**Split the Goldilocks band.** Do not make richness-vs-boundedness one obligation. Register three separate obligations: (a) `νF` non-degenerate (branching ≥ 2 survives); (b) `νF` exists as a set (κ-bounded / finite powerset); (c) joint satisfiability for a specific `F`. Registering separately prevents declaring the band non-empty by conflating two half-proofs.

**Poles invariant.** At every WS6 report phase, check a standing invariant: the terminal-coincidence (zero-object) must never be definitionally entangled with an inconsistent universal set. Conflating them sinks the program (§8).

**Obligation zero.** There is no standard mechanized non-well-founded set theory in Lean 4. WS1 must register "build/justify the AFA carrier" as obligation zero before any downstream obligation can proceed. Its Phase 2 registration must pin the encoding choice and the axioms it introduces.

---

## 5. The ledger

One checked-in file, one row per obligation. Because sessions are incognito, **the ledger is the only durable state** — it must be maintained by hand outside the sessions.

| Field | Meaning |
|---|---|
| `obligation_id` | e.g. WS5-crit-v |
| `commitment` | C1–C6 |
| `criterion` | (i)–(vii) |
| `registered_sig_hash` | hash from Phase 2 |
| `cr_hash` | charter version this ran against |
| `outcome` | discharged / impossibility / partial / failed |
| `axioms_used` | from Phase 6 `#print axioms` |
| `blind_review_pass` | Phase 4 and Phase 6 verdicts |
| `lean_file` | path to the artifact |

---

## 6. Incognito session discipline

Because no session remembers any other:

1. **Every phase is a cold start.** Paste in only the declared "context in" for that phase — never more. Pasting the charter into a blind phase breaks the protocol.
2. **Carry state by hand.** Phase outputs are saved by you and pasted into the next phase. The ledger and the two registers live outside the sessions.
3. **Hash before you cross a blind/against-charter boundary.** The Phase 2 registration hash and the CR hash are what let you prove, later, that the blind work was not retrofitted to the charter.
4. **Reviews get their own cold sessions.** Reusing the execution session for review reintroduces the memory that blindness is meant to remove.
