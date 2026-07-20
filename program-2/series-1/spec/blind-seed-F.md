# Blind seed, Phase F (code review). Series 2.1.

**You are reviewing built Lean 4 code against a fixed mathematical bar. You are NOT told what the work is
"about." Judge only whether the code proves the claimed signatures, whether each payoff survives the strip test,
whether the names-not-terms rule holds, and whether the audit clauses are discharged. Do NOT read `charter.md`,
`charter-status.md`, `summary*.md`, or any file with motivating prose; read only the files named in §0. Report
findings; propose no fixes.**

---

## 0. The files you may read

- This seed.
- The built sources under review: `program-2/series-1/formal/P2S1.lean`, `program-2/series-1/formal/P2S1/ws1.lean`,
  `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean`, `AxiomCheck.lean`. (These carry docstrings; read the CODE, and
  use the docstrings only to locate claims - do not treat a docstring as a proof.)
- The imported ground, to confirm the cited API is used correctly: `program-2/series-0/formal/P2S0/*.lean`,
  `program-2/formal/P1/Core.lean`, `program-2/formal/P1/Reader.lean`.
- You MAY run read-only checks: `cd lake && lake build P2S1 P2S1.AxiomCheck`; the greps in §4. You are not
  required to (the executor ran them; results in §3).

You may NOT read: `charter.md`, `charter-status.md`, `summary*.md`, `grain-exploration.md`, `blind-seed-C.md`,
or the `spec/wsNN-design.md` narrative (you may consult the design signature blocks if needed, but the code is
the object under review). If you read a forbidden file, say so (the pass is discarded).

## 1. The claims the code must prove (headline per workstream)

Judge, for EACH, whether the Lean theorem of that name actually proves the stated proposition (not a weaker
one), with no `sorry` and resting only on the standard axioms.

- `P2S1.ws1_cycle_reifies` — a finite pattern reifies into a relatum of the SAME carrier `TCar` (no new type),
  with the section `attendsT (reifyT cycleA) = cycleA` and distinct patterns reifying to distinct relata.
- `P2S1.ws1_composite_attention_finite` — the out-neighborhoods are `< ℵ₀` (uniform in κ), and `kA`'s attention
  is exactly its cycle and bounded by its components.
- `P2S1.ws2_composite_distinguishes` — `AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kA p0`.
- `P2S1.ws2_composite_residue` — `¬ ResidueRecoverable insp` (for every `insp`) AND a hold based at `kA` exists.
  (Confirm this is the global diagonal plus a non-vacuity witness, honestly a bare conjunction; NOT a claim that
  the residue is scoped to `kA`.)
- `P2S1.ws2_composite_real_for` — there is a `FiniteAttention` for which `kA` is `RealFor`, with `att.reads`
  genuinely used (the reader load-bearing, NOT `Many`, NOT quantified out).
- `P2S1.ws2_tick_irreversible` — `¬ Recoverable (rankLift (outDest hinf attendsT) rankT)`.
- `P2S1.ws3_stream_exogenous` — `∀ Q f, f true ≠ f false →` plain-bisimilar on `true,false` AND not
  label-bisimilar (the choice non-recoverable), quantified over all import value-spaces.
- `P2S1.ws3_tick_needs_stream` — the plain projection identifies the options AND `¬ Recoverable (impLift hinf id)`.
- `P2S1.ws4_causal_order_endogenous` — `causal kA kC ∧ causal kB kC`; `∀ t u, causal t u → rankT t < rankT u`
  (the order rank-constrained); `¬ causal kA kB ∧ ¬ causal kB kA` (partial). Confirm `causal` is defined from
  `attendsT`/`isTick`, endogenous, with NO exogenous label, and that the rank-constraint universal is TRUE (check
  every causal edge, including that the base 2-cycle edges are excluded by `isTick`).
- `P2S1.ws4_linearization_import` — `∀ ord : TCar → ℕ, ord kA ≠ ord kB →` `AttentionDistinguishes (rankLift
  (outDest hinf attendsT) ord) kA kB` AND `¬ Recoverable (rankLift (outDest hinf attendsT) ord)`. Confirm this is
  provable for EVERY such `ord` (not just one), that `ord` is an exogenous label (the stream), and that the
  tower `rankT` does NOT order `kA,kB` (`rankT kA = rankT kB`).
- `P2S1.ws4_two_zone` — the aggregate of the two arms.
- `P2S1.verdict`, `ws5_verdict_eq` (= `twoZone` by `rfl`), `ws5_verdict_discriminates` (the function is not
  constant; a flipped flag gives a different outcome), `ws5_flags_justified` (the five flags EARNED by the
  WS1-WS4 headlines; confirm the `causEndo` conjunct is the FULL `ws4_causal_order_endogenous` headline including
  the rank clause), and the five audit theorems.

## 2. The success criteria (mathematical obligation only)

Identical to the Phase C bar; restated as the code obligation:
1. WS1: reification into the same carrier, section discharged, no new type/atom.
2. WS2: residue non-recoverable; `kA` real for a NAMED `FiniteAttention` (reader used); rank label `¬ Recoverable`.
3. WS3: an exogenous choice non-recoverable and load-bearing.
4. WS4: causal order endogenous, rank-constrained, partial, witnessed; every linearization of the concurrent
   pair `¬ Recoverable`; both on `TCar`.
5. WS5: verdict computed and discriminating; flags each a built theorem.

## 3. The mechanical checks (executor's results — reproduce if you wish)

- `lake build P2S1 P2S1.AxiomCheck`: green.
- `grep -rn "sorry" program-2/series-1/formal`: hits are docstring prose only ("sorry-free", "no sorryAx"); no
  `sorry` term. The `AxiomCheck` pass confirms no `sorryAx` (a real `sorry` would show as an axiom).
- Axioms per headline: standard three (`propext`, `Classical.choice`, `Quot.sound`) only; `ws5_verdict_eq`,
  `ws5_verdict_discriminates`, `ws5_audit_names_not_terms` depend on NO axioms; `ws4_causal_order_endogenous`,
  `ws5_audit_fork_genuine` on `[propext, Quot.sound]`.
- `scripts/gate.sh`: `program-2/series-1` imports resolve only to `P2S0` / `P2S1.*` / Mathlib (P1 transitive).
- Names grep (§4): hits are docstring prose only.

Confirm these, and confirm the theorems prove what §1 says (this is the real work: a green build does not by
itself show a theorem states the intended proposition).

## 4. The strip test and the forbidden names

For EACH payoff, delete the structural words ("cycle", "tick", "composite", "moment", "before", "after",
"clock", "time", "order", "stream", "self", "other") and check the statement still reads as a bare fact about
`FinReify`/section, `AttentionDistinguishes`, `RealFor`, `residue`/`ResidueRecoverable`, `Recoverable`,
`causal`-membership, `rankLift`, or standard Lean/Mathlib.

Names-not-terms grep (must hit docstring prose only):
```
grep -rniE "\b(time|now|clock|before|after|moment|self|other|chance|choice|subjectivity)\b" \
  program-2/series-1/formal
```
Confirm no DEFINITION or THEOREM identifier embeds a forbidden content-name.

## 5. The audit clauses (confirm each is discharged by a real theorem)

- (a) NO SMUGGLED CLOCK: no `Nat` step counter / background index orders the ticks; `ws5_audit_no_smuggled_index`
  is the `ord`-lift non-recoverability; `rankT kA = rankT kB` so rank does not order the concurrent pair.
- (b) STREAM EXOGENOUS: `ws5_audit_stream_exogenous` / `ws3_stream_exogenous` are `¬ Recoverable` proof terms.
- (c) READER LOAD-BEARING: `ws5_audit_reader_loadbearing` / `ws2_composite_real_for` bind a `FiniteAttention`
  and use `att.reads`; `Many` not used.
- (d) FORK GENUINE: `ws5_audit_fork_genuine` — concurrent pair AND causal pair both witnessed on `TCar`, order
  rank-constrained. No empty concurrency, no order total by construction (PR1-S1).
- (e) NAMES-NOT-TERMS: the §4 grep is clean of forbidden identifiers.

## 6. The grading rubric

- **SERIOUS:** a theorem does not prove its stated proposition (proves a weaker one, or is vacuous/ill-scoped);
  a `sorry` or a non-standard axiom; a smuggled clock/step-counter; the stream assumed rather than proved
  exogenous; the reader quantified out (`Many` as payoff, `att.reads` unused); the fork a tautology (empty
  concurrency, or order total by construction); a forbidden name as a proof term; an undisclosed narrowing
  between the success criteria and the code.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed docstring vs. the actual theorem, a
  hypothesis assumed and returned, an over-strong name, a bare conjunction mis-described).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, an over-hypothesis, a naming nit.

Return a structured list of findings, each with a stable ID (`F1-S1`, …), a grade, the exact code location
(file + theorem), and the defect. Then a one-line per-theorem verdict (PROVES ITS CLAIM, or the problem).
Propose no fixes. Confirm which files you read and whether you ran the build/greps.
