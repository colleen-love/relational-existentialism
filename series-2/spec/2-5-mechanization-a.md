# 2.5-mechanization-a — Work Order: the D19 Pack and the Closing Theorems of Series 2

Target file: `series-2/formal/Spec25a.lean` (the name is free again and this is the file it was waiting for). Conventions in force: no `sorry`; doc-comments with spec addresses (cite 2.5); axiom audit in-build; results post-hoc-marked, predictions frozen; hostile-first ordering mandatory.

**A change of standing discipline, stated once.** Every prior order forbade consulting §8 / the D19 register. That discipline is retired: D19 is written (2.5 §1) and is now citable like any other decision. What replaces it: **no proof in this order may *depend* on D19 for its mathematics.** The naming is interpretation over proved structure; if any theorem below turns out to need D19 as a hypothesis, that is a category error and a finding — halt and report. The doc-comments may (should) carry the interpretive readings; the proof terms may not.

**Scope in one line.** Mechanize the naming's formal content (V1, Fog, privacy, non-transmissibility, T19), then close Series 2's theorem contract: S1 honestly, T11 as far as it will go, T4/T7, T5/T10 attempts, and the small debts. When the MUSTs land, Series 2 is closed and the closing statement is written.

---

## Stage 0 — the D25 sweep (MUST; cheap; first)

- Doc-comment sweep across Spec20a–204g and the specs: 'observe/observation' → 'know/knowing' in interpretive text per D25. **No proof term changes; no declaration renames** (identifier churn risks nothing and buys nothing — record `Reveal`, `contextsC_differ`, etc. as legacy names in a glossary comment at the head of Spec25a.lean).
- One verification build after the sweep; the cold-reader check (O-2-5-5) is spec-side, flagged for the owner.

## Stage 1 — the D19 formal pack (MUST)

- **V1** `rem_empty_at_saturation` : ctx_x(r) = pat(x) → remC x r = ∅. One line off the definitions; doc-comment: the vanishing that forces the stratified reading — at D19's locus, loss cannot be edge-shaped.
- **FP-D1 / P-D19-1** `selfKnowing_inexhaustible` : the tower over a self-anchored knowing never terminates — every order has a successor act not witnessed at that order. Route: `ascentC` restricted to the self-anchored locus + T6's seriality (`descent_serial` idiom from Spec21d, ascended). The fog, as theorem.
- **FP-D2 / P-D19-2** `residue_private` : (a) Reveal(w, s) ⊆ pat(w) for all w, s (have it); (b) an unshared self-anchored r ∈ pat(x) appears in no Reveal of any w ≠ x. One-liners composed; the content is the composition.
- **FP-D2 / P-D19-3** `residue_nontransmissible` : no hearsay chain from w ≠ x assembles x's self-anchored tower — chain content bounded by shared boundaries at each step (T13's bound, iterated; if full T13 lands in Stage 5 first, cite it; otherwise prove the bound-per-step form here and let Stage 5 generalize).
- **FP-D3 / T19** `T19_no_residue_no_many` : package T17 + the Forcing Lemma as one statement over the functor class (any signature without a self-referential loss-generator has final coalgebra ≅ 1). Expected: re-exposition, no new proof. Doc-comment carries the modus tollens.

## Stage 2 — S1 and T11 (MUST for the honest S1; the T11 attempt is the order's star)

- **FP-D4 / S1_ω** : at the ω-tier, finitude of deep holds is trivial (pat finite). Prove it in one line **and say so loudly** — the doc-comment must state that ω-S1's content is scaffold-borrowed and the real S1 is the κ-form. R3's warning stands in the comment: this was the most-wantable resolution; triviality at ω is not vindication.
- **FP-D6 / T11 interface attempt (hostile-first star).** Over arbitrary coherent models (no finiteness hypotheses): attempt the conditional `depth_bound_of_no_total` — an object with unboundedly many pairwise-independent contexts above a fixed fineness threshold has a pattern forced toward totality; contrapositive with A-T gives the bound. The lattice is subsets of pat(x) under inclusion (2.1 §5's sharpened route); "independent" and "fineness" get their provisional definitions **in the file, before any lemma, D15-style**.
  - Budget: a genuine multi-session attempt; partial results (e.g., the two-context case, or the bound under an added uniformity hypothesis) are deliverables, not failures.
  - **Outcomes ledger, written in advance:** full proof → the κ-loan discharges via A-T and Series 2 closes debt-free (falsifying FP-D6 in the good direction). Partial → the loan survives into Series 3, documented, with the obstruction named. Refutation (a coherent model with unboundedly many independent deep contexts and no totality) → the loudest write-up since the Mirror; A-S returns to the table; D19 unaffected (its grounding is C3/T17, not T11).
- **Drop clause:** none for S1_ω (one line); T11 drops to its partials freely after the budgeted attempt.

## Stage 3 — T4 completed and T7 (MUST; FP-D5)

- T4 close-out: `ApproxW` equivalence is delivered (refl/symm/trans, Spec24g); remaining: the profile form's isomorphism-over-pat(w) reading reconciled with the ApproxW definition (a definitional-equivalence lemma or a documented divergence), and O8's all-finite-depths default **ratified in a doc-comment** (owner has not objected; record it as ratified-by-default with a pointer).
- **T7** `identity_is_limit` : x = y ⟺ bisimilar x y ⟺ ∀ w, ApproxW w x y (with the depth-family bridge through EqDepth). Forward directions are `identity_by_unfolding` + monotonicity; the substantive direction is (∀w-agreement → bisimilarity) — route: exhibit the family's joint refinement as a bisimulation, or the EqDepth-at-all-depths → bisimilarity bridge at the ω-tier (finitely-branching behaviors make depth-wise agreement suffice — the classical argument; note the tier honestly).
- This is the framework's oldest strong claim (A3's strong form; 2.0 §2.6 as corrected: identity approached as the limit of observer-local equalities). Its landing or failure is the headline alongside T11.

## Stage 4 — T5 and T10, attempts (SHOULD)

- `closing_denseC` re-attempt with ρ_C and EqDepth in hand; the drop clause has been exercised twice and remains available a third time, but the machinery gap that motivated it is now closed — attempt in earnest, log the outcome.
- T10 partials: `reach_infinite` — the seeds reach infinitely many elements (the tower family is seed-reachable; compose with FP-C1's injectivity). Full ReachableFromSeeds stays open; state any counterexample-shaped obstruction found.

## Stage 5 — the small debts (SHOULD)

- **T13 full** : hearsay derived by induction on chain length, laxity + acquaintance bound (the per-step pieces exist; the induction is the deliverable). D8's reversion clause dies here if it lands.
- **FP-D7 / C2-strong, hostile** : predicted false on Ω_C — exhibit two grounded objects with empty π, or prove it can't be done on the grounded part; either outcome is recorded against 2.2 §1.2.
- **D14(b)** : rate of determination — definition via EqDepth (depth at which an object's unfolding stabilizes relative to a description), plus one monotonicity lemma; the third closure dimension finally gets its instrument.
- **T14d** (MAY, drop freely, final call): the comparative fish/partner witness — the long-deferred corner, offered its last chance in Series 2.

## Stage 6 — the closing statement (MUST; last)

A results section appended to 2.5, plus a Series 2 closing note in the repo (README-adjacent, cold-reader facing), stating: the ledger's final form (one primitive, one axiom, its address, its price); which of T11/T5/T10/C2-strong closed and which carry into Series 3; the κ-loan's end-state per the Stage 2 outcomes ledger; and the standing invariant — **nothing in the mathematics depends on D19; D19 depends on all of it.**

---

## Frozen predictions

FP-D1 through FP-D7 as frozen in 2.5 §6; no additions.

## Deliverable summary

| Stage | Level | Contract items |
|---|---|---|
| 0 | MUST | D25 sweep, glossary note |
| 1 | MUST | V1, P-D19-1/2/3, T19 |
| 2 | MUST/star | S1_ω (honest), T11 attempt + outcomes ledger |
| 3 | MUST | T4 close-out, T7 |
| 4 | SHOULD | closing_denseC, reach_infinite |
| 5 | SHOULD | T13, C2-strong (hostile), D14(b), T14d (MAY) |
| 6 | MUST | closing statement |

Success criterion: Stages 0–3 and 6 land → **Series 2 is closed.** The universe exists, is many, is bridged, and its one irreducible loss is named — with the naming's formal content machine-checked and its independence from the mathematics certified. Whatever T11 leaves open walks into Series 3 in daylight, which is the only way this project has ever carried a debt.
