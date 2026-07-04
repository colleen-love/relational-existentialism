# 2.03-mechanization-b — Work Order: Run the Trials (B1, the Forcing Lemma, and the Anti-Mirror Spot-Check)

**This document describes:** `scratch/formal/Spec203b.lean` (new file; imports `Spec201`, `Spec201c`, `Spec203`)
**Normative sources:** `scratch/spec/2-03.md` **§5 (The Trials, R4)** — the protocol, candidates, battery, and frozen predictions — plus §4 (D20/D21). Specs win; report discrepancies.
**Audience:** Claude Code. All conventions in force. **This file is an experiment's lab notebook: the predictions in 2-03 §5.3 are frozen; your job is to make each one true or false, and every doc-comment must say which prediction its theorem confirms or refutes.** Do not soften a refutation; a surprised prediction is the trial working.

---

## 1. Purpose and scope

Run gate B1 (the F(1)/Parmenides check, D20) on every entrant, symmetrically; prove the Forcing Lemma at whatever generality closes; run the B2 anti-Mirror spot-check on candidate (C) **before any (C)-development** (2-03 §5.4: the wanted candidate is scrutinized first).

| ID | Name | Prediction under test (2-03 §5.3) | Priority |
|----|------|-----------------------------------|----------|
| B1-G | Control: the collapsed G | fails (proved: `G_unit_subsingleton`, Spec203) — cite, don't reprove | MUST (citation) |
| B1-A | Pure (A), division-over-pattern | **fails by collapse** (`Subsingleton`) | MUST |
| B1-B | (B), inclusion, T possibly empty | **fails by collapse** (`Subsingleton`) | MUST |
| B1-Bs | (B)-strict, both sides nonempty | **fails by emptiness** (`IsEmpty`) — "the arrow cannot turn" | MUST |
| B1-C | (C), relations over `Sym2 (O ⊕ R)` | **passes** (`¬ Subsingleton` at the relation sort over the point-pair) | MUST |
| B1-A2 | The evasion-clause entrant | **passes** (`¬ Subsingleton`), powered by ∅ — hazard on record | MUST |
| FL | The Forcing Lemma, class-level | derived division-material is forced over the point | SHOULD-strong |
| B2-C | Anti-Mirror spot-check for (C) | two states separated by a depth-1 sort-composition invariant | MUST |
| DOC | Results annotation + spec labels | — | MUST |

**Out of scope:** νF construction for any candidate (the winner's construction is its own order, via the Spec201c template); B3–B7 beyond what lands incidentally (spec-level, later spot-checks); the coherence design for (C) (O-2-03-1b — flagged, not solved); anything about D19.

## 2. The entrants, transcribed to Lean

Fix shorthand in a fresh namespace:

```lean
namespace RelEx.Trials
/-- Finite nonempty subsets, as the standing subtype. -/
def PfNe (α : Type) : Type := {S : Set α // S.Finite ∧ S.Nonempty}
```

**B1-A (pure division over the pattern).** Per 2-03 §5.1(A), evaluated at the one-point pair directly — the relation sort there is `Sym2 PUnit`, a subsingleton (Spec203's helper; import and reuse). Take the charitable-to-(A) reading in which the division is defined **on the pattern's members** (do not let off-member junk manufacture a fake pass — kill (A) fairly or be surprised fairly):

```lean
def AttA : Type :=
  Σ S : PfNe (Sym2 PUnit), ∀ _r : ↥S.1, {T : Set (Sym2 PUnit) // T ⊂ S.1}

theorem B1_A : Subsingleton AttA := by
  sorry
```

Plan: `S.1`, nonempty inside a subsingleton type, is forced to the universal singleton (`Set.eq_univ_of_forall` through subsingleton membership); the only proper subset of a singleton is `∅`, so each `T` is forced; conclude by `Sigma`/`Subtype`/`funext` extensionality with everything forced. Record the restatement (division on `↥S.1` rather than a total function) in the mapping table as the charitable reading. One line then lifts to the pattern level if you also state `Subsingleton (PfNe AttA)` — optional; `Subsingleton AttA` is the load-bearing fact.

**B1-B and B1-Bs.**

```lean
def AttB : Type := { p : Set (Sym2 PUnit) × Set (Sym2 PUnit) //
  p.1.Finite ∧ p.1.Nonempty ∧ p.2 ⊂ p.1 }              -- T possibly empty
def AttBs : Type := { p : Set (Sym2 PUnit) × Set (Sym2 PUnit) //
  p.1.Finite ∧ p.1.Nonempty ∧ p.2.Nonempty ∧ p.2 ⊂ p.1 } -- both nonempty

theorem B1_B : Subsingleton AttB := by sorry
  -- S forced to the singleton; T ⊂ S forces T = ∅; one element.
theorem B1_Bs_empty : IsEmpty AttBs := by sorry
  -- a nonempty set strictly inside a nonempty subset of a subsingleton: impossible.
```

`B1_Bs_empty`'s doc-comment carries its name from 2-03 §5.3: **the arrow cannot turn** — austere properness forbids the One from attending at all; a universe built on strict inclusion alone is *empty* at the fiber where T1 demands the self-loop. Both B-failure-modes (collapse and emptiness) are thereby on record.

**B1-C.** The two-sorted test evaluates at the one-point *pair*; the relation component is `Sym2 (O ⊕ R)`:

```lean
theorem B1_C : ¬ Subsingleton (Sym2 (PUnit ⊕ PUnit)) := by
  sorry -- s(Sum.inl u, Sum.inl u) ≠ s(Sum.inl u, Sum.inr u): separate by
        -- membership (`Sum.inr u ∈` one, not the other) or `Sym2.mk`-injectivity
        -- up to swap; verify lemma names with exact?.
```

Doc-comment: over the One, the tower already distinguishes *the self-relation* from *the bearing on the self-relation* — sort-composition of endpoints is observable structure, and F(1)'s inhabitants are the different ways the One can turn upon its own turning. (The tower's infinitude is a spec-level remark; do not chase it here.)

**B1-A2 (the evasion-clause entrant, 2-03 §5.1/§5.3).**

```lean
def AttA2 (X : Type) : Type :=
  { p : Set (Sym2 X) × Set (Sym2 X) // p.1.Finite ∧ p.2.Finite ∧ p.2.Nonempty }
  -- p.1 = H (grasp, may be ∅); p.2 = M (remainder, mandatory)

theorem B1_A2 : ¬ Subsingleton (AttA2 PUnit) := by
  sorry -- ⟨(∅, {r̂})⟩ vs ⟨({r̂}, {r̂})⟩ differ in the first component.
```

Doc-comment MUST carry the hazard verbatim from 2-03 §5.3: the pass is **powered by ∅** — the ∅/nonempty bit is the individuating resource, which the framework's own D4 analysis names the primordial atom; the B7 audit is predicted to eliminate A2 on the framework's own grounds. This theorem is *evidence for that elimination*, not a victory for A2: read the two witnesses — their entire difference is emptiness.

## 3. FL — the Forcing Lemma (SHOULD-strong; budget a half-day)

The honest formalization work is finding the right statement: a family-of-subsets type over a subsingleton aspect-space `α`, each component pinned by a constraint drawn from {nonemptiness (which forces `= univ`), properness-inside-a-pinned-component (which forces `= ∅`)}, proved `Subsingleton`. Deliver the strongest version that closes and **derive `B1_A` and `B1_B` from it as instances** — that derivation is the acceptance test; if the instances don't follow, the generality is wrong. If after a half-day no class-level form closes: ship the instance proofs (already MUSTs), state the lemma as a documented conjecture at the file's foot, and record the drop. NOT acceptable: a "lemma" tuned so narrowly it is the two instances in a trenchcoat. Doc-comment carries 2-03 §5.3's moral: derived division-material as such is forced over the point; the escapes are exactly relational self-reference (C) and the forbidden coin (A2).

## 4. B2-C — the anti-Mirror spot-check (before any (C)-development)

```lean
/-- Candidate (C)'s raw shape: endpoints drawn from either sort. Coherence and
parthood design are OPEN (2-03 O-2-03-1b); this structure exists only to run
the anti-Mirror check on raw behavior. -/
structure RawC where
  O : Type
  R : Type
  endpoints : R → Sym2 (O ⊕ R)
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty

/-- Depth-1 invariant: some pattern-member bears on a relation. -/
def HasMetaBearing (A : RawC) (x : A.O) : Prop :=
  ∃ r ∈ A.pat x, ∃ q : A.R, Sum.inr q ∈ A.endpoints r

theorem B2_C_separation :
    ∃ (A : RawC) (x y : A.O), HasMetaBearing A x ∧ ¬ HasMetaBearing A y := by
  sorry
```

Construction plan: `O := Bool`, `R := Bool`; `endpoints true := s(Sum.inl true, Sum.inr false)` (the meta-bearing), `endpoints false := s(Sum.inl true, Sum.inl false)` (ordinary object-object relation); `pat true := {true}`, `pat false := {false}`; then `x := true` has the bearing, `y := false` does not (both endpoints of its sole pattern-member are `inl` — `Sym2` membership case-split). Doc-comment: this is the theorem the collapsed universe could not have, checked for (C) *before* any (C)-development per the wantability-hazard clause — the candidate both collaborators now want is the one scrutinized first. **Stretch (drop freely with note):** state the natural `IsBisimC` (Egli–Milner over patterns with `Sym2`-lifting over `O ⊕ R`) and prove `HasMetaBearing` is preserved by it — full bisimulation machinery otherwise belongs to (C)'s own spec if it wins; the separation-by-invariant above is the load-bearing content.

## 5. Build, verify, deliver

Standard: clean build, no `sorry`, axiom audit (the B1 block should be choice-light; `B1_Bs_empty` and `B1_C` plausibly axiom-free — report), mapping table with the prediction-outcome column:

```
-- 2-03 §5.3 predictions ↔ outcomes (fill in: CONFIRMED / REFUTED)
-- Forcing (A):   B1_A    Subsingleton   — predicted fail-by-collapse   → ____
-- Forcing (B):   B1_B    Subsingleton   — predicted fail-by-collapse   → ____
-- Arrow:         B1_Bs   IsEmpty        — predicted fail-by-emptiness  → ____
-- Tower:         B1_C    ¬Subsingleton  — predicted PASS               → ____
-- Evader:        B1_A2   ¬Subsingleton  — predicted pass (∅-powered)   → ____
-- Forcing Lemma: FL                     — class-level                  → ____ (or dropped)
-- Anti-Mirror:   B2_C_separation        — predicted separation         → ____
```

## 6. DOC (MUST)

- `2-03.md`: append **§5.6 Results** (clearly post-hoc-marked, per the freeze rule) transcribing the outcome column; each REFUTED prediction gets one honest sentence.
- `2-00.md` §5: no theorem-label changes (the trials decide a functor, not a 2-00 target); add one line under T2's entry: `Trials in progress (2-03 §5); B1 outcomes recorded (Spec203b).`
- `2-02.md` §7: note the trials as the current gate on the corrected-functor spec.

---

*End of work order. Whatever the outcomes, this file is the first page of the framework's experimental era: predictions frozen, hazards named, the wanted candidate scrutinized first, the forbidden coin tested in the open. If the predictions all confirm, the fork resolves by elimination — twice over for the (A)-family — and the owner's original axiom, the one reduced away at the dyad ruling, returns as the arena not because either collaborator wanted it back, but because everything else provably collapses, empties, or pays with the atom.*
