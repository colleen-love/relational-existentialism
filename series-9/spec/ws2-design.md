# WS2 — The residue breaks the collapse from one position

**Design doc. Series 9, the payoff. Owns: the diagonal residue is distinct from the self-total attempt and FREE (not recoverable from the inspection), derived from ONE position with no second position in the premise — the exact repair of Series 8's circularity (`x↾(x,y) ≠ y↾(y,x)` needed `x ≠ y`). Recovers Series 8's distributed perspective as a special case (mutual residues), not the source.**

*Series 9 is standalone; the semantic import test (`ws4_free_label_is_import`, `ws4_recoverable_not_import`, `Recoverable`, `plainOf`, `labelLoop`) and the coincidence witness are transcribed into `series-9/formal/Series9/ws2.lean`, re-namespaced `Series9.WS2` (see `spec/README.md` §6). WS2's plurality is stated with **the spine's independence as a hypothesis discharged by WS1** (charter §6, protocol §4): the residue breaks the collapse only if the spine is genuinely diagonal (not Coincident), which WS1's `ws1_diagonal_not_bisim` secures. The genuinely new Lean here is `residue` and `ws2_residue_free`; the distributed-perspective recovery re-reads Series 8's `labelLoop`.*

## The object at stake

The charter's Consequence 1 (§2, §5.2): Series 8 sought a distinguisher between two positions (`x↾(x,y)` vs `y↾(y,x)`) and found the premise needed `x ≠ y` — the distinguisher presupposed the plurality. Series 9 relocates it *inside one position*. Given one inspection `insp` on one carrier, the **residue** is the diagonal content no hold holds: `residue insp := diag insp = fun h => ¬ insp h h`. It is (a) **distinct** from every hold's content — `∀ h, insp h ≠ residue insp` — a theorem, derived from the single inspection, no `x ≠ y` in the premise; and (b) **free** — not recoverable from the inspection, because recoverability would put `residue insp` in the range of `insp`, reconstructing the self-total hold the diagonal forbids (WS1). Plurality is the residue made real: the first genuine other-than-this-hold, an interior exterior, from one position.

The design must be scrupulous about the strip test here (the payoff most at risk of being Series 8's free-label import wearing the word "residue"): stripped of "residue"/"diagonal," `ws2_residue_free` is exactly the Cantor fact "`diag insp` is not in the range of `insp`." What makes it *the residue of an incompletable self-inspection* rather than a generic un-hit predicate is that it is the diagonal of the carrier's own inspection (not external data), and that its freeness is the *global* no-self-total-hold fact (WS1), not a local stipulation. WS2 states this distinction and does not oversell it; WS7 adjudicates. The load-bearing repair over Series 8: the residue's distinctness needs **no** second position, so the circularity Series 8 hit is gone.

**Ambient theory.** `spec/README.md` §2.3 (`HoldPred`, `insp`, `diag`, `SelfTotal`), §2.1–§2.2 (carrier, hold, the semantic import test `Recoverable`/`plainOf`/`labelLoop`/`ws4_free_label_is_import`/`ws4_recoverable_not_import`), and WS1's `ws1_no_self_total_hold` / `ws1_diagonal_not_bisim`. All transcribed.

## Candidates

### C1 — The residue is distinct from every hold's content, from one position (the lead)

```lean
def residue {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest := diag insp
theorem ws2_residue_distinct {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ∀ h, insp h ≠ residue insp := by
  intro h hh
  have := congrFun hh h                                -- insp h h = ¬ insp h h
  simp only [residue, diag] at this; tauto
```
The residue is distinct from the content of *every* hold — including the hold itself — and the proof takes one hold `h` and derives `insp h h ↔ ¬ insp h h`. No second position: the distinctness is a fact about one inspection, refuting Series 8's `x ≠ y`-in-the-premise circularity.

- **Ambient:** the reflexive layer; `residue := diag insp`.
- **Success condition:** the term typechecks; the premise contains no `x ≠ y`, so plurality is derived from ONE position (charter §5.2).
- **Failure mode:** *second position smuggled in.* If `residue` were defined using two distinct holds, the repair would fail. It is not: `diag insp` is a function of `insp` alone; the diagonal point `h` in the proof is universally quantified, not a posited second position. WS7 confirms the premise.

**Paper triage.** Decidable: `congrFun` on the assumed equality gives `p ↔ ¬p`. **Winner (plurality from one position).**

### C2 — The residue is FREE: not recoverable from the inspection (the non-circularity core)

```lean
/-- The residue is recoverable iff some hold's content realises it (it is a function of the inspection). -/
def ResidueRecoverable {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ h, insp h = residue insp
theorem ws2_residue_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ResidueRecoverable insp := by
  rintro ⟨h, hh⟩; exact ws2_residue_distinct dest insp h hh
```
Freeness is the negation of recoverability: no hold's content is the residue. Recoverability would put `residue insp` in the range of `insp` — i.e. a hold whose content is the completed self-inspection, which is a self-total hold (WS1). So the residue is free *because* the self-total hold does not exist: freeness is the diagonal, re-read.

- **Failure mode:** *residue recoverable-hence-not-free (charter §5.5).* The named hazard: if the residue were recoverable from the plain relating, it collapses (Series 4/WS4 semantic test) and monism reasserts. The diagonal is the defense: recoverability reconstructs the self-total hold, which `ws1_no_self_total_hold` forbids. This is a *theorem* (`ws2_residue_free`), not a gloss. **Winner (secures C1, the non-circularity core).**

### C3 — Freeness tied to the Series 4/WS4 semantic import test

```lean
theorem ws2_residue_is_import {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    -- the residue is unrecoverable (free) exactly as a free label is an import (semantic test):
    (¬ ∃ h, insp h = residue insp)                                    -- residue not in range of insp
  ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) := by           -- recoverability ⇒ self-total hold
  refine ⟨ws2_residue_free dest insp, ?_⟩
  rintro ⟨h, hh⟩; exact ⟨h, fun g => by rw [hh]⟩
```
The residue's freeness is the same shape as Series 8's `ws4_free_label_is_import`: a content the inspection cannot recover, exactly as the free directed hold is a label the plain relating cannot recover. The second conjunct is the diagonal defense as a theorem: recoverability of the residue reconstructs the self-total hold. This binds Series 9's residue to Series 8's recoverable/free dichotomy — the residue lands on the `ws4_free_label_is_import` horn (free), never the `ws4_recoverable_not_import` horn (recoverable, hence collapsing).

- **Failure mode:** *the analogy is decorative.* The bind is load-bearing only if "recoverable ⇒ self-total" is a theorem, which the second conjunct proves. **Winner (the semantic-test bind).**

### C4 — The residue is a full face, non-empty (no leaf, §4.3 — routed to WS3's NL, previewed here)

```lean
theorem ws2_residue_nonempty {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (hne : ∃ h, ¬ insp h h) :
    ∃ h, residue insp h := hne          -- the residue is inhabited: a hold the inspection does not self-hold
```
The residue is the-me-I-cannot-reach — not nothing, a hold I do not hold (charter §3, (NL)). Its inhabitation: any hold `h` with `¬ insp h h` is in the residue, and on a hold-reflexive carrier such `h` exists (the diagonal is non-vacuous). This previews WS3's (NL) at the level of the static residue.

- **Failure mode:** *the residue is empty (a leaf).* If `insp h h` held for every hold, the residue would be empty — but then `insp` self-holds everything, and the diagonal is vacuous (a self-loop-flavoured degeneracy, §4.4). On a genuinely hold-reflexive carrier (WS1 D5, a rich inspection) the residue is inhabited. Full discharge is WS3's (NL); WS2 previews it. **Retain as the no-leaf preview; WS3 owns the theorem.**

### C5 — Distributed perspective recovered as a special case: mutual residues

```lean
theorem ws2_distributed_special_case (hinf : ℵ₀ ≤ κ) :
    -- Series 8's distributed perspective (labelLoop) embeds as a pair of holds each in the OTHER's residue:
    ∃ (insp : Hold (plainOf (labelLoop hinf)) → HoldPred (plainOf (labelLoop hinf))) (h₁ h₂ : Hold _),
        residue insp h₂ ∧ residue insp h₁ ∧ h₁ ≠ h₂    -- mutual residues: each is the other's blind spot
```
Series 8's two free directed holds (`labelLoop ⟨true⟩` vs `⟨false⟩`) recover as *residues held mutually*: two holds each lying in the other's blind spot. Distributed perspective is not the source of plurality (as Series 8 took it) but a *special case* of the residue — residues made mutual (charter §2, Consequence 1). This is the precise sense in which Series 9 subsumes Series 8's WS2.

- **Failure mode:** *the recovery is forced/artificial, or the residue does not genuinely subsume distributed perspective (charter §9, open risk).* The honest position: mutual residues are *a* configuration the residue admits, and the `labelLoop` pair instantiates it; whether *every* distributed perspective is mutual residues is left open (charter §9, "whether Series 8's distributed perspective genuinely recovers"). WS2 claims the special case, not the universal. **Winner (the special-case recovery), scoped honestly.**

### C6 — The abstract form: freeness IS the diagonal (bridge, not a payoff)

```lean
theorem ws2_free_iff_no_self_total {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ResidueRecoverable insp) ↔ (¬ ∃ t, SelfTotal insp t)
```
Freeness of the residue and non-existence of the self-total hold are *equivalent* — freeness is the diagonal, re-read. True but definitional (both unfold to the diagonal), so it is the coincidence-rule trap in miniature: `ws2_residue_free` is `ws1_no_self_total_hold` wearing "free."

- **Failure mode:** *unfolds to the spine.* This is the honest disclosure, not a hidden defect: WS2's freeness *is* WS1's spine re-read, and that is fine — the payoff is that plurality follows from the diagonal from ONE position. **Keep as the bridge lemma naming what freeness means; not a standalone payoff.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | residue distinct from every hold, one position | `congrFun`, `diag` | yes | **win (plurality from one position)** |
| C2 | residue is free (not recoverable) | `ws2_residue_distinct` | yes | **win (non-circularity)** |
| C3 | freeness = import; recoverable ⇒ self-total | `SelfTotal`, semantic test | yes | **win (semantic-test bind)** |
| C4 | residue inhabited (no-leaf preview) | rich `insp` | yes (with hold-reflexive hyp) | preview → WS3 (NL) |
| C5 | distributed perspective = mutual residues | `labelLoop`, `plainOf` | yes (special case) | **win (special-case recovery), scoped** |
| C6 | freeness ↔ no self-total hold | unfolds to spine | yes but definitional | bridge only |

## Winning candidates: C1+C2+C3 (the payoff and its freeness), C5 (distributed recovery); C4 previews WS3, C6 the bridge

### Definitions and obligations (cite `spec/README.md` §2; consume WS1)

```lean
namespace Series9.WS2
-- carrier + reflexive layer (HoldPred, insp, diag, SelfTotal), ws1_no_self_total_hold,
-- ws1_diagonal_not_bisim from WS1; Recoverable, plainOf, labelLoop, ws4_free_label_is_import,
-- ws4_recoverable_not_import — transcribed (README §6).

def residue {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest := diag insp
def ResidueRecoverable {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : Prop :=
  ∃ h, insp h = residue insp

/-- **D1 — plurality from one position (C1).** The residue is distinct from every hold's content, with
    NO second position in the premise — the repair of Series 8's `x↾(x,y) ≠ y↾(y,x)` needing `x ≠ y`. -/
theorem ws2_residue_distinct {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ∀ h, insp h ≠ residue insp := by
  intro h hh; have := congrFun hh h; simp only [residue, diag] at this; tauto

/-- **D2 — the residue is free (C2, non-circularity core).** Not recoverable from the inspection;
    recoverability would reconstruct the self-total hold, which the diagonal (WS1) forbids. -/
theorem ws2_residue_free {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ResidueRecoverable insp := by
  rintro ⟨h, hh⟩; exact ws2_residue_distinct dest insp h hh

/-- **D3 — freeness is an import; recoverability ⇒ self-total hold (C3, the semantic-test bind).** The
    residue lands on the `ws4_free_label_is_import` horn (free), never `ws4_recoverable_not_import`. -/
theorem ws2_residue_is_import {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t) := by
  refine ⟨ws2_residue_free dest insp, ?_⟩
  rintro ⟨h, hh⟩; exact ⟨h, fun g => by rw [hh]⟩

/-- **D4 — from one position, non-circular, tied to the independent spine (the headline).** Plurality
    exists (the residue is distinct and free) from ONE inspection, and it is genuine plurality (not the
    Series 8 coincidence) BECAUSE the spine is diagonal-not-bisimulation (WS1 D3, consumed here). -/
theorem ws2_from_one_position {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (∀ h, insp h ≠ residue insp)            -- distinct, from one position
  ∧ (¬ ResidueRecoverable insp)             -- free
  ∧ (¬ ∃ t, SelfTotal insp t) :=            -- and the spine that secures it is the independent diagonal
  ⟨ws2_residue_distinct dest insp, ws2_residue_free dest insp,
   ws1_no_self_total_hold dest insp⟩

/-- **D5 — distributed perspective as a special case (C5), scoped honestly.** Series 8's `labelLoop`
    pair recovers as mutual residues; NOT claimed universal (charter §9). -/
theorem ws2_distributed_special_case (hinf : ℵ₀ ≤ κ) :
    ∃ (insp : Hold (plainOf (labelLoop hinf)) → HoldPred (plainOf (labelLoop hinf)))
      (h₁ h₂ : Hold (plainOf (labelLoop hinf))),
        residue insp h₂ ∧ residue insp h₁ ∧ h₁ ≠ h₂ := …
```

**D1/D2/D3** are the payoff: plurality from one position (D1), free (D2), on the free-import horn (D3). The mathematical work is the diagonal, re-read as distinctness and freeness. **D4** is the headline, and its third conjunct makes the dependency on WS1 explicit: the residue is genuine plurality *because* the spine is the independent diagonal (`ws1_diagonal_not_bisim`), not the coincidence. The cross-workstream review (protocol §D) must confirm this edge — WS2's plurality laundered through a *Coincident* spine would be Series 8's plurality re-described, not the repair. **D5** recovers distributed perspective as a special case, scoped away from the universal (charter §9's open risk).

## Outcome classes (per charter §7)

- **Discharged (plurality from one position):** D1, D2, D3, D4 — the residue is distinct and free from a single inspection, no second position, tied to the independent spine. This is the direct repair of Series 8's circularity (charter §8.2).
- **Discharged (special case):** D5 — distributed perspective recovers as mutual residues, scoped to the `labelLoop` witness.
- **Coincident (inherited from WS1, if the spine is):** if WS1's spine comes back Coincident, WS2's plurality is Series 8's plurality re-described (laundered through the coincidence), reported honestly and routed to WS7. Not expected: WS1 D3 secures independence.
- **Failed / monismStands (pre-registered honest alternative):** if the residue were found *recoverable* after all (freeness defined-in, or the residue a function of the plain relating), then recoverability reconstructs the self-total hold (D3), contradicting WS1 — so the only way this fails is if WS1 fails. Routed to WS7 → `monismStands`. Not expected: freeness is a built theorem (D2), the diagonal the same non-circularity shape.
- **Partial (pre-registered, charter §9):** the *universal* "every distributed perspective recovers as mutual residues" is open (charter §9); D5 claims only the special case, the universal a defended thesis (WS6).
- **Strip test.** Delete **"residue"/"diagonal"** from `ws2_residue_free` and the statement is the bare **`diag insp ∉ Set.range insp`** — a Cantor "the diagonal content is not realised" fact. The payoff **survives the strip** as a range/fixed-point fact — so the *mathematical* content is the diagonal's un-hit content, and "residue / the-me-I-cannot-reach / free interior exterior" is the earned reading (the un-hit content is the carrier's own diagonal, its freeness the global no-self-total-hold fact of WS1). WS2 does **not** claim the strip leaves nothing; it claims the residue is a genuine plurality-from-one-position fact and names the interpretive surplus. What the strip does **not** remove is the load-bearing structural gain over Series 8: the distinctness needs **no second position** (delete `residue` from `ws2_residue_distinct` and the premise still has no `x ≠ y`) — that is the earned repair, and WS7 weighs it directly.

## Deliverable

`series-9/formal/Series9/ws2.lean`: transcribed semantic-import machinery (README §6); `residue`, `ResidueRecoverable`; `ws2_residue_distinct` (D1), `ws2_residue_free` (D2), `ws2_residue_is_import` (D3), `ws2_from_one_position` (D4), `ws2_distributed_special_case` (D5). Axiom check: `#print axioms ws2_residue_free` reduces through `ws2_residue_distinct` to `propext` / the standard three. **Depends on WS1** (`ws1_no_self_total_hold` and `ws1_diagonal_not_bisim` secure the freeness and its independence); the ledger records the edge. This is the payoff most at risk of the strip (charter's own note); WS7 weighs whether the interior-exterior reading is earned or the bare Cantor fact.
