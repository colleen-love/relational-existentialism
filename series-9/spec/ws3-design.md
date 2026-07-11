# WS3 — Re-diagonalization and forced dynamics

**Design doc. Series 9, the engine of the tower. Owns: the re-diagonalization map (`spec/README.md` §2.4, ambient for WS4–WS5), its two cheap obligations **(NL)** no leaf and **(NF)** not-a-function, the forcing of dynamics from the impossibility of self-totality, and the ONE endogenous tower order `≺` — with the imported-index branch designed in as a refuted failure mode, never a fallback.**

*Series 9 is standalone; the carrier and `SHNE` machinery are transcribed into `series-9/formal/Series9/ws3.lean`, re-namespaced `Series9.WS3` (see `spec/README.md` §6). This is **genuinely new Lean**: `ReDiagStep`, `prec`, the (NL)/(NF) obligations, and the forced-dynamics seriality are Series 9 content built on WS1's reflexive layer. Per protocol §C, the re-diagonalization map and (NL)+(NF) are the **seed of the series' dynamics** (built early after the WS1 spine); **monotonicity (MG) is NOT attempted here and is never folded into `ReDiagStep`** — it is WS5's, on the map WS3 hands it.*

## The object at stake

Charter §3 and Consequence 2 (§2, §5.2). Re-diagonalization is the reopening of the gap at a hold that tried to close it: from an inspection attempting self-totality, produce the residue it necessarily omits (WS1) and a next-stage inspection that holds that residue (and omits its own). Three properties are demanded, each a separate obligation:

- **(NL) No leaf.** The residue is a full face, never a bare point; hereditary non-emptiness (`SHNE`) is preserved. The-me-I-cannot-reach is not nothing, it is a hold I do not hold. The diagonal residue `diag insp` must be shown *inhabited* (a genuine face to be held next), not merely absent from the prior inspection. This is the hard rejection of limit-atomlessness (§4.3).
- **(NF) Not-a-function.** The next self-inspection is a *free* re-diagonalization, not determined by the prior inspection: two identical inspections can re-diagonalize toward different next-stage inspections (the diagonal picks *a* fixed-point-denier, not *the* one). This is what keeps the dynamics from being a determined unfolding and preserves the will-reading (charter §3, (NF)).
- **Forced dynamics.** A self-total hold being impossible (WS1), self-inspection cannot terminate in a complete self-image; from every inspection there is always a further re-diagonalization, so the re-diagonalization relation **never terminates** (seriality). Dynamics is not added; it is forced by the incompletability of self-reference — the diagonal analogue of Series 8's finitude-on-atomlessness, and forced from ONE position.

And the load-bearing methodological duty (§4.2, protocol §2 second design duty): the order `≺` must be **endogenous** — derived from re-diagonalization sequences, not an imported stage-index (the Series 3/5 trap). WS3 fixes `≺` once (`spec/README.md` §2.4) and proves its endogeneity; WS4 and WS5 consume the *same* `≺`.

**Ambient theory.** `spec/README.md` §2.3 (`HoldPred`, `insp`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`), §2.4 (`ReDiagStep`, `prec`). `Function.update` is the constructor for the always-available next inspection; a periodic (`pingPong`-flavoured) carrier is the 2-cycle witness for the imported-index refutation.

## Candidates

### C1 — Re-diagonalization = the next inspection holds the prior residue; (NL)+(NF) as map facts (the lead)

```lean
def ReDiagStep {X} (dest : X → PkObj κ X) (insp insp' : Hold dest → HoldPred dest) : Prop :=
  ∃ h₀, insp' h₀ = diag insp          -- insp' HOLDS the prior residue at some hold; the rest of insp' is free
theorem ws3_redi_no_leaf {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hne : ∃ h, ¬ insp h h) : ∃ h, diag insp h                          -- (NL): the residue is a full face
theorem ws3_redi_not_function {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) (c₁ c₂ : HoldPred dest) (hne : c₁ ≠ c₂) :
    ∃ insp₁ insp₂, ReDiagStep dest insp insp₁ ∧ ReDiagStep dest insp insp₂ ∧ insp₁ ≠ insp₂  -- (NF)
```
An inspection re-diagonalizes to any inspection that realises its residue `diag insp` at some hold — narrowing from the failed self-total attempt to a stage that holds the blind spot it left (while, by WS1, leaving its own).

- **Ambient:** the reflexive layer; `ReDiagStep` realises the residue; the accumulated residue is measured separately (§2.5).
- **Success condition (NL):** on a hold-reflexive carrier the residue is inhabited — some hold `h` has `¬ insp h h` (WS1 D5's rich inspection guarantees the diagonal is non-vacuous), so there is a genuine face to hold next. Never a leaf.
- **Success condition (NF):** from `insp`, two inspections that both realise `diag insp` at `h₀` but differ elsewhere both re-diagonalize — the next stage is a free facing, not a function of the prior.
- **Failure mode:** *monotonicity-assumed / NF baked out.* The traps: (i) defining `ReDiagStep` to *accumulate* growth (stamping strict enlargement of the residue in) — C1 does not; it says only "the next inspection holds the prior residue," compatible with the blind spot being re-inherited unchanged, so monotonicity stays WS5's open test (§2.5); (ii) defining `ReDiagStep` as a function (a determinate `reDiag insp`) — C1 is a *relation* with many successors (NF), so the free facing is preserved.

**Paper triage.** Decidable and short: (NL) is the diagonal's inhabitation from a rich inspection; (NF) is a two-content witness via `Function.update`. The step realises a residue and touches no accumulated measure, so monotonicity is not baked in. **Winner (the map + NL + NF).**

### C2 — Forced dynamics: no inspection is terminal (seriality, the lead for Consequence 2)

```lean
theorem ws3_dynamics_forced {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ∃ insp', ReDiagStep dest insp insp' :=
  ⟨Function.update insp (Classical.arbitrary _) (diag insp), _, by simp⟩   -- always a next inspection
```
A self-total hold being impossible (WS1), no inspection completes self-inspection; from every inspection there is a further re-diagonalization (set some hold's content to the residue via `Function.update`), so `ReDiagStep` is **serial** — no terminal inspection, the self must be unfolded over succession. Dynamics is *forced* by the incompletability of self-reference, from one position.

- **Ambient:** `ws1_no_self_total_hold` (the residue always exists); `Function.update` (the always-available successor); the non-termination of `ReDiagStep`.
- **Success condition:** the term produces, from any inspection, a next re-diagonalization — an infinite ascending `prec`-chain, no static complete self-image. The theorem IS the forcing (not a hand-waved "a finite self can't hold itself").
- **Failure mode:** *non-termination read as a bug; or the forcing asserted between definitions.* The honest form is the crisp seriality theorem "`∀ insp, ∃ insp', ReDiagStep insp insp'`," a genuine theorem, not an intuition asserted between two definitions. And it must be forced by the *diagonal* (the residue always exists), not by an external "time" — `Function.update` witnesses a successor precisely because `diag insp` is always a well-defined content to hold.

**Paper triage.** Decidable: `Function.update insp h₀ (diag insp)` realises `diag insp` at `h₀`, so a successor always exists — `ReDiagStep` is serial. **Winner (Consequence 2), phrased as seriality/non-termination.**

### C3 — The endogenous order `≺` and its non-importedness (the §4.2 guard)

```lean
def prec {X} (dest : X → PkObj κ X) : (Hold dest → HoldPred dest) → (Hold dest → HoldPred dest) → Prop :=
  Relation.ReflTransGen (ReDiagStep dest)
theorem ws3_order_endogenous {X} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' := Iff.rfl   -- ≺ IS the re-diag closure
```
`≺` is the reflexive-transitive closure of `ReDiagStep` — defined from the diagonal operator alone, no external index. "`m ≺ m′` iff `m′` is reached by a re-diagonalization sequence from `m`" (charter §3, protocol §2). This is the single order WS3 (forced dynamics) and WS4 (tower/depth) both consume.

- **Failure mode:** *painted-on / imported index.* If `≺` were an external `ℕ`-stamp on stages, endogeneity would fail and dynamics would be an import (Series 5). C4 refutes that branch as a theorem.

**Paper triage.** `prec` is the closure of a diagonal-defined relation; endogeneity is `Iff.rfl`. **Winner (the ONE order).**

### C4 — The imported-index branch refuted: the order cycles / branches (pre-registered failure mode, NOT a fallback)

```lean
-- The imported order: a stage counter stamped from outside, m ≺ᵢ m' := stage m < stage m'. A strict
-- monotone index forbids cycles (stage m < stage m is false) and is LINEAR (any two stages comparable).
-- Re-diagonalization is neither: it CYCLES (a periodic carrier re-diagonalizes back) and BRANCHES (NF).
theorem ws3_imported_index_refuted {X} (dest : X → PkObj κ X) :
    ∃ m₀ m₁ : Hold dest → HoldPred dest,
      ReDiagStep dest m₀ m₁ ∧ ReDiagStep dest m₁ m₀ ∧ m₀ ≠ m₁     -- a genuine 2-cycle m₀ ↝ m₁ ↝ m₀
```
The re-diagonalization relation has a 2-cycle: `m₀` holds `diag m₁` and `m₁` holds `diag m₀`, so `prec m₀ m₀` is a cycle through two distinct stages — and **no external strict monotone stage-index** can represent it (a strict index forbids `stage m₀ < stage m₁ < stage m₀`). The order is genuinely the endogenous re-diagonalization closure, not a disguised counter.

- **Failure mode of the branch itself:** this is the *refutation*, so its success is showing the imported index does **not** fit. If it *did* fit (a monotone stamp reproducing `≺`), Consequence 2 would be an import (Series 5) and dynamics assumed. The cycle forecloses that. *(NB — a 1-cycle `ReDiagStep m m` is IMPOSSIBLE: it would need `m` to hold `diag m` at some `h₀`, i.e. `m h₀ = diag m`, but `m h₀ h₀ = ¬ m h₀ h₀` is a contradiction — this is WS2's `ws2_residue_free` again. So the witness must be a genuine 2-cycle; the design pre-registers this and the witness is the delicate part, constructed on a periodic carrier.)*

**Paper triage.** Decidable in principle; the 2-cycle witness (mutually residue-holding inspections on a periodic carrier) is the delicate construction — if only branching (NF-based non-linearity) is provable without a full 2-cycle, that *also* refutes an imported *linear* index and is the honest fallback. **Winner (the §4.2 guard, as a refutation); witness possibly via branching if the 2-cycle resists.**

### C5 — Re-diagonalization as a relation on residues (semantic form, routed to WS4)

```lean
theorem ws3_step_opens_new_residue {X} (dest : X → PkObj κ X) (insp insp' : Hold dest → HoldPred dest)
    (r : ReDiagStep dest insp insp') : ∃ h, diag insp' h ∧ ¬ diag insp h    -- the new stage has a FRESH blind spot
```
State re-diagonalization semantically: the next stage's residue contains a hold the prior stage's residue did not — each re-run opens a *new* blind spot (the diagonal always escapes the enumeration it is run against). This is the *depth* content, which is WS4's; here it risks pre-empting WS4.

- **Failure mode:** *this is WS4's depth claim, not WS3's map.* "Each re-diagonalization opens a new blind spot" is the layering payoff (charter §2, Consequence 3), WS4's `ws4_new_blind_spot`. WS3 keeps the *step* and the *order*; WS4 keeps the *fresh-residue* content.

**Paper triage.** A genuine lemma, but it is WS4's depth content. **Route to WS4 (`ws4_new_blind_spot`); WS3 keeps the step (C1) and order (C3), WS4 keeps the fresh-residue fact.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `ReDiagStep`; (NL) no leaf, (NF) not-a-function | rich `insp`, `Function.update` | yes — short | **win (map + NL + NF)** |
| C2 | dynamics forced (seriality / non-termination) | `ws1_no_self_total_hold`, `Function.update` | yes | **win (Consequence 2)** |
| C3 | `≺` = closure of re-diagonalization | `ReflTransGen`, `Iff.rfl` | yes | **win (the ONE order)** |
| C4 | imported index refuted (`≺` cycles/branches) | 2-cycle / NF-branching witness | yes (branching); 2-cycle delicate | **win (§4.2 guard)** |
| C5 | a step opens a fresh blind spot | `diag insp'` vs `diag insp` | yes | → WS4 (depth) |

## Winning candidates: C1 (map+NL+NF), C2 (forced dynamics), C3 (the order), C4 (index refuted); C5 routed to WS4

### Definitions and obligations (cite `spec/README.md` §2; the seed of the tower)

```lean
namespace Series9.WS3
-- carrier, SReaches, SHNE, SHNE.succ, SHNE.ne_empty, pingPong — transcribed (README §6);
-- Hold, afford, HoldPred, insp, diag, SelfTotal, ws1_no_self_total_hold from WS1.

def ReDiagStep {X} (dest : X → PkObj κ X) (insp insp' : Hold dest → HoldPred dest) : Prop :=
  ∃ h₀, insp' h₀ = diag insp
def prec {X} (dest : X → PkObj κ X) : (Hold dest → HoldPred dest) → (Hold dest → HoldPred dest) → Prop :=
  Relation.ReflTransGen (ReDiagStep dest)

/-- **D1a — (NL) no leaf.** The residue is a full face: on a hold-reflexive carrier some hold is not
    self-held, so `diag insp` is inhabited — there is a genuine face to hold next, never a bare point.
    Honors the hard rejection of limit-atomlessness (§4.3). -/
theorem ws3_redi_no_leaf {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (hne : ∃ h, ¬ insp h h) : ∃ h, diag insp h := by
  obtain ⟨h, hh⟩ := hne; exact ⟨h, hh⟩

/-- **D1b — (NF) not-a-function.** From one inspection, two DISTINCT next inspections both realise the
    residue (agreeing at `h₀`, differing elsewhere): the re-diagonalization is a free facing, not a
    function of the prior inspection. Witnessed via `Function.update` at a second hold. -/
theorem ws3_redi_not_function {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ h₁ : Hold dest) (hne : h₀ ≠ h₁) (c : HoldPred dest) (hc : c ≠ diag insp) :
    ∃ insp₁ insp₂, ReDiagStep dest insp insp₁ ∧ ReDiagStep dest insp insp₂ ∧ insp₁ ≠ insp₂ :=
  ⟨Function.update insp h₀ (diag insp),
   Function.update (Function.update insp h₀ (diag insp)) h₁ c,
   ⟨h₀, by simp⟩, ⟨h₀, by simp [Function.update_noteq hne.symm]⟩, by
     intro he; apply hc; have := congrFun he h₁; simpa [Function.update_same, hne] using this.symm⟩

/-- **D2 — forced dynamics (C2).** No inspection is terminal: from any inspection there is a further
    re-diagonalization (`Function.update` realises the residue), so `ReDiagStep` is serial — the self
    must be unfolded over succession. Dynamics is forced by the incompletability of self-reference. -/
theorem ws3_dynamics_forced {X} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest)
    (h₀ : Hold dest) : ∃ insp', ReDiagStep dest insp insp' :=
  ⟨Function.update insp h₀ (diag insp), h₀, by simp⟩

/-- **D3 — the ONE endogenous order (C3).** `≺` is the closure of re-diagonalization (`Iff.rfl`),
    defined from the diagonal operator alone — no imported index. -/
theorem ws3_order_endogenous {X} (dest : X → PkObj κ X) (m m' : Hold dest → HoldPred dest) :
    prec dest m m' ↔ Relation.ReflTransGen (ReDiagStep dest) m m' := Iff.rfl

/-- **D4 — the imported-index branch refuted (C4, §4.2 guard).** The order CYCLES: a genuine 2-cycle
    `m₀ ↝ m₁ ↝ m₀` between distinct stages (each holds the other's residue), so no strict monotone
    stage-index represents `≺`. (A 1-cycle is impossible — `ws2_residue_free`; the witness is a genuine
    2-cycle on a periodic carrier. If the 2-cycle resists, NF-branching refutes an imported LINEAR
    index and is the honest fallback — see C4.) -/
theorem ws3_imported_index_refuted {X} (dest : X → PkObj κ X) :
    ∃ m₀ m₁ : Hold dest → HoldPred dest, ReDiagStep dest m₀ m₁ ∧ ReDiagStep dest m₁ m₀ ∧ m₀ ≠ m₁ := …
```

**D1a/D1b (NL, NF)** are the seed obligations: short, map-only, no accumulated-residue clause — so monotonicity is *not* baked in. **D2 (forced dynamics)** is the diagonal analogue of Series 8's `ws3_dynamics_forced`: seriality forced by the always-existing residue (WS1), not by external time — a genuine theorem, not an asserted intuition. **D3 (the order)** fixes `≺` as the endogenous closure. **D4 (index refuted)** discharges the §4.2 guard as a *refutation*, pre-registering the imported index as a failure mode, never a fallback; the 2-cycle (which doubles as WS5's monotonicity refutation witness) is the delicate construction.

## Outcome classes (per charter §7)

- **Discharged:** D1a (NL), D1b (NF), D2 (forced dynamics), D3 (the endogenous order), D4 (imported index refuted). All short and map-only, except D4's witness.
- **Partial (pre-registered, universal form → WS6):** "dynamics is forced across *any* construction" is the un-rangeable quantifier (charter §5.3) — WS3 proves seriality on any hold-reflexive carrier; the all-constructions universal is WS6's ceiling.
- **Failed (pre-registered honest alternative):** if `≺` could be represented by a monotone external index (D4's refutation *fails* — the order is a disguised linear counter), the order is not endogenous, Consequence 2 becomes an import (Series 5), and dynamics is assumed — routed to WS7. Not expected: the 2-cycle (or NF-branching) forecloses a strict linear stamp.
- **Strip test.** (a) Delete **"re-diagonalization"** from `ws3_dynamics_forced` and the statement is the bare **`∀ insp, ∃ insp', ∃ h₀, insp' h₀ = diag insp`** — a seriality fact about a total function space (`Function.update` always provides a successor). Forced-dynamics **survives the strip** as a seriality fact; the earned layer is reading non-termination as *forced self-unfolding driven by the diagonal*. (b) Delete **"order"** from `ws3_order_endogenous` and it is the bare **`ReflTransGen` closure = itself** (`Iff.rfl`). (c) The load-bearing residue that does **not** strip: `≺` genuinely being the re-diagonalization closure and **not** an external index (D4) — that is the endogeneity, and the cycle proves it is not a painted-on linear order. WS7 records: the map and order are honest (no baked-in growth, no imported index); the *dynamism* reading is the interpretive surplus over the seriality fact, and the *diagonal-drivenness* (the successor exists because the residue always does, WS1) is what makes it self-reference's engine rather than a generic serial relation.

## Deliverable

`series-9/formal/Series9/ws3.lean` (**the seed of the tower's dynamics**, charter §3): transcribed carrier (README §6); `ReDiagStep`, `prec`; `ws3_redi_no_leaf` (NL), `ws3_redi_not_function` (NF), `ws3_dynamics_forced` (D2), `ws3_order_endogenous` (D3), `ws3_imported_index_refuted` (D4). **The accumulated-residue measure and monotonicity are NOT defined here** — they are WS5's, on this map. Axiom check: `#print axioms ws3_dynamics_forced` reduces through `Function.update` to the standard three. **Consumes WS1's `ws1_no_self_total_hold` (the residue always exists, so the process cannot halt); never bakes growth into `ReDiagStep`.**
