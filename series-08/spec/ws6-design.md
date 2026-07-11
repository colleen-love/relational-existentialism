# WS6 — The heuristic ceiling

**Design doc. Series 08, the honest boundary. Owns: the universal forms of Consequence 3 (layering-as-narrowing, WS4) and the conservation law (WS5) where they exceed what is rangeable, reported as defended theses floored by the mechanized core — the Series 04/05/07 pattern.**

*Series 08 is standalone; names transcribed into `series-08/formal/Series08/ws6.lean`, re-namespaced `Series08.WS6` (see `spec/README.md` §6). WS6 **consumes WS4 and WS5** (protocol §4): it re-exports their mechanized cores as the *floor* of two theses whose universal quantifiers are not rangeable, and it names precisely what is proved versus what is defended. It introduces no new object; it draws the line.*

## The object at stake

Charter §5.3, §6 (WS6), §9. Two of Series 08's claims have a universal form that quantifies over *every construction* — un-formalizable in the same way Series 07's trichotomy-exhaustiveness and Series 04/05's universals were:

- **Layering-as-narrowing, universal (WS4 C4):** "*all* depth, across *any* construction and *any* notion of deeper, is narrowing." WS4 discharges the per-map form (`afford` antitone along `≺`, `ws4_depth_is_narrowing`) and the foreclosure witness; the all-constructions universal is the ceiling.
- **Conservation, universal (WS5):** the strong "self-limiting universe" claim is already *Refuted* in general (WS5 D2, the kill condition fires); what remains for WS6 is to state honestly that the *weak* bound (mere boundedness) holds universally as a **defended thesis** — every hold is finite (`< κ`, by the carrier), so breadth is always bounded — while conservation (the strong form) is refuted, and to floor the "bounded" thesis on the per-hold finiteness that *is* mechanized.

WS6's discipline: never relabel a defended thesis as a theorem, and never let the refuted strong form (conservation) masquerade as the surviving weak one (boundedness). It reports: **proved core** (per-map narrowing; per-hold finiteness), **refuted strong form** (conservation, from WS5), **defended universal** (all-constructions narrowing; universal mere-boundedness), obstruction precise.

**Ambient theory.** `spec/README.md` §2.2 (`Hold`, `afford`, and the `< κ` bound baked into `PkObj`), §2.4–§2.5 (`prec`, `breadth`, from WS3/WS5); WS4's `ws4_depth_is_narrowing`, WS5's `ws5_kill_condition` / `ws5_conservation_verdict`.

## Candidates

### C1 — The provable core: per-hold finiteness and per-map narrowing (the floor)

```lean
theorem ws6_hold_finite {X} (dest : X → PkObj κ X) (h : Hold dest) : breadth dest h < κ
theorem ws6_provable_core {X} (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    afford dest h' ⊆ afford dest h ∧ breadth dest h < κ
```
Everything the mechanization *does* establish about the bound: every hold affords a `< κ`-bounded breadth (the carrier's own constraint — `PkObj` is κ-bounded), and narrowing is monotone along `≺` (WS4). This is the floor the theses stand on.

- **Success condition:** the terms typecheck — `breadth dest h < κ` is `(dest h.1.2).2` (the `PkObj` cardinality bound), and narrowing is `ws4_depth_is_narrowing`.
- **Failure mode:** none — both are transcribed/consumed facts.

**Paper triage.** Decidable and immediate: finiteness is the `PkObj` subtype proof; narrowing is WS4. **Winner (the floor).**

### C2 — The defended universals, stated as theses (not theorems)

```lean
-- ws6_universal_narrowing (thesis): across ANY construction, deeper ⇒ narrower. Floored by ws4_depth_is_narrowing.
-- ws6_universal_bounded (thesis): across ANY construction, every hold's breadth is bounded. Floored by ws6_hold_finite.
def ws6_universal_narrowing_thesis : Prop := True   -- documentation datum; the Lean content is the floor (C1)
```
The un-rangeable universals, marked as defended theses: WS6 does not claim them as Lean theorems; it names the floor (C1) that supports them and the obstruction (quantifying over all constructions) that keeps them off the machine.

- **Failure mode:** *thesis relabeled as theorem.* The guard: these are `Prop`-level documentation, and the *only* Lean payoff is C1; the design forbids stating them with a real all-constructions quantifier and calling it proved. **Winner (as honestly-flagged theses).**

### C3 — The retraction ledger: conservation refuted, boundedness survives (the sharp line)

```lean
theorem ws6_conservation_retracted (hinf : ℵ₀ ≤ κ) :
    ws5_conservation_verdict = ConservationVerdict.partial      -- strong form refuted (WS5)
  ∧ (∀ {X} (dest : X → PkObj κ X) (h : Hold dest), breadth dest h < κ)   -- weak form (boundedness) survives
```
The one line the whole series' bound-story reduces to: the **strong** conservation law is refuted (WS5's verdict is Partial/Refuted-universal), and what survives is **mere boundedness** (every hold finite). The "self-limiting universe" is retracted; the "bounded but not conserved" world is floored on `PkObj`'s κ-bound.

- **Failure mode:** *the retraction is cosmetic.* Guard: `ws5_conservation_verdict = .partial` is `rfl` on WS5's justified verdict, so the retraction is tied to the actual refutation, not asserted. **Winner (the sharp line WS7 consumes).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | per-hold finiteness + per-map narrowing | `PkObj` bound, `ws4_depth_is_narrowing` | yes | **win (the floor)** |
| C2 | the defended universals as theses | documentation over C1 | yes (as theses, not theorems) | **win (honest theses)** |
| C3 | conservation refuted, boundedness survives | `ws5_conservation_verdict`, `PkObj` bound | yes — `rfl` + subtype proof | **win (the sharp line)** |

## Winning candidates: C1 (floor) + C2 (defended theses) + C3 (retraction ledger)

### Definitions and obligations (cite `spec/README.md` §2; consume WS4, WS5)

```lean
namespace Series08.WS6
-- carrier, PkObj (with its < κ bound) — transcribed (README §6); Hold, afford from WS1;
-- prec from WS3; breadth, ConservationVerdict, ws5_conservation_verdict from WS5;
-- ws4_depth_is_narrowing from WS4.

/-- **D1 — per-hold finiteness (C1).** Every hold affords a `< κ`-bounded breadth: the carrier's own
    constraint. This is the floor of the "bounded" thesis. -/
theorem ws6_hold_finite (dest : X → PkObj κ X) (h : Hold dest) : breadth dest h < κ :=
  (dest h.1.2).2

/-- **D2 — the provable core (C1).** Narrowing is monotone along `≺` and every hold is finite. -/
theorem ws6_provable_core (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    afford dest h' ⊆ afford dest h ∧ breadth dest h < κ :=
  ⟨ws4_depth_is_narrowing dest h h' hp, ws6_hold_finite dest h⟩

/-- **D3 — the retraction ledger (C3).** The STRONG conservation law is refuted (WS5); the WEAK bound
    (mere boundedness) survives on every hold. The "self-limiting universe" is retracted. -/
theorem ws6_conservation_retracted (hinf : ℵ₀ ≤ κ) :
    ws5_conservation_verdict = ConservationVerdict.partial
  ∧ (∀ {X : Type u} (dest : X → PkObj κ X) (h : Hold dest), breadth dest h < κ) :=
  ⟨rfl, fun dest h => ws6_hold_finite dest h⟩

/-- **D4 — the defended universals (C2), NOT theorems.** Documentation of what is defended above the
    floor and why it is off the machine (the all-constructions quantifier). -/
def ws6_universal_theses : Prop := True   -- the Lean payoff is D1–D3; these are the flagged theses.
```

**D1/D2 (floor)** re-export the mechanized core. **D3 (retraction ledger)** is the sharp line: conservation's strong form refuted (tied by `rfl` to WS5's verdict), mere boundedness surviving on `PkObj`'s bound. **D4** names the defended universals as theses, floored on D1–D3, obstruction precise — never relabeled as proved.

## Outcome classes (per charter §7)

- **Discharged:** D1 (per-hold finiteness), D2 (provable core), D3 (retraction ledger).
- **Partial (the honest ceiling, pre-registered):** the universal forms of layering-as-narrowing and mere-boundedness (D4) — defended theses floored by the mechanized core, the all-constructions quantifier the obstruction (charter §5.3, the Series 04/05/07 pattern).
- **Refuted (carried from WS5, reported here):** the strong conservation law — WS6 records the retraction, it does not re-litigate it.
- **Strip test.** Delete **"layering / self-limiting"** from D2/D3 and what remains is the bare **`PkObj` κ-bound + `afford` antitone** — a finiteness-and-reachability fact. The floor **survives the strip** (it is honest finiteness); the *defended universals* are explicitly *not* stripped because they are *not* claimed as theorems — WS6's whole function is to keep that line visible. The retraction (D3) is the anti-laundering payoff: it forbids the refuted strong form from being reported as the surviving weak one.

## Deliverable

`series-08/formal/Series08/ws6.lean`: transcribed carrier (README §6); `ws6_hold_finite` (D1), `ws6_provable_core` (D2), `ws6_conservation_retracted` (D3), `ws6_universal_theses` (D4, documentation). **Consumes WS4's `ws4_depth_is_narrowing` and WS5's `ws5_conservation_verdict`.** Axiom check: `#print axioms ws6_provable_core` reduces through the `PkObj` bound and `ws4_depth_is_narrowing` to the standard three.
