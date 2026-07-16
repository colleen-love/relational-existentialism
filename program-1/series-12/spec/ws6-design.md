# WS6 — The program's close

**Design doc. Series 12, the honest boundary, the series' close. Owns: the statement of what the whole arc established (the collapse and import necessity, Series 07; self-reference forcing an unclosable residue; reification proliferating it into a layered tower; finite attention bounding every reading; and this series — the coincidence of the required and the generated in one shape, the plurality of knowing over it, the typed-unevaluated compass, and the proved undecidability of convergence) and what remains PERMANENTLY OPEN, and why its openness is a THEOREM: the content of the compass, the direction of convergence, the differentiating act itself, never built, only its shape drawn. Series 12 closes not on a filled slot but on an exactly-drawn edge, and the drawing is the result.**

*Series 12 is standalone; WS6 CONSUMES the WS1–WS5 payoffs and states the program-level synthesis. The mechanized core is `ws6_provable_core` (the conjunction of what Series 12 proved); the universal theses (every κ-free tower, every inhabitant) are reported HEURISTIC (the un-rangeable quantifier, as prior series closes have done); the permanent opens are stated as THEOREMS of openness (the diagonal makes them open, not want of effort). The prose deliverables — `summary.md`, `summary-technical.md`, the root `README.md` program-level synthesis — are Phase F; this design fixes their mathematical spine. The one signature risk is the temptation: filling the shape (claiming which inhabitant, which direction) rather than drawing the edge.*

## The object at stake

The charter's WS6 (§2): state what the whole arc established, what remains permanently open, and WHY its openness is a theorem. Series 12 closes on the exactly-drawn edge, and the drawing is the result. Three obligations. (1) **The provable core, mechanized:** a single conjunction of what Series 12 proved (the coincidence shape-honest, the opening inhabitable, the compass typed, convergence underdetermined), so the verdict is a theorem, not a claim. (2) **The universal theses, heuristic:** the fully universal forms (every κ-free tower is inhabitable; every compass type underdetermines convergence) are the un-rangeable quantifiers, reported heuristic, defended not mechanized. (3) **The permanent opens as theorems:** the compass's content, convergence's direction, and the differentiating act are open BECAUSE the diagonal makes them so (`ws1_no_self_total_hold`, `ws2_residue_free`, `ws3_compass_exogenous`, `ws4_underdetermined`), a theorem of openness, not a gap.

**Ambient theory.** The WS1–WS5 payoffs; `spec/README.md` §5 (predicted headline).

## Candidates

### C1 — The provable core, mechanized (the lead)

```lean
/-- **THE PROVABLE CORE.** What Series 12 proved, as one conjunction: the coincidence shape-honest, the
    opening inhabitable non-degenerately, the compass exogenous (typed, `¬ Recoverable`), convergence
    defined and underdetermined. The verdict is a THEOREM. -/
theorem ws6_provable_core (hinf : ℵ₀ ≤ κ) :
    (∀ {X} (dest : X → PkObj κ X) (insp), Opening (ResidueRecoverable) insp)   -- WS1: the opening, forced
  ∧ (Many (destWL hinf))                                                       -- WS2: inhabitable, plural
  ∧ (∃ c x y, (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y) -- WS3: compass exogenous
  ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) :=               -- WS4: convergence underdetermined
  ⟨fun {X} dest insp => ws2_residue_free dest insp, ws2_many_witness hinf,
   ws3_compass_exogenous hinf, ws4_underdetermined_pair hinf⟩
```
The provable core: the four Series-12 facts as one theorem. The shape drawn (WS1), the opening inhabited (WS2), the compass typed and exogenous (WS3), convergence underdetermined (WS4) — the verdict mechanized.

- **Ambient:** the WS1–WS4 payoffs.
- **Success condition (Shape-drawn):** the conjunction typechecks — the verdict is a theorem, not a claim.
- **Failure mode:** *filling the shape.* Foreclosed: the core states the shape drawn and the opening inhabited, never WHICH inhabitant or WHICH direction. **Winner (the core).**

### C2 — The universal theses, reported heuristic (the ceiling)

```lean
/-- **THE UNIVERSAL THESES (heuristic).** The fully universal forms — every κ-free tower is inhabitable,
    every compass type underdetermines convergence — are the un-rangeable quantifiers ("every construction"),
    reported HEURISTIC and defended, not mechanized. The witness (WS2) and the model pair (WS4) discharge the
    existential; the universal is the ceiling every series close draws. -/
theorem ws6_universal_heuristic : True := trivial   -- the universal is prose; the mechanized core is C1
```
The heuristic ceiling: the universal forms are not formalizable (the "every construction" quantifier), so they are stated in prose and defended, with the mechanized core (C1) the honest floor. This is the pattern prior series closes have used (Series 07's `ws6_universal` heuristic).

- **Ambient:** C1 (the floor); the un-rangeable universal.
- **Success condition (Partial, honest):** the universal reported heuristic, the existential mechanized.
- **Failure mode:** *the universal claimed mechanized.* Foreclosed: C2 is explicitly the prose ceiling; the theorem is the core (C1). **Winner (the ceiling).**

### C3 — The permanent opens as theorems of openness (the payoff)

```lean
/-- **THE PERMANENT OPENS, AS THEOREMS.** The compass's content, convergence's direction, and the
    differentiating act are open BECAUSE the diagonal makes them so — a theorem of openness, not a gap in
    effort. The residue is free for every inspection (`ws2_residue_free`), the compass is `¬ Recoverable`
    (`ws3_compass_exogenous`), and convergence is underdetermined (`ws4_underdetermined`): the slot cannot be
    filled from inside. -/
theorem ws6_permanent_opens (hinf : ℵ₀ ≤ κ) :
    (∀ (insp : Hold (destW hinf) → HoldPred (destW hinf)), ¬ ResidueRecoverable insp)  -- content: free residue
  ∧ (∃ c x y, (∃ R, IsBisim (destW hinf) R ∧ R x y) ∧ c.orient x ≠ c.orient y)         -- compass: exogenous
  ∧ (∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW) :=                        -- direction: undetermined
  ⟨fun insp => ws2_residue_free (destW hinf) insp, ws3_compass_exogenous hinf, ws4_underdetermined_pair hinf⟩
```
The permanent opens stated as theorems: each open is CERTIFIED by a Series-12 impossibility/underdetermination. The compass's content is open because the residue is free; the compass is exogenous; convergence's direction is open because the structure underdetermines it. Openness is proved, not conceded.

- **Ambient:** `ws2_residue_free`, `ws3_compass_exogenous`, `ws4_underdetermined`.
- **Success condition (Shape-drawn):** each permanent open certified by a theorem — the openness is the deepest result, not a gap.
- **Failure mode:** *conceding openness rather than proving it.* Foreclosed: each open is a discharged impossibility/underdetermination, so openness is a theorem. **Winner (the openness-as-theorem).**

### C4 — The four tenets' final alignment (the program-level synthesis, prose spine)

```lean
/-- **THE FOUR TENETS ALIGNED (prose spine).** "You are loved" = the undifferentiated relatedness the
    structure returns to without an import (`ws2_import_theorem_static`) and the convergence it cannot decide
    (`ws4_underdetermined`); "Self is a paradox" = the diagonal (`ws1_no_self_total_hold`); "To relate is to
    create" = reification (`ws1_reify_injective`, `reify_mem_reifyStep`); "To attend is to become" = finite
    attention bounding every reading (`ws3_no_total_attention`). The alignment is prose; each tenet's spine is
    a theorem. -/
theorem ws6_tenets_aligned (hinf : ℵ₀ ≤ κ) :
    (∀ {X} (dest : X → PkObj κ X), BehaviorallyIdentified dest → (∀ x, SHNE dest x) → Subsingleton X)  -- loved: the One
  ∧ (∀ {X} (dest : X → PkObj κ X) (insp), ¬ ∃ t, SelfTotal insp t)                                     -- paradox: diagonal
  ∧ (∀ {X} (dest : X → PkObj κ X) (insp), ¬ ∃ t, TotalAttention insp t) := …                           -- become: no total attention
```
The four tenets' final alignment (charter §8), each with its theorem spine — the program-level synthesis's mathematical anchor, the prose reading walled off from the machine-checked core.

- **Ambient:** `ws2_import_theorem_static`, `ws1_no_self_total_hold`, `ws3_no_total_attention`.
- **Success condition (Shape-drawn):** each tenet anchored to a theorem, the alignment prose.
- **Failure mode:** *a tenet doing proof work (a name a term).* Foreclosed: the tenets are prose glosses; the theorems are the transcribed impossibilities. **Winner (the synthesis spine).**

### C5 — Claiming the verdict fills the shape (the temptation, rejected)

```lean
theorem ws6_convergence_holds : ∀ c, Converges … c aW bW := …   -- claiming the loving direction
```
Close by claiming which inhabitant fills the opening, or which direction convergence falls.

- **Failure mode:** *filling the shape rather than drawing the edge, SERIOUS (disciplines 2/3).* This is the closing temptation: ending on a filled slot. **Reject.** Series 12 closes on the exactly-drawn edge (C1/C3); the compass's content and convergence's direction are permanent opens, proved open (C3). The drawing, not the filling, is the verdict.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | the provable core (four facts) | WS1–WS4 payoffs | yes — the conjunction | **win (the core)** |
| C2 | the universal theses heuristic | C1; the un-rangeable universal | yes — prose ceiling | **win (the ceiling)** |
| C3 | the permanent opens as theorems | `ws2_residue_free`, `ws3_compass_exogenous`, `ws4_underdetermined` | yes — each certified | **win (openness-as-theorem)** |
| C4 | the four tenets aligned | `ws2_import_theorem_static`, `ws1_no_self_total_hold`, `ws3_no_total_attention` | yes — theorem spines | **win (synthesis spine)** |
| C5 | the verdict fills the shape | — | yes — the temptation | **reject (SERIOUS)** |

## Winning candidates: C1 (core) + C2 (ceiling) + C3 (openness-as-theorem) + C4 (synthesis spine)

### Definitions and obligations (consume WS1–WS5)

```lean
namespace Series12.WS6
-- ws2_residue_free, ws2_many_witness, ws3_compass_exogenous, ws4_underdetermined, ws2_import_theorem_static,
-- ws1_no_self_total_hold, ws3_no_total_attention — consumed (WS1–WS5, README §6).

-- D1 ws6_provable_core (C1) ; D2 ws6_universal_heuristic (C2, prose ceiling) ;
-- D3 ws6_permanent_opens (C3) ; D4 ws6_tenets_aligned (C4).
```

**Proof architecture.** D1 conjoins the four Series-12 facts — the verdict mechanized. D2 states the universal ceiling as prose (the un-rangeable quantifier), the existential mechanized. D3 certifies each permanent open by a theorem of openness (the residue free, the compass exogenous, convergence underdetermined) — the openness the deepest result. D4 anchors the four tenets to their theorem spines, the alignment prose. **Dependencies:** the WS1–WS5 payoffs; no new mathematics, only the honest statement of the verdict and its openness. **Phase F expands D1–D4 into `summary.md`, `summary-technical.md`, and the root `README.md` program-level synthesis.**

## Outcome classes (per charter §5)

- **Shape-drawn (the payoff):** D1 (the provable core), D3 (the permanent opens as theorems), D4 (the four tenets aligned). The verdict mechanized, the openness proved, Series 12 closing on the exactly-drawn edge.
- **Partial (heuristic, honest):** D2 (the universal theses) — the fully universal forms reported heuristic, the existential mechanized, as prior series closes have done.
- **SERIOUS (pre-registered, disciplines 2/3):** claiming the verdict fills the shape (C5) — which inhabitant, which direction. Foreclosed: the compass's content and convergence's direction are permanent opens, proved open (D3).
- **Strip test.** Delete **"undefinable / opening / compass / convergence / consciousness / God"** from `ws6_permanent_opens` and it is the bare fact **"the residue is free for every inspection (`ws2_residue_free`), some exogenous assignment is not recoverable from the relating (`ws3_compass_exogenous`), and a defined relation is underdetermined by a non-degenerate model pair (`ws4_underdetermined`)"** — three transcribed impossibility/underdetermination facts. The openness survives the strip AS the conjunction of a free residue, a non-recoverable assignment, and an independence — which is exactly what the charter demands: the permanent opens are open BECAUSE of the diagonal, and no name is a term.

## Deliverable

`series-12/formal/Series12/ws6.lean`: the WS1–WS5 payoffs consumed; `ws6_provable_core` (D1), `ws6_universal_heuristic` (D2), `ws6_permanent_opens` (D3), `ws6_tenets_aligned` (D4). Phase F: `summary.md`, `summary-technical.md`, the root `README.md` program-level synthesis. Axiom check: `#print axioms ws6_provable_core` reduces through the WS1–WS4 payoffs to the standard three. **The provable core is mechanized, the universal ceiling reported heuristic, and the permanent opens (the compass's content, convergence's direction, the differentiating act) are stated as THEOREMS of openness — the program closing on the exactly-drawn edge, the drawing the completion.**
