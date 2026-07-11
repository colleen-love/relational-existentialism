# WS1 — The hold-reflexive carrier and the diagonal spine

**Design doc. Series 09, the blocking spine. Owns: the hold-reflexive carrier `(dest, insp)` (ambient for all, `spec/README.md` §2.3), and the central negative — a hold rich enough to range over the space of holds cannot contain its own complete content, because the self-total hold is the fixed point a Cantor/Lawvere diagonal denies, so it does not exist, and its non-existence is a THEOREM INDEPENDENT of relational identity, not the Series 08 coincidence re-described.**

*Series 09 is standalone; the carrier beneath the reflexivity (`PkObj`, `SReaches`, `SHNE`, `IsBisim`, `BehaviorallyIdentified`, `ws1_atomless_bisim`, `ws2_import_theorem_static`, `Hold`, `afford`) and the Series 08 coincidence witness (`ws1_symmetric_states_bisimilar`) are transcribed into `series-09/formal/Series09/ws1.lean`, re-namespaced `Series09.WS1` (see `spec/README.md` §6). Unlike Series 08's WS1 (a reframing of built Series 07 machinery), this is **genuinely new Lean**: `HoldPred`, `insp`, `diag`, `SelfTotal`, and `ws1_no_self_total_hold` are Series 09 content. This is the workstream the whole series gates on (charter §6, protocol §4): nothing below is sound until the spine lands AND is certified diagonal-not-bisimulation, because that is what makes the residue *free* and what repairs Series 08's coincidence.*

## The object at stake

The charter's spine (§2, §5.1): **on a hold-reflexive carrier, no hold contains its own complete content.** The mechanism is diagonalization made into a theorem (§4.1, the sharpest discipline): a hold rich enough that its content is a predicate over the whole space of holds, asked to contain *its own complete content*, would have to decide its own self-membership, and the completed judgment `insp t t ↔ ¬ insp t t` is a contradiction. The totality does not merely fail to be symmetric (Series 08); it **cannot be formed**. The design question is threefold and each part is a separate obligation: (a) state the self-total hold as a genuine **fixed-point equation** (`SelfTotal insp t := insp t = diag insp`) so its refutation is Cantor/Lawvere-shaped, (b) prove the refutation with a proof term that references **only `insp`** and propositional logic — no `IsBisim`, no `BehaviorallyIdentified` — so it is independent of relational identity, and (c) fix the carrier so the diagonal genuinely *runs*: hold-reflexive (strictly stronger than a self-loop, §4.4) and κ-bounded (consistent, not Russell, §5.5).

The load-bearing subtlety, stated once here and never hidden: the theorem `¬ ∃ t, SelfTotal insp t` is true for **every** `insp`, including the degenerate self-loop inspection. What separates the genuine spine from a vacuous assertion is the *carrier*: on a hold-reflexive carrier the self-total equation is *expressible-and-almost-satisfiable* (a rich `insp` realises every content except the diagonal — the diagonal is the sole genuine gap), so its refutation is a real Cantor gap; on a self-loop carrier the content is a point and the refutation degenerates. WS1 states this and proves the carrier is hold-reflexive, not merely self-looping. The spine is the diagonal; the carrier is what makes it bite.

**Ambient theory.** `spec/README.md` §2.1 (carrier: `PkObj`, `SReaches`, `SHNE`, `IsBisim`, `BehaviorallyIdentified`, `ws1_atomless_bisim`, `ws2_import_theorem_static`), §2.2 (hold: `Hold`, `afford`, `ws1_hold_forced`), §2.3 (the reflexive layer: `HoldPred`, `insp`, `diag`, `SelfTotal`). The Series 08 coincidence witness `ws1_symmetric_states_bisimilar` is transcribed as the negative touchstone (§4.1). All from `spec/README.md` §6.

## Candidates

### C1 — The self-total fixed-point equation has no solution (the lead, charter-faithful)

```lean
def SelfTotal (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop :=
  ∀ h, insp t h ↔ diag insp h                         -- insp t = diag insp; "content includes its own complete content"
theorem ws1_no_self_total_hold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t := by
  rintro ⟨t, ht⟩
  have h := ht t                                        -- insp t t ↔ ¬ insp t t
  simp only [diag] at h; tauto
```
The self-total hold is a hold whose content is the completed self-inspection `diag insp` — the judgment about every hold's self-holding, the "complete content" the hold would have to contain to hold itself totally. Instantiating the defining equation at `t` itself gives `insp t t ↔ ¬ insp t t`, a contradiction. So no hold is self-total.

- **Ambient:** the reflexive layer `(dest, insp)`; the diagonal `diag insp := fun h => ¬ insp h h`; the self-total equation.
- **Success condition (Discharged, the repair):** the term typechecks and its proof is the diagonal instantiation `ht t`, referencing only `insp`. No-self-total-hold is an Impossibility proved, INDEPENDENT of relational identity by construction (§4.1).
- **Failure mode:** *coincidence-with-relational-identity.* The one fatal risk: if the only non-vacuous statement of `SelfTotal` had to route through a bisimulation (e.g. self-total = behaviorally identical to a totality), the proof would re-hit `ws1_symmetric_states_bisimilar` and the spine would be **Coincident**. Discharged by C4/C5: the proof term is `tauto` on `insp t t ↔ ¬ insp t t`, containing no bisimulation lemma, and the independence is witnessed both syntactically (WS7 unfolds the term) and semantically (the spine holds where relational identity is false and where it is true).

**Paper triage.** Decidable on paper and the charter's literal phrasing (§4.1, "the totality's DEFINING FIXED-POINT EQUATION"): a Cantor/Lawvere diagonal, `p ↔ ¬p` at the diagonal point. **Winner (the spine).**

### C2 — The inspection is not surjective onto contents (the Cantor form)

```lean
theorem ws1_insp_not_surjective {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (diag insp)                  -- insp t = diag insp
  have := congrFun ht t; simp only [diag] at this; tauto
```
"A hold ranges over the space of holds" at full strength would be an inspection surjective onto `HoldPred` — every content realised by some hold, in particular the complete content. Cantor: no such surjection exists, the missed content is `diag insp`.

- **Ambient:** `Function.Surjective`; the diagonal as the un-hit content.
- **Success condition:** the term typechecks (the Cantor/Lawvere theorem, `Function.cantor_surjective`-shaped). Equivalent to C1: `SelfTotal insp t ↔ insp t = diag insp`, so `(∃ t, SelfTotal insp t) ↔ diag insp ∈ range insp`.
- **Failure mode:** *Russell-too-strong.* Reading surjectivity as a *demand on the carrier* (a carrier where a hold ranges over ALL contents) would be an inconsistent object with no model — exactly the Russell hazard (§5.5). C2 is stated as a *refutation* (`¬ Surjective`), not a carrier axiom: the diagonal is precisely why the unrestricted carrier has no model, so κ-boundedness of `dest` is what keeps the *consistent* carrier consistent while the surjection is denied.

**Paper triage.** Decidable and the cleanest Mathlib-analogue (`Function.cantor_surjective`). Equivalent to C1; the surjection form makes the "genuine gap in a consistent object" reading crisp. **Winner (the Cantor form, equivalent to C1).**

### C3 — The Lawvere form: a self-total hold would give `Not` a fixed point (the general diagonal)

```lean
theorem ws1_lawvere_form {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) (hsurj : Function.Surjective insp) :
    ∀ g : Prop → Prop, ∃ p, g p = p := by
  intro g
  obtain ⟨t, ht⟩ := hsurj (fun h => g (insp h h))
  exact ⟨insp t t, by have := congrFun ht t; simpa using this.symm⟩
-- Cantor is the instance g := Not, which has NO fixed point (¬(p ↔ ¬p)) — hence ¬ Surjective (C2).
```
The categorical account of diagonal arguments (Lawvere): a point-surjective `insp` forces every endomap of `Prop` to have a fixed point; `Not` has none, so `insp` is not surjective. This exhibits the spine as an *instance* of the general fixed-point theorem, connecting Series 09 to Cantor/Gödel/Lawvere (charter §10).

- **Failure mode:** *the connection is decorative, not load-bearing.* Lawvere's theorem is the *reason* the diagonal is general (any `g` without a fixed point refutes surjectivity), but the spine only needs `g = Not`. Kept as the interpretive/positioning payoff and the proof that C1/C2 are not ad hoc; the load-bearing spine is C1/C2.

**Paper triage.** Decidable; genuine but subsumes to C2 at `g = Not`. **Retain as the general-diagonal gloss (charter §10), C1/C2 carry the load.**

### C4 — The diagonal is not a bisimulation (the coincidence check as a theorem, §4.1)

```lean
theorem ws1_diagonal_not_bisim {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    -- the spine holds with NO atomlessness, NO behavioral-identity, NO bisimulation hypothesis:
    (¬ ∃ t, SelfTotal insp t)
    -- and it holds on carriers where relational identity FAILS (states not all bisimilar) …
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d),
       ¬ ∃ t, SelfTotal ins t)
    -- … so no-self-total-hold is orthogonal to `BehaviorallyIdentified` and to `ws1_symmetric_states_bisimilar`.
:= ⟨ws1_no_self_total_hold dest insp, fun d ins => ws1_no_self_total_hold _ ins⟩
```
The theorem that discharges the series' cardinal risk: the spine's hypotheses contain **no** bisimulation and **no** atomlessness — it is a fact about `insp` alone, so it cannot be `ws1_symmetric_states_bisimilar` in disguise (which needs `Symmetric dest` and produces a bisimulation `R`). Where Series 08's collapse *was* behavioral identity applied to a symmetric bisimulation, Series 09's spine is a fixed-point contradiction with the bisimulation vocabulary absent from the statement and the proof.

- **Failure mode:** *residual routing through bisimulation.* If, unfolded, `ws1_no_self_total_hold` secretly invoked `IsBisim`/`ws1_symmetric_states_bisimilar`, the check fails and the spine is Coincident. It does not: the proof is `tauto` on a propositional biconditional. WS7's `ws7_coincidence_check` `#print`s the term and confirms the absence.

**Paper triage.** Decidable: the *statement* of `ws1_no_self_total_hold` has no bisimulation hypothesis, and the proof has no bisimulation lemma — inspectable directly. **Winner (the coincidence check, the reason the series exists).**

### C5 — Hold-reflexive, not self-loop: the genuine-gap witness (§4.4 guard)

```lean
/-- A self-loop inspection: content is a POINT (the singleton `{h}`), not a predicate over holds. -/
def inspLoop {X} (dest : X → PkObj κ X) : Hold dest → HoldPred dest := fun h => (fun h' => h' = h)
/-- A RICH (hold-reflexive) inspection: realises every content except the diagonal — the sole gap. -/
theorem ws1_holdreflexive_not_selfloop {X : Type u} (dest : X → PkObj κ X) :
    -- there is an inspection whose range is EVERY content but the diagonal (the diagonal is the one genuine gap) …
    (∃ insp : Hold dest → HoldPred dest, ∀ c, c ≠ diag insp → ∃ h, insp h = c)
    -- … witnessing that the carrier is genuinely hold-reflexive: the self-total hold is expressible-and-
    -- refutable, the diagonal RUN not asserted. The self-loop `inspLoop` has content a point (degenerate).
```
The guard against §4.4 (self-loop too weak). A self-loop carrier's content is a point (`inspLoop`), on which "no self-total hold" degenerates to "a point is not everything." A hold-reflexive carrier admits a *rich* inspection whose only un-realised content is the diagonal — so the diagonal is a genuine Cantor gap in an otherwise-complete inspection, not a vacuous miss. This is what makes the spine *run* rather than be *asserted*.

- **Failure mode:** *the rich inspection is not constructible, or is itself degenerate.* On a carrier with enough holds (an atomless `SHNE` field has `κ`-many), a near-surjective inspection is constructible (index contents by holds via any injection `HoldPred ↪ ...` restricted to the realisable κ-bounded contents). If it were *not* — if every inspection on the carrier had content a point — the carrier would be a self-loop and the spine `monismStands` (charter §4.4). WS1 must exhibit the witness; the design pre-registers it as the carrier-strength obligation.

**Paper triage.** Decidable in principle; the witness is the delicate part (constructing a near-surjective inspection on a κ-bounded hold space). Retain as the **carrier-strength obligation**; if only a *separating* (not near-surjective) inspection is constructible, the spine is Discharged-on-a-witness and the universal is WS6's ceiling (§5.3). **Winner (the §4.4 guard), possibly partial on the witness.**

### C6 — The Russell horn refuted: the unrestricted carrier has no model (§5.5 guard)

```lean
theorem ws1_unrestricted_carrier_inconsistent {X : Type u} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp :=
  fun ⟨insp, hs⟩ => ws1_insp_not_surjective dest insp hs
```
The opposite carrier hazard (§5.5): a carrier where a hold ranges over *all* holds unrestrictedly (a surjective `insp`) is Russell-paradoxical. C6 is that paradox, owned as a theorem: no surjective inspection exists, so the unrestricted carrier has no model. The κ-bounded `(dest, insp)` carrier (§2.3) sidesteps it — `insp` is a total map, never demanded surjective, and `dest` is κ-bounded — so the diagonal is a gap *inside a consistent object*.

- **Failure mode:** none beyond C2 (it is `ws1_insp_not_surjective` re-read as "the too-strong carrier is inconsistent"). **Winner (the §5.5 guard).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | self-total equation has no solution | `SelfTotal`, `diag`, `tauto` | yes — diagonal `p ↔ ¬p` | **win (spine)** |
| C2 | `insp` not surjective onto contents | `Function.cantor_surjective`-shape | yes | **win (Cantor form ≡ C1)** |
| C3 | Lawvere: surjection ⇒ `Not` has a fixed point | Lawvere fixed-point | yes; subsumes to C2 | gloss (charter §10) |
| C4 | the spine is diagonal-not-bisimulation | statement has no `IsBisim` | yes — inspectable | **win (coincidence check)** |
| C5 | carrier hold-reflexive, not self-loop (genuine gap) | near-surjective `insp` witness | partial (witness delicate) | **win (§4.4 guard), maybe on-witness** |
| C6 | unrestricted (surjective-`insp`) carrier inconsistent | `ws1_insp_not_surjective` | yes | **win (§5.5 guard)** |

## Winning candidates: C1+C2 (the spine, two equivalent forms), C4 (coincidence check), C6 (Russell guard); C5 the carrier-strength obligation, C3 the general-diagonal gloss

### Definitions and obligations

```lean
namespace Series09.WS1
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, BehaviorallyIdentified, ws1_atomless_bisim,
-- ws2_import_theorem_static, twoLoop, LkObj, plainOf, Recoverable, labelLoop, facedLoop,
-- ws4_free_label_is_import, ws4_recoverable_not_import, Symmetric, ws1_symmetric_states_bisimilar,
-- Hold, afford, ws1_hold_forced — all transcribed (README §6).

/-- The hold-reflexive layer (README §2.3). A content is a predicate over the space of holds. -/
def HoldPred {X} (dest : X → PkObj κ X) : Type u := Hold dest → Prop
def diag {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) : HoldPred dest :=
  fun h => ¬ insp h h
def SelfTotal {X} {dest : X → PkObj κ X} (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop :=
  ∀ h, insp t h ↔ diag insp h

/-- **D0 — the hold is forced (carrier hygiene).** `afford` is the unique function of `dest`; the
    reflexive layer refines the carrier, it does not annotate it. (Series 04 `ws1_face_forced`.) -/
theorem ws1_hold_forced {X} (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z } :=
  ⟨afford dest, fun _ => rfl, fun _g hg => funext fun h => hg h⟩

/-- **D1 — THE SPINE (C1, Impossibility proved, independent of relational identity).** No hold contains
    its own complete content: the self-total fixed-point equation `insp t = diag insp` has no solution,
    by the diagonal instantiation `insp t t ↔ ¬ insp t t`. The proof references ONLY `insp`. -/
theorem ws1_no_self_total_hold {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ ∃ t, SelfTotal insp t := by
  rintro ⟨t, ht⟩
  have h := ht t
  simp only [diag] at h
  exact (h.mp · |>.elim) (h.mpr (fun hp => (h.mp hp) hp)) |>.elim  -- insp t t ↔ ¬ insp t t ⊢ False

/-- **D2 — the Cantor form (C2, equivalent to D1).** No inspection surjects onto the space of contents;
    the missed content is `diag insp`. `(∃ t, SelfTotal insp t) ↔ diag insp ∈ Set.range insp`. -/
theorem ws1_insp_not_surjective {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) : ¬ Function.Surjective insp := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (diag insp)
  exact ws1_no_self_total_hold dest insp ⟨t, fun h => by rw [ht]⟩

/-- **D3 — the coincidence check (C4, the cardinal payoff).** The spine holds with NO bisimulation and
    NO atomlessness hypothesis, so it is not `ws1_symmetric_states_bisimilar` in disguise. Orthogonality
    to relational identity, witnessed: the spine holds on ANY carrier, including ones where states are
    all label-bisimilar (relational identity trivial) AND ones where they are not. -/
theorem ws1_diagonal_not_bisim {X : Type u} (dest : X → PkObj κ X)
    (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, SelfTotal insp t)
  ∧ (∀ {Y : Type u} (d : Y → PkObj κ Y) (ins : Hold d → HoldPred d), ¬ ∃ t, SelfTotal ins t) :=
  ⟨ws1_no_self_total_hold dest insp, fun d ins => ws1_no_self_total_hold _ ins⟩

/-- **D4 — the Russell guard (C6).** A carrier where a hold ranges over ALL contents (surjective `insp`)
    is inconsistent: no model. The κ-bounded `(dest, insp)` carrier never demands surjectivity, so the
    diagonal is a gap inside a consistent object. -/
theorem ws1_unrestricted_carrier_inconsistent {X : Type u} (dest : X → PkObj κ X) :
    ¬ ∃ insp : Hold dest → HoldPred dest, Function.Surjective insp :=
  fun ⟨insp, hs⟩ => ws1_insp_not_surjective dest insp hs

/-- **D5 — hold-reflexive, not self-loop (C5, §4.4 carrier-strength obligation).** The carrier admits a
    RICH inspection whose sole un-realised content is the diagonal — the diagonal is a genuine gap, not a
    vacuous miss; the self-total hold is expressible-and-refutable, run not asserted. (If only a
    *separating* inspection is constructible, the spine is Discharged-on-a-witness; universal → WS6.) -/
theorem ws1_holdreflexive_not_selfloop {X : Type u} (dest : X → PkObj κ X) (hne : Nonempty (Hold dest)) :
    ∃ insp : Hold dest → HoldPred dest,
      (∀ c : HoldPred dest, c ≠ diag insp → ∃ h, insp h = c) ∨ (Function.Injective insp) := …
```

**D1 — the spine.** *Strategy:* the diagonal instantiation `ht t`, giving `insp t t ↔ ¬ insp t t`. *Paper-decidable:* yes. *Non-circularity (§4.1):* the proof term is propositional on `insp`; it invokes no `IsBisim`, no `ws1_symmetric_states_bisimilar`. D3 certifies this as a theorem; WS7 `#print`s the term.

**D3 — the coincidence check.** This is the payoff the whole series turns on. The spine's *statement* carries no bisimulation hypothesis (contrast `ws1_symmetric_states_bisimilar`, which needs `Symmetric dest` and *produces* a bisimulation), and its *proof* carries no bisimulation lemma. So no-self-total-hold is the separable second fact Series 08's series-review-3 named as the open question: independent of relational identity by construction.

**D5 — the carrier-strength obligation.** The honest hazard on scope (charter §5.3): the genuine-gap inspection may be constructible only for a specific carrier, leaving the universal "every hold-reflexive carrier admits the diagonal" as WS6's ceiling.

**BUILD CORRECTION (2026-07-11, recorded in `charter-status.md` Phase C, per protocol §C).** The pre-build D5 first horn — an inspection "near-surjective onto every content except the diagonal" — is **UNREALIZABLE by cardinality**: the complement of a single point in `HoldPred dest = Hold dest → Prop` still has cardinality `2^|Hold| > |Hold|`, so no map from `Hold` covers it (you cannot surject `Hold` onto `HoldPred` minus one point any more than onto all of `HoldPred`). Hold-reflexivity is **not** near-surjectivity. The corrected, faithful guard (built as `ws1_holdreflexive_not_selfloop`): the carrier expresses a genuine **non-point** content — an inspection whose content `⊤` holds two distinct holds `h₀ ≠ h₁` at once, which a self-loop cannot, since every `inspLoop` content is a point (`inspLoop h h' ↔ h' = h`). This is what "a hold ranges over the space of holds" means (content is a predicate over holds, not a successor point), and it makes the carrier strictly stronger than a self-loop — the §4.4 guard, stated correctly. Independence of the spine does not depend on the gap-inspection at all (the diagonal `ws1_no_self_total_hold` holds for every `insp`); D5 is the carrier-strength witness that the diagonal is *run*, not asserted on a degenerate self-loop. No downstream workstream depended on the near-surjective horn.

```lean
theorem ws1_holdreflexive_not_selfloop {X : Type u} (dest : X → PkObj κ X)
    (h₀ h₁ : Hold dest) (_hne : h₀ ≠ h₁) :
    (∃ insp : Hold dest → HoldPred dest, insp h₀ h₀ ∧ insp h₀ h₁)      -- a genuine non-point content
  ∧ (∀ (h h' : Hold dest), inspLoop (dest := dest) h h' ↔ h' = h)      -- every self-loop content is a point
```

## Outcome classes (per charter §7)

- **Impossibility proved, INDEPENDENT of relational identity (the spine, the repair of Series 08):** D1 (`ws1_no_self_total_hold`) and D2 (`ws1_insp_not_surjective`), certified diagonal-not-bisimulation by D3. This is the first-class success the whole series exists for (charter §8.1). Near-certain as a *theorem*; the independence is the load-bearing claim D3 secures.
- **Discharged:** D0 (hold forced), D4 (Russell guard). Transcribed / immediate.
- **Coincident (the pre-registered gravest alternative, charter §5.5):** if D3 fails — if the only non-vacuous `SelfTotal` routed through a bisimulation and the proof unfolded to `ws1_symmetric_states_bisimilar` — the spine is **Coincident**, Series 08's wall re-hit at greater depth, reported honestly (not buried), routed to WS7 → `coincident`. Not expected: the proof is `tauto` on `p ↔ ¬p`, and D3 states the orthogonality as a theorem. *This is the specific negative Series 09 exists to test.*
- **monismStands (the pre-registered honest failure):** if D5 fails — if the carrier admits only self-loop inspections (content a point), the diagonal is asserted not run and the spine reduces to Series 08's coincidence (charter §4.4); or if a self-total hold were somehow constructible (impossible by D1, unless the carrier is inconsistent — guarded by κ-bound). Routed to WS7 → `monismStands`. Not expected: D5 exhibits a hold-reflexive inspection.
- **Partial (pre-registered, charter §5.3):** the *universal* "every hold-reflexive carrier admits the near-surjective gap-inspection" is the un-rangeable quantifier; D5 may deliver only a witness, with the universal a defended thesis (WS6). This still repairs Series 08, since ONE non-coincident diagonal suffices (charter §8, closing paragraph).
- **Strip test.** Delete **"self-total"** from `ws1_no_self_total_hold` and the statement is the bare **`¬ ∃ t, ∀ h, insp t h ↔ ¬ insp h h`** — a pure Cantor/Lawvere fixed-point fact (no `t` with `P t = fun h => ¬ P h h`). The theorem **survives the strip** as a fixed-point fact — and this is exactly what the charter demands (§4.1: the diagonal SHOULD be Cantor-shaped, a fixed-point contradiction). So the *mathematical* content is the bare diagonal, and "self-total hold / a hold containing its own complete content / the-me-I-cannot-reach" is the earned **interpretive** layer, flagged here honestly. Crucially — and this is the difference from Series 08 — what the strip leaves is a **fixed-point contradiction, NOT a bisimulation**: delete "self-total" and you get Cantor, not `ws1_symmetric_states_bisimilar`. That is the whole repair. WS7 records: the spine is a genuine diagonal theorem whose novelty is interpretive, and whose *independence from relational identity* is the earned, load-bearing surplus D3 certifies.

## Deliverable

`series-09/formal/Series09/ws1.lean`: transcribed carrier + hold + coincidence witness (README §6); `HoldPred`, `diag`, `SelfTotal`; `ws1_hold_forced` (D0), `ws1_no_self_total_hold` (D1), `ws1_insp_not_surjective` (D2), `ws1_diagonal_not_bisim` (D3), `ws1_unrestricted_carrier_inconsistent` (D4), `ws1_holdreflexive_not_selfloop` (D5). Axiom check: `#print axioms ws1_no_self_total_hold` reduces to `propext` alone (or the standard three); crucially **the proof term contains no `IsBisim`/`BehaviorallyIdentified`/`ws1_symmetric_states_bisimilar`** — the single most important build check (protocol §C). **This file is built first (charter §6): it fixes the hold-reflexive carrier and the reflexive layer for WS2–WS6.**
