# WS2 — The Import Theorem, and its non-circularity

**Design doc. Series 7, the spine. Owns: the four-ingredient impossibility (plain relating ∧ behavioral identity ∧ genuine atomlessness ⇒ ¬plurality), for static and dynamic constructions, and the non-circularity proof that the ingredients are independently motivated and the escapes refuted as theorems rather than excluded by fiat.**

*Series 7 is standalone; names transcribed into `series-7/formal/Series7/ws2.lean`, re-namespaced `Series7.WS2` (see `spec/README.md` §6). The static collapse is **already built** in Series 6 `ws2.lean` (`ws2_static_collapse`, `ws2_escapes_are_imports`); WS2 reframes it as the four-ingredient theorem and sharpens the non-circularity.*

## The object at stake

The charter (§5.1) states the deliverable: ingredients (1) plain relating, (2) behavioral identity, (3) genuine every-moment atomlessness are jointly incompatible with (4) plurality. WS1 gives the engine (atomless ⇒ one behavior); WS2 adds (2) to turn one-behavior into one-thing, states the impossibility in its four-ingredient form, and — the load-bearing half — proves it **non-circular**: that the theorem is a discovery about relating, not a tautology of definitions rigged to exclude the escapes. The whole result lives or dies on the non-circularity, because "atomless plurality is impossible" is worthless if "atomless" was defined to mean "the kind of thing that cannot be plural."

**Ambient theory.** `spec/README.md` §2: the four ingredients as predicates; `BehaviorallyIdentified` (= `NoImportedAtom`, the same predicate); `HereditarilyAtomless`; `Plural`; `ws1_atomless_bisim` (WS1); the transcribed `Static`, `ws2_static_collapse`, `ws2_escapes_are_imports`, `ws1_productive_unique`.

## Candidates (for the theorem's statement)

### C1 — Contrapositive on a plain behaviorally-identified coalgebra (transcribes Series 6)

```lean
theorem ws2_import_theorem_static {X} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X
```
Atomless + behavioral-identity ⇒ at most one object. (Plainness is carried by `dest : X → PkObj κ X` — the unlabelled functor — in the type itself.)

- **Ambient `F`:** `P_κ`; the collapse is `ws1_atomless_bisim` + `hbehav`.
- **Success condition:** `Subsingleton X` — any two are bisimilar (WS1) hence equal (`hbehav`).
- **Failure mode:** none structural (it is `ws2_static_collapse` reframed); the risk is purely that stating it as `Subsingleton` on a single coalgebra does not *look* like the four-ingredient impossibility, hiding the ingredient structure the non-circularity story needs visible.

**Paper triage.** True and transcribed. **Winner for the static half**, but paired with C2 so the four ingredients are explicit.

### C2 — Four-ingredient conjunction impossibility (the headline shape)

```lean
theorem ws2_import_theorem {X} (dest : X → PkObj κ X) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y))
-- plainness is the ambient `dest : X → PkObj κ X`; the three listed are (2),(3),(4)
```
The impossibility as a refuted conjunction: no plain coalgebra is behaviorally-identified, atomless, and plural.

- **Success condition:** the conjunction is refuted — from (2)+(3), `Subsingleton X` (C1), contradicting (4).
- **Failure mode:** none new; equivalent to C1. This is the shape that makes "drop exactly one ingredient" legible.

**Paper triage.** The headline form; `ws2_import_theorem := fun ⟨hb, ha, x, y, hxy⟩ => hxy ((ws2_import_theorem_static dest hb ha).elim x y)`. **Winner (headline).** C1 is its engine.

### C3 — Drop-catalogue form (plurality ⇒ ¬(1∧2∧3))

```lean
theorem ws2_plurality_requires_drop {X} (dest : X → PkObj κ X) (h4 : ∃ x y : X, x ≠ y) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x))     -- must drop (2) or (3) [ (1) is the ambient functor ]
```
Contrapositive read as a price: plurality forces dropping behavioral identity or atomlessness (or, off-type, plainness).

- **Failure mode:** none; it is `ws2_import_theorem` rearranged. Useful for WS4 (each prior series *is* a witnessed drop).

**Paper triage.** Keep as the WS4-facing corollary. **Winner (corollary).**

### C4 — General `Construction` (static ⊔ dynamic) in one statement

```lean
structure Construction where            -- covers coalgebras AND processes
  ...
theorem ws2_import_theorem_general (C : Construction) (h : GenuinelyAtomless C ∧ Plain C ∧ BehavId C) :
    ¬ Plural C
```
One theorem quantifying over both static and dynamic constructions.

- **Failure mode:** **the un-formalizable universal.** A `Construction` general enough to cover coalgebras *and* the process *and* whatever else is exactly the "any construction faithful to relating" quantifier the charter (§5.3) flags as not formalizable.

**Paper triage.** This is the WS6 heuristic ceiling, not a WS2 obligation. **Reject here; WS2 proves the static form (C1/C2) and cites the dynamic instance (`ws1_productive_unique`) as the parallel; WS6 attempts the union.**

## Winning candidates: C2 (headline) built on C1 (engine), C3 (corollary); dynamic case by citation

### The non-circularity — the crux

The theorem is only a discovery if the ingredients are not rigged. Three facts carry it, and the third is the genuinely new WS2 work:

**NC1 — ingredient (2) is the founding principle, not an exclusion.** `BehaviorallyIdentified` (every bisimulation ⊆ equality) is "an object is its relating", point 1 of *every* prior charter, and `NoImportedAtom` is *literally the same predicate* (`spec/README.md` §2). So "no import" is not an ad-hoc side-condition invented to exclude labels; it is the program's own definition of what an object is. *Paper-decidable:* inspect that `NoImportedAtom` and `BehaviorallyIdentified` are the same definition (they are, in Series 6 `ws2.lean`).

**NC2 — ingredient (3) is plain hereditary non-emptiness, independently motivated.** `SHNE` is "relates to something, hereditarily" — the charter-old definition of "no atom", used identically in Series 4 (`ws2_collapse`) and Series 6. It does not mention plurality, labels, or behavior. *Paper-decidable:* inspect `SHNE`'s definition; it is a fixpoint of "successor set nonempty".

**NC3 — the escapes are refuted as theorems (the load-bearing half).** Each prior plurality is shown to *drop a structural ingredient*, by theorem:
```lean
theorem ws2_non_circular (hinf : ℵ₀ ≤ κ) :
    -- νLk's plurality, viewed on the PLAIN functor, is not behavioral: distinct loops,
    -- same bare successor shape — so it drops (2) unless it adds the label to the functor,
    -- dropping (1). Either way a STRUCTURAL ingredient, refuted by ws3_same_succ_diff_face.
    (∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ SameBareSuccessor (loopState q₁) (loopState q₂)
        ∧ loopState q₁ ≠ loopState q₂)
  ∧ -- the tower's plurality is not carrier-atomless: it drops (3) (local foundedness /
    -- unbuilt descent, Series 5 open #2), the index substituting for atomlessness.
    (TowerDropsAtomlessness)
```
The `νLk` half transcribes `ws3_same_succ_diff_face` + `ws3_plurality_core` (distinct loops, identical bare successor) — a *theorem* that the label-distinction is non-behavioral on the plain functor, hence an import. The tower half records that the tower is not carrier-atomless (Series 5's own open #2). *Strategy:* transcribe the Series 4 loop facts and Series 5 tower status; assemble into the two-clause refutation, building on Series 6's `ws2_escapes_are_imports`. *Paper-decidable:* yes — the loop facts are proved; the tower fact is a status transcription.

**The strip test on the theorem.** Delete "atomless" (`SHNE`) from `ws2_import_theorem`: the statement becomes "no plain behaviorally-identified coalgebra is plural", which is *false* (any plain coalgebra with a genuine leaf-difference is plural) — so atomlessness is load-bearing, not rigged. Delete "plain" (allow a `Q`-coordinate): the statement becomes false (νLk is a witness) — so plainness is load-bearing. Both deletions break the theorem *by exhibiting a real counterexample*, which is exactly what non-circularity requires: the ingredients are the hypotheses a genuine theorem needs, not definitional gerrymanders.

### Definitions and obligations

```lean
namespace Series7.WS2
-- ingredients (README §2), ws1_atomless_bisim (WS1), Static/ws2_static_collapse/
-- ws2_escapes_are_imports/ws3_same_succ_diff_face/ws3_plurality_core/Winf — transcribed.

theorem ws2_import_theorem_static {X} (dest) (hbehav) (hatom) : Subsingleton X     -- C1
theorem ws2_import_theorem {X} (dest) : ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x)
    ∧ (∃ x y : X, x ≠ y))                                                          -- C2, headline
theorem ws2_plurality_requires_drop {X} (dest) (h4) :
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x))                           -- C3, WS4-facing
theorem ws2_dynamic_instance (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht                          -- cited parallel
theorem ws2_non_circular (hinf : ℵ₀ ≤ κ) : ... (NC3 above)
```

**D1 — the static theorem.** `ws2_import_theorem_static` + `ws2_import_theorem`. *Strategy:* WS1 gives a bisimulation on any two atomless states; `hbehav` collapses it to equality; `Subsingleton`. *Paper-decidable:* yes (`ws2_static_collapse` reframed).

**D2 — the corollary and the dynamic parallel.** `ws2_plurality_requires_drop`, `ws2_dynamic_instance`. *Strategy:* contrapositive; transcription. *Paper-decidable:* yes.

**D3 — non-circularity.** `ws2_non_circular` + NC1/NC2 (inspection). *Strategy:* transcribe the loop facts and tower status; assemble. *Paper-decidable:* yes. **This is where a SERIOUS review finding would land** — if the loop distinction cannot be shown non-behavioral on the plain functor, the "no import" clause is a fiat and the theorem is `Circular`.

## Outcome classes (per charter §7)

- **Impossibility proved (success):** `ws2_import_theorem` (the four-ingredient impossibility) — the motivating deliverable.
- **Discharged:** the static form, the corollary, the dynamic-instance citation, and `ws2_non_circular` (NC1–NC3).
- **Partial (pre-registered):** the general `Construction` union (C4) deferred to WS6 as the heuristic ceiling; the "static and dynamic are one theorem" question deferred to WS3.
- **Circular (the failure to watch):** if the escapes are only excluded by defining atomlessness/plainness to rule them out — i.e. if `ws2_non_circular` cannot be proved as theorems. The strip test (both deletions exhibit real counterexamples) is the evidence against this; WS7 adjudicates.

## Deliverable

`series-7/formal/Series7/ws2.lean`: transcribed ingredients + `ws2_static_collapse` + the loop/tower import facts; `ws2_import_theorem_static`, `ws2_import_theorem`, `ws2_plurality_requires_drop`, `ws2_dynamic_instance`, `ws2_non_circular`. Axiom check: `#print axioms ws2_import_theorem` on the standard three.
