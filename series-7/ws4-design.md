# WS4 — The imports catalogued: the program explained

**Design doc. Series 7, the interpretive spine (the capstone unification). Owns: exhibiting weights (Series 3), labels/faces (Series 4), and levels (Series 5) each as the specific ingredient-1 drop its series relied on, and showing that the Import Theorem (WS2) *predicts* each — the recurring honest negative of every prior series was this theorem, unproved.**

*Series 7 is standalone; all import-witnesses are transcribed into `series-7/formal/Series7/ws4.lean`, re-namespaced `Series7.WS4` (see `spec/README.md` §6 — the label `νLk`/`loopState`/`ws3_plurality_core`/`ws3_same_succ_diff_face` from Series 4, the tower `Winf` from Series 5, the weight algebra from Series 3's archive). This workstream is **interpretive-heavy, light on new Lean**: the Lean is almost entirely transcription of already-proved import-witnesses; the work is the unification that reads them as one phenomenon. Cite README §6, never redefine.*

## The object at stake

The charter's payback (§5.4, §6 WS4): weights, labels, levels, and Series 6's failed time are not four different achievements but four responses to one theorem. WS2 proved that plain ∧ behavioral-identity ∧ atomless ⇒ ¬plural; WS4 must show that each prior series, having *chosen* plurality, was thereby forced to drop exactly one structural ingredient, and that the drop it made is *visible in its formalism as a theorem* — not an interpretive gloss laid over it after the fact. This is where Series 7 pays the whole program back: the "the import could not be removed" that every prior series reported as its own honest negative was `ws2_import_theorem` all along, felt before it was proved. The design question is only how to cash out "series S imported ingredient (i)" so that (a) it is grounded in a transcribed *theorem* of S, not a reading, (b) the tower's genuine drop-ambiguity ((1) vs (3)) is handled honestly rather than forced, and (c) the four cases assemble into one predictive statement `ws4_program_explained` without over-claiming a formalizable universal (that is WS6's ceiling, not WS4's).

**Ambient theory.** `spec/README.md` §2 (the four ingredients as predicates; `BehaviorallyIdentified` = `NoImportedAtom`; `HereditarilyAtomless`; `Plural`) and the transcribed import-witnesses: Series 4's `νLk` (functor `P_κ(Q × X)`, *not* plain `P_κ`), `loopState : Q → (νLk).X`, `ws3_plurality_core` (distinct loops are hereditarily non-empty and distinct), `ws3_same_succ_diff_face` (distinct loops have identical bare successor shape — distinguished only by `q ∈ Q`); Series 5's `Tower`/`Winf` (the indexed family, locally founded); Series 3's weight algebra (archived, transcribed only if a clean Lean witness exists — see Outcome). The engine `ws2_import_theorem` / `ws2_plurality_requires_drop` (WS2) is consumed as the predictor.

## Candidates (for cashing out "X is an import")

### C1 — Each import as a witnessed drop of a NAMED ingredient (the lead)

```lean
-- S4: the label. Distinct plural loops, identical bare successor — difference factors through Q ↪ νLk.
theorem ws4_labels_are_import (hinf : ℵ₀ ≤ κ) :
    ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ loopState q₁ ≠ loopState q₂
      ∧ SameBareSuccessor (loopState q₁) (loopState q₂)      -- ws3_same_succ_diff_face
-- reads: plural on νLk (P_κ(Q×X)) ⇒ the distinction is non-behavioral on the PLAIN functor,
--        so it is carried by q ∈ Q — a dropped (1) [the functor is not plain].
```
Each series' import is a *theorem of that series* that the plurality is distinguished only by a coordinate the plain relating does not carry. For S4 this is `ws3_same_succ_diff_face` (identical bare successor) plus `ws3_plurality_core` (distinct, hereditarily non-empty): the loops differ, but strip the face and their `P_κ` shape coincides, so the difference factors through `Q ↪ νLk` — a dropped (1).

- **Success condition:** for each series, a transcribed theorem exhibits the plurality *and* the collapse of its bare-`P_κ` shape, so the distinguisher is provably the imported coordinate.
- **Failure mode (the thing to watch):** a prior plurality that is **not** an import — a series whose distinct atomless objects differ in their bare `P_κ` shape — would break `ws2_import_theorem`'s exhaustiveness, since it would be plain-behavioral-atomless-plural. This is the exact counterexample WS2's collapse forbids; WS4 must confirm each catalogued case does *not* differ in bare shape, or the Import Theorem is false. For S4 this is precisely what `ws3_same_succ_diff_face` guarantees.

**Paper triage.** Decidable-on-paper and, for S4/S5, already proved: `ws3_same_succ_diff_face` and `ws3_plurality_core` exist verbatim in Series 4 `ws3.lean`; `Winf`'s local-foundedness is Series 5's own open #2. Each `ws4_*_are_import` threads these into the ingredient-drop reading. **Winner.**

### C2 — "Import" as an abstract predicate over constructions

```lean
def IsImport (C : Construction) : Prop := ...          -- some uniform "carries an extra-relational coordinate"
theorem ws4_all_prior_import : ∀ S ∈ priorSeries, IsImport S
```
Define a single predicate `IsImport` ranging over all constructions and prove every prior series satisfies it.

- **Failure mode:** **over-general / un-formalizable.** A predicate uniform enough to range over weights *and* labels *and* an ordinal index *and* whatever else is exactly the "any construction faithful to relating" quantifier the charter (§5.3) flags as the WS6 heuristic ceiling. Quantifying over "prior series" as objects is not a formalizable domain.

**Paper triage.** This is WS6's universal, not WS4's obligation. **Reject as the statement; retain "each import is the same phenomenon" as the unification prose that `ws4_program_explained` records case-by-case, not by a uniform predicate.**

### C3 — The tower ambiguity handled as an explicit disjunction (honest)

```lean
-- S5: the index. The tower is EITHER not one plain coalgebra (indexed family ⇒ drops (1))
--      OR not carrier-atomless (locally founded, descent unbuilt ⇒ drops (3)). They coincide.
theorem ws4_levels_are_import (hinf : ℵ₀ ≤ κ) :
    TowerDropsPlainness Winf ∨ TowerDropsAtomlessness Winf
```
State the S5 case as a genuine disjunction: the tower `Winf` drops (1) (read as an indexed family, not one plain coalgebra) *or* drops (3) (read as not carrier-atomless — locally founded, carrier-descent unbuilt, Series 5's own open #2). **They coincide because the index is exactly what substitutes for carrier atomlessness**: the level-index *is* the missing descent, so "indexed, not plain" and "not atomless" name the same fact from two sides.

- **Success condition:** the disjunction is proved (either disjunct suffices), and the coincidence is stated as the honest content — not a hedge but the observation that for the tower the (1)-drop and the (3)-drop are the same drop.
- **Failure mode:** forcing a single disjunct (claiming the tower *only* drops (1), or *only* (3)) would be dishonest and, worse, brittle — a reviewer picking the other reading would appear to refute it. The disjunction is the load-bearing honesty.

**Paper triage.** Decidable-on-paper: `Winf`'s indexed structure and its local foundedness are both transcribable facts of Series 5. **Winner for the S5 case**, paired with C1's frame for S3/S4. This is the tower drop-ambiguity the charter demands be flagged, carried openly to WS7.

### C4 — Purely-interpretive catalogue, no Lean

```lean
-- (no Lean; a prose table asserting each series imported)
```
Assert the catalogue entirely in prose, citing the series without transcribing their witnesses.

- **Failure mode:** **circular / non-refutable.** Without the loop witnesses (`ws3_same_succ_diff_face`: distinct loops, identical bare successor) and the index witness (`Winf` locally founded), "S imported" is an assertion, not a refutation — and the charter's non-circularity rule (§7) requires each escape be refuted *as a theorem*, never by fiat. A prose-only catalogue is exactly the rigged reading WS7 would flag `Circular`.

**Paper triage.** **Reject:** the whole non-circularity of Series 7 turns on the imports being refuted by the transcribed loop/index witnesses, not narrated. WS4 must carry the Lean, however thin.

## Paper-decidable triage

| Cand. | Statement | Lean cost | Decidable-on-paper? | Verdict |
|---|---|---|---|---|
| C1 | each import a witnessed named-ingredient drop | transcription (S3/S4/S5 witnesses) | yes — S4/S5 proved upstream | **Winner (S3, S4)** |
| C2 | uniform `IsImport` predicate | heavy / un-formalizable | no — the WS6 universal | reject (→ WS6) |
| C3 | tower drop as explicit `(1)∨(3)` disjunction | transcription (Series 5) | yes | **Winner (S5)** |
| C4 | prose-only catalogue | none | no — non-refutable, rigged | reject (→ Circular risk) |

## Winning candidates: C1 (S3/S4, witnessed named drops) + C3 (S5, honest disjunction)

### Definitions and obligations

```lean
namespace Series7.WS4
-- νLk, loopState, ws3_plurality_core, ws3_same_succ_diff_face (Series 4 ws3);
-- Tower, Winf (Series 5 ws1); weight algebra (Series 3, archived) — all transcribed (README §6).
-- ws2_import_theorem, ws2_plurality_requires_drop (WS2) — consumed as the predictor.

/-- **S3 — weights.** A weight hung on each relation is a coordinate the plain functor does not
    carry: the S3 world is `P_κ(W × X)`, not plain `P_κ`. Drops (1), plainly. -/
theorem ws4_weights_are_import : WeightsAreExtraRelationalCoordinate

/-- **S4 — labels/faces.** Distinct plural loops, hereditarily non-empty, with IDENTICAL bare
    successor shape — distinguished only by `q ∈ Q`, so the difference factors through `Q ↪ νLk`.
    Drops (1): the functor is `P_κ(Q × X)`. -/
theorem ws4_labels_are_import (hinf : ℵ₀ ≤ κ) :
    ∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ loopState q₁ ≠ loopState q₂
      ∧ SameBareSuccessor (loopState q₁) (loopState q₂)

/-- **S5 — levels.** The tower drops (1) [indexed family, not one plain coalgebra] OR (3) [not
    carrier-atomless, locally founded, descent unbuilt = S5 open #2]. They coincide: the index is
    exactly what substitutes for carrier atomlessness. -/
theorem ws4_levels_are_import (hinf : ℵ₀ ≤ κ) :
    TowerDropsPlainness Winf ∨ TowerDropsAtomlessness Winf

/-- **The capstone.** For each prior plural series, `ws2_plurality_requires_drop` PREDICTS the drop
    the series is separately witnessed (above) to have made. The theorem explains the program: the
    recurring "the import could not be removed" WAS this theorem, unproved. S6 is the confirmation —
    it kept (1)(2)(3), refused to drop, and collapsed (`ws1_productive_unique`). -/
theorem ws4_program_explained (hinf : ℵ₀ ≤ κ) :
    (WeightsAreExtraRelationalCoordinate)                                   -- S3 drops (1)
  ∧ (∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ SameBareSuccessor (loopState q₁) (loopState q₂)) -- S4 drops (1)
  ∧ (TowerDropsPlainness Winf ∨ TowerDropsAtomlessness Winf)                -- S5 drops (1) or (3)
  ∧ (∀ t : Proc κ, Productive t → t = omegaProc hinf)                       -- S6 refused, collapsed
```

**D1 — weights (S3).** `ws4_weights_are_import`. *Strategy:* the S3 world's functor carries a weight algebra `W` alongside the relation (`P_κ(W × X)`), so the coordinate is not carried by plain relating — a dropped (1). *Paper-decidable:* the reading is; the *Lean witness* depends on the S3 archive having a clean statement (flagged Partial below).

**D2 — labels (S4).** `ws4_labels_are_import`. *Strategy:* transcribe `ws3_plurality_core` (distinct, hereditarily non-empty loops) + `ws3_same_succ_diff_face` (identical bare successor); the difference thus factors through `Q ↪ νLk`, a dropped (1). *Paper-decidable:* yes — both are proved Series 4 lemmas.

**D3 — levels (S5).** `ws4_levels_are_import`. *Strategy:* transcribe `Winf`'s indexed structure (drops (1)) and its local foundedness / unbuilt descent (drops (3)); prove the disjunction (either disjunct suffices), state the coincidence — the index *is* the missing atomlessness. *Paper-decidable:* yes, both disjuncts are Series 5 status facts.

**D4 — the unification.** `ws4_program_explained`. *Strategy:* conjoin D1–D3 with the transcribed S6 collapse (`ws1_productive_unique`), the whole read against `ws2_plurality_requires_drop`: every plural series is witnessed to have dropped a structural ingredient, and the one series (S6) that *refused* the drop lost plurality instead. The interpretive payoff is not a new proof but the assembly: the four cases are one theorem's four shadows. *Paper-decidable:* yes as a conjunction of transcribed facts; the *predictive* reading (that WS2 forces each drop) is the interpretive claim WS4 defends, not a formalizable universal (→ WS6).

## Outcome classes (per charter §7)

- **Discharged (transcribed):** D2 (labels — `ws3_plurality_core` + `ws3_same_succ_diff_face`) and D3 (levels — the `Winf` disjunction). Both thread proved upstream witnesses; near-certain.
- **Partial (flagged honestly):** D1 (weights) — the *reading* is clean (S3's functor is `P_κ(W×X)`), but the Series 3 archive may lack a clean Lean witness of the form the label/index cases enjoy. If so, D1 is reported Partial: the drop is argued from the archived functor signature, not a transcribed theorem, and the residual obstruction (no S3 Lean witness) is stated, not laundered.
- **Impossibility / confirmation:** S6 is *not* an import and is not a discharge of the same shape — it is the **confirmation**: it kept (1)(2)(3), refused to import, and collapsed (`ws1_productive_unique`). The drop it refused to make is why it failed; that is the negative that seals the catalogue.
- **The interpretive payoff:** `ws4_program_explained` — the theorem predicts each forced drop. This is the capstone, and it is honestly interpretive: a conjunction of transcribed facts read against `ws2_plurality_requires_drop`, defended as the program's explanation, not claimed as a formalizable "every construction" (that ceiling is WS6).
- **Strip test:** delete "import" from the catalogue and each `ws4_*_are_import` still asserts a *structural* fact (the functor carries `W`/`Q`; the tower is indexed/locally-founded) refutable by a bare-shape counterexample — so "import" is a name for a witnessed drop, not a rigged label. The failure mode to watch (a prior plurality that is not an import, differing in bare `P_κ` shape) would break `ws2_import_theorem`'s exhaustiveness; each catalogued case is confirmed to *not* so differ.

## Deliverable

`series-7/formal/Series7/ws4.lean`: transcribed import-witnesses (`νLk`, `loopState`, `ws3_plurality_core`, `ws3_same_succ_diff_face`, `Winf`, and the S3 weight functor if archived); `ws4_weights_are_import` (D1, Partial if no clean S3 witness), `ws4_labels_are_import` (D2), `ws4_levels_are_import` (D3, the honest disjunction), `ws4_program_explained` (D4, the unification). Axiom check: `#print axioms ws4_labels_are_import` on the standard three (it is `ws3_same_succ_diff_face`, already axiom-clean in Series 4); `ws4_program_explained` reduces to its transcribed conjuncts.

---

*Design doc for WS4. The Lean is thin transcription; the work is the unification — reading weights, labels, and levels as one theorem's forced drops, with S6's collapse as the confirming negative. The tower's drop-ambiguity ((1) vs (3), coinciding because the index substitutes for atomlessness) is carried openly to WS7. No em dashes in final academic paper copy; this working design doc is not final copy.*
