# WS1 — The perspective primitive and the no-god's-eye theorem

**Design doc. Series 8, the blocking spine. Owns: the carrier and the hold primitive `x↾(x,y)` (ambient for all, `spec/README.md` §2.2), and the central negative — the god's-eye node that holds all faces symmetrically is a recoverable-face coalgebra, hence collapses to the One by the engine, hence does not exist as a relationally-identified node.**

*Series 8 is standalone; all names are transcribed into `series-8/formal/Series8/ws1.lean` and re-namespaced `Series8.WS1` (see `spec/README.md` §6). The engine `ws4_recoverable_atomless_collapses` and the free-label witness `ws4_free_label_is_import` are **already built** in Series 7 `ws4.lean`; WS1's job is to re-name them as the god's-eye collapse and to fix the carrier/hold every downstream workstream is written against. This is the workstream the whole series gates on (charter §6, protocol §4): nothing below is sound until the spine lands, because it is what makes a directed hold *free*.*

## The object at stake

The charter's spine (§2, §5.1): **no relationally-identified node has a restriction including all perspectival restrictions.** The mechanism is the Spinozist rebuttal made into a theorem (§5.5, the sharpest risk): a node holding *all* faces *symmetrically* has no asymmetry anywhere, so its directed labels distinguish nothing the plain relating does not — it is a **recoverable** face — and a recoverable, behaviorally-identified, atomless coalgebra is a subsingleton (`ws4_recoverable_atomless_collapses`). The totality does not *contain* the perspectives; it *annihilates* them. The design question is only how to state the god's-eye node so that (a) "holds all faces symmetrically" is *literally* `Recoverable` (not a bespoke exclusion — the Spinozist-retreat guard, protocol §0.5), (b) the collapse discharges to the transcribed engine, and (c) freeness of *distributed* perspective falls out as the contrapositive (routed to WS2).

The load-bearing subtlety, stated once here and never hidden: each face `x↾(x,y)` is *locally* recoverable (it is a function of `dest`, Series 4's `ws1_face_forced`). Freeness is therefore **global**: it is not that any single face escapes the relating, but that no single node recovers *all* faces at once — because the node that would is the god's-eye node, and the god's-eye node collapses. The spine is exactly the proof of this global freeness. WS1 states this; WS2 witnesses the surviving directed hold; WS7 audits that freeness is this global fact and not a defined-in local one.

**Ambient theory.** `spec/README.md` §2.1 (carrier: `PkObj`, `SReaches`, `SHNE`, `IsBisim`, `BehaviorallyIdentified`, `hneRel_isBisim`, `ws1_atomless_bisim`), §2.2 (hold: `Hold`, `afford`), §2.3 (the labelled face: `LkObj`, `plainOf`, `IsBisimL`, `BehaviorallyIdentifiedL`, `Recoverable`, `ws4_recoverable_atomless_collapses`, `ws4_free_label_is_import`, `labelLoop`, `facedLoop`). All transcribed from Series 7.

## Candidates

### C1 — God's-eye = recoverable face; collapse via the engine (the lead)

```lean
theorem ws1_no_gods_eye {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X :=
  ws4_recoverable_atomless_collapses dest hrec hbehav hatom
```
"Holding all faces symmetrically" = the direction-label is recoverable; an atomless, behaviorally-identified such carrier is a subsingleton — the god's-eye node has at most one state, so it cannot be the many-faced totality it was posited as.

- **Ambient `F`:** the labelled functor `LkObj κ Q X`; the hold is the `Q`-direction; symmetry = `Recoverable`.
- **Success condition:** the term typechecks — it is `ws4_recoverable_atomless_collapses` re-named. The god's-eye node collapses **by the engine**, not by exclusion.
- **Failure mode:** *recoverable-hence-not-free / Spinozist retreat smuggled.* The only risk is that `Recoverable` fails to capture "symmetric/all-faces" — that would make the collapse a proof about the wrong object. Discharged by C2 (the symmetric witness `facedLoop` is provably `Recoverable`) and by the honest note that *each* face is recoverable, so "all faces symmetrically" is recoverability at full strength, not a rigged special case.

**Paper triage.** Decidable-on-paper and already proved: `ws4_recoverable_atomless_collapses` exists verbatim in Series 7 `ws4.lean`; the reframing is "recoverable label = symmetric hold = god's-eye node." **Winner.**

### C2 — The symmetric witness: `facedLoop` is the god's-eye node in miniature

```lean
theorem ws1_symmetric_hold_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (facedLoop hinf)
theorem ws1_gods_eye_collapses_witness (hinf : ℵ₀ ≤ κ)
    (hbehav : BehaviorallyIdentifiedL (facedLoop hinf)) : Subsingleton (ULift.{u} Bool)  -- FALSE hyp, see below
```
`facedLoop` carries the *same constant* label on both states — a face that is a function of the relating, not of identity: the god's-eye/symmetric hold seen on collapse-equal states, where it cannot tell them apart. It is provably `Recoverable` (`ws4_facedLoop_recoverable`).

- **Failure mode:** *the witness is too degenerate.* `facedLoop`'s two states are plain-bisimilar and behaviorally-identified-**L** would force them equal, but they are posited distinct — so `facedLoop` is *not* itself `BehaviorallyIdentifiedL`-and-plural; it is the witness that a symmetric label **cannot** carry plurality (the collapse bites). That is the point: the god's-eye node cannot be plural, which is the spine. Stated as `ws1_symmetric_hold_recoverable` (recoverability of the symmetric face) plus its consequence via C1.

**Paper triage.** `ws4_facedLoop_recoverable` is built. It is the concrete anchor showing C1's hypothesis `Recoverable` is *satisfied* by the paradigm symmetric hold, so C1 is not vacuous. **Winner (the witness that grounds C1).**

### C3 — Bisimilar-to-the-trivial-loop form (the charter's literal phrasing)

```lean
theorem ws1_gods_eye_bisim_trivial {X : Type u} (dest : X → PkObj κ X) (x : X)
    (hx : SHNE dest x) (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim dest R ∧ R x x   -- and, cross-carrier, related to the self-loop by hneRel
```
The charter says the all-faces node "is bisimilar to the trivial self-loop." Its plain reduct, being atomless, is `hneRel`-related to any atomless state including the self-loop `twoLoop` — `ws1_atomless_bisim`. So "no asymmetry anywhere ⇒ bisimilar to the positionless One" is literal.

- **Failure mode:** *cross-carrier bisimulation is not a single relation.* `dest` and `twoLoop` live on different carriers; "bisimilar" across them needs a coproduct coalgebra. Rather than build the coproduct, state it as: on the *disjoint union* `X ⊕ ULift Bool` with the merged `dest`, the symmetric node and the self-loop are both `SHNE`, hence `hneRel`-bisimilar (`ws1_atomless_bisim`). Constructible but heavier than C1.

**Paper triage.** Faithful to the charter's wording and a genuine theorem, but it does no *collapse* work C1 does not already do (bisimilarity to the One is what `ws4_recoverable_atomless_collapses` uses internally). **Retain as the interpretive gloss** ("all-faces node = the positionless One") and, if cheap on the coproduct, as a secondary payoff; the *load-bearing* spine is C1's subsingleton.

### C4 — Direct impossibility statement (no god's-eye node exists)

```lean
theorem ws1_no_gods_eye_node {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) :
    ¬ (∃ x y : X, x ≠ y)   -- a god's-eye node cannot host the plurality of faces it must contain
```
The Impossibility phrased as "no distinct faces survive at the totality" — the direct negation, matching charter §7's "Impossibility proved" outcome.

- **Failure mode:** none beyond C1 (it is `Subsingleton.elim` on C1). **Winner (the headline phrasing of C1).**

### C5 — The hold is forced (Series 4 transcription, carrier hygiene)

```lean
theorem ws1_hold_forced {X : Type u} (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z }
```
`afford` is a function of `dest` alone — no annotation, no imported data (Series 4's `ws1_face_forced`). This is the hygiene lemma that makes "holding-first, reaching-derived" (charter §3) honest: the hold refines the plain carrier, it does not add a coordinate.

**Paper triage.** A one-line `⟨afford, fun _ => rfl, …⟩`, transcribed. It is *why* each face is locally recoverable (and hence why freeness must be global). **Winner (the primitive-hygiene payoff).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | god's-eye (recoverable) ⇒ subsingleton | `ws4_recoverable_atomless_collapses` | yes — transcribed engine | **win (spine)** |
| C2 | the symmetric hold is `Recoverable` | `ws4_facedLoop_recoverable` | yes — built witness | **win (grounds C1)** |
| C3 | all-faces node bisimilar to the self-loop | coproduct + `ws1_atomless_bisim` | yes; coproduct build-owed | gloss / secondary |
| C4 | no distinct faces at the totality | `Subsingleton.elim ∘ C1` | yes | **win (headline)** |
| C5 | the hold is forced by `dest` | `ws1_face_forced` (S4) | yes — one line | **win (hygiene)** |

## Winning candidates: C1+C4 (the spine), grounded by C2, hygiened by C5; C3 as gloss

### Definitions and obligations

```lean
namespace Series8.WS1
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, BehaviorallyIdentified, hneRel, hneRel_isBisim,
-- ws1_atomless_bisim, twoLoop, LkObj, plainOf, IsBisimL, BehaviorallyIdentifiedL, Recoverable,
-- labelLoop, facedLoop, ws4_recoverable_atomless_collapses, ws4_facedLoop_recoverable,
-- ws4_free_label_is_import, ws4_labelLoop_not_recoverable — all transcribed (README §6).

def Hold (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }

/-- **D5 — the hold is forced (C5).** `afford` is the unique function of `dest`; holding refines
    the carrier, it does not annotate it. (Series 4 `ws1_face_forced`, transcribed.) -/
theorem ws1_hold_forced (dest : X → PkObj κ X) :
    ∃! f : Hold dest → Set X, ∀ h, f h = { z | SReaches dest h.1.2 z } :=
  ⟨afford dest, fun _ => rfl, fun g hg => funext fun h => hg h⟩

/-- **D2 — the symmetric hold is recoverable (C2).** The paradigm god's-eye face (a constant,
    identity-independent label) adds no constraint the relating does not: `Recoverable`. -/
theorem ws1_symmetric_hold_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (facedLoop hinf) :=
  ws4_facedLoop_recoverable hinf

/-- **D1 — the no-god's-eye collapse (C1, the spine).** A node holding all faces symmetrically is a
    recoverable-face coalgebra; atomless and behaviorally identified, it is a subsingleton — the
    totality annihilates its faces. This IS `ws4_recoverable_atomless_collapses`, re-read: symmetric
    hold = recoverable label = god's-eye node. -/
theorem ws1_no_gods_eye {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X :=
  ws4_recoverable_atomless_collapses dest hrec hbehav hatom

/-- **D4 — the Impossibility, headline phrasing (C4).** No relationally-identified god's-eye node
    hosts a plurality of faces. -/
theorem ws1_no_gods_eye_node {Q X : Type u} (dest : X → LkObj κ Q X)
    (hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
    (hatom : ∀ x, SHNE (plainOf dest) x) : ¬ (∃ x y : X, x ≠ y) := by
  haveI := ws1_no_gods_eye dest hrec hbehav hatom
  rintro ⟨x, y, hxy⟩; exact hxy (Subsingleton.elim x y)

/-- **D3 — freeness is global, routed to WS2.** The DIRECTED hold (a free label) is NOT recoverable
    (`ws4_labelLoop_not_recoverable`), so it survives the merge; and no single node recovers all such
    holds, because that node would satisfy D1's hypotheses and collapse. Freeness = no-totality. -/
theorem ws1_directed_hold_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf
```

**D1 — the spine.** `ws1_no_gods_eye`. *Strategy:* the transcribed engine; symmetry ⇒ `Recoverable`. *Paper-decidable:* yes. *Non-circularity (protocol §0.5):* the god's-eye node is *collapsed by the engine* (`ws4_recoverable_atomless_collapses` → `ws2_import_theorem_static`), not excluded by a definitional clause. C2 proves the paradigm symmetric hold actually *satisfies* `Recoverable`, so the hypothesis is inhabited, not vacuous.

**D3 — global freeness.** The directed hold is not recoverable (built), and the totality that would recover every hold at once is precisely a `ws1_no_gods_eye` node — non-existent. This is the ambient fact WS2 consumes; WS1 states it, WS2 turns it into plurality.

## Outcome classes (per charter §7)

- **Impossibility proved (the spine):** D1 (`ws1_no_gods_eye`) and D4 (`ws1_no_gods_eye_node`) — the sharp negative, a first-class success (charter §8.1). Near-certain: both transcribe a built engine.
- **Discharged:** D2 (symmetric hold recoverable), D5 (hold forced), D3 (directed hold not recoverable) — all transcribe built Series 7 lemmas.
- **Partial / gloss (routed to WS7):** C3, the literal "bisimilar to the trivial self-loop," if the coproduct carrier is not built; the subsingleton collapse (D1) carries the load either way.
- **Failed (pre-registered honest alternative, charter §8.1):** if `Recoverable` were found *not* to model "all faces symmetrically" — i.e. a genuinely symmetric all-faces node that is *not* recoverable and does *not* collapse — the god's-eye node would be constructible and **monism wins**, reported as Failed, routed to WS7 → `monismStands`. Not expected: each face is a function of `dest` (D5), so "all faces" is recoverability at full strength.
- **Strip test.** Delete **"face"** from `ws1_no_gods_eye` and the statement is the bare **`ws4_recoverable_atomless_collapses`**: *a recoverable-label, atomless, behaviorally-identified coalgebra is a subsingleton.* The theorem **survives the strip** as a recoverable-collapse fact — so the *mathematical* content is Series 7's engine, and "god's-eye node / all faces symmetrically" is the earned **interpretive** layer, flagged here honestly. What the strip does **not** remove is the load-bearing hypothesis `Recoverable`: delete atomlessness (`SHNE`) and the collapse fails (`labelLoop` is atomless, free, and plural), so *symmetry/recoverability is doing the work*, not a rigged "atomless." This is the WS7 input: the spine is a genuine theorem whose novelty is interpretive, not a new bisimulation.

## Deliverable

`series-8/formal/Series8/ws1.lean`: transcribed carrier + labelled/face machinery (README §6); `Hold`, `afford`; `ws1_hold_forced` (D5), `ws1_symmetric_hold_recoverable` (D2), `ws1_no_gods_eye` (D1), `ws1_no_gods_eye_node` (D4), `ws1_directed_hold_free` (D3). Axiom check: `#print axioms ws1_no_gods_eye` reduces through `ws4_recoverable_atomless_collapses` / `ws2_import_theorem_static` to the standard `propext` / `Classical.choice` / `Quot.sound` (axiom-clean in Series 7). **This file is built first (charter §6): it fixes the carrier and the hold for WS2–WS6.**

---

## REVIEW-RESPONSE NOTE (2026-07-11, series-review-1 S1 → series-review-2 S1 — SERIOUS, now closed at charter strength)

**Pass 1 (`series-review-1.md` S1)** found `ws1_no_gods_eye` collapses only *under the hypothesis*
`Recoverable`, witnessed only by the one-face `facedLoop`. The Phase-E-pass-1 response added a
`Recoverable`-based "fork" (`ws1_no_recoverable_plurality`, `ws1_gods_eye_dichotomy`, …).

**Pass 2 (`series-review-2.md` S1) correctly rejected that response** as a tautological case-split
(`Subsingleton X ∨ ¬ Recoverable dest` is `by_cases`), whose free horn *asserted* "distributed, not
monist" in a docstring rather than proving it — silently renaming the charter's pre-registered Failed
antecedent. Those two theorems were **removed**.

**Now closed at charter strength (§2, §5.1, §5.5) — the literal spine, no `Recoverable` hypothesis:**

- **`ws1_gods_eye_collapses`** *(THE SPINE)* — the god's-eye node is the **positionless** node,
  `Symmetric dest := ∀ x y, dest x = dest y` ("no asymmetry anywhere," the view from everywhere is the
  view from nowhere). On it the all-true relation is a label-bisimulation
  (**`ws1_symmetric_bisim_trivial`** — the charter's literal "bisimilar to the trivial self-loop," a
  theorem, no coproduct carrier needed), so behavioral identity collapses it to a subsingleton. The
  collapse is **by the engine**, unconditional (no `Recoverable`, no atomlessness).
- **`ws1_symLoop_not_behav`** — a concrete ≥2-face symmetric node (`symLoop`, labels `⟨true⟩`/`⟨false⟩`)
  cannot host relationally-identified plurality: its states are label-bisimilar, so behav-id forces
  them equal. The collapse bites on a genuine multi-face totality, not just one-face `facedLoop`.
- **`ws1_labelLoop_not_symmetric`** — the surviving plural node is provably NOT symmetric
  (`dest ⟨true⟩ ≠ dest ⟨false⟩`). So the charter's **Failed condition — a *symmetric* node that does
  not collapse — provably does not arise**: symmetric ⟹ collapse (spine lands); the plural survivor is
  asymmetric = distributed perspective (WS2), and this is now a *theorem* about the witness, not a
  docstring assertion. `ws1_freeness_needs_two_positions` further shows freeness is irreducibly a
  between-two-positions phenomenon, never a lone free totality.

The headline is now genuinely earned: *no relationally-identified positionless (all-faces-symmetric)
node exists — it collapses to the One by the engine; genuine plurality is asymmetric/distributed.*
All axiom-clean (`axiom-check-log.md`). C3 (coproduct carrier) is subsumed: `ws1_symmetric_bisim_trivial`
gives the bisimilarity to the trivial loop directly on the identity carrier.

---

## REVIEW-RESPONSE NOTE (2026-07-11, series-review-3 S1 — SERIOUS, resolved as an honest PARTIAL)

Pass 3 (independent adversarial) correctly found that the pass-2 `Symmetric := ∀ x y, dest x = dest y`
spine is "positionless by a definitional clause" — the bisimilarity holds by rewriting the defining
equality, and the genuine multi-face symmetric witness (`symLoop`) is *excluded* (not behav-id), not
*collapsed*. This is the §0.5 "asserted positionless / excluded by a definitional clause" pattern.

**Attempted the charter-strength theorem first (per protocol §E); it provably resists.** The precise
obstruction, now itself a theorem:

- **`ws1_symmetric_states_bisimilar`** — on a positionless coalgebra ANY two states are label-bisimilar.
  So `ws1_gods_eye_collapses` is *behavioral identity applied to that bisimulation*: the **coincidence
  rule fails at the spine** (the "forced collapse" unfolds to relational identity on a symmetric
  coalgebra). This is now OWNED in-code, not hidden.
- **`ws1_distinct_faces_atomless_not_recoverable`** — a genuine face-plurality on an atomless field is
  FREE, never recoverable. So a rich *symmetric/recoverable* totality is an EMPTY class on atomless:
  there is nothing to collapse independently, because genuine plurality of faces forces freeness
  (asymmetry). The reviewer's requested "collapse a genuine all-faces node" asks to collapse an object
  that provably does not exist as relationally-identified.

**Honest outcome: the spine is a PARTIAL.** Impossibility-proved core (no recoverable/symmetric god's-eye
node; genuine plurality ⟹ free/distributed, WS2 + `ws1_freeness_needs_two_positions`); the
charter-strength *independent* derivation (a rich totality collapsing as a fact over and above
relational identity) resists — it reduces to the Series 7 relational-identity collapse. The overclaim
"Impossibility proved at charter strength" is withdrawn from `Series8.lean` and `charter-status.md`.

This is WITHIN the charter's pre-registration: §5.5 names the Spinozist rebuttal as "the sharpest
risk," and §9 lists "whether the all-faces node is *provably* bisimilar to the trivial loop, or only
heuristically" as an open problem. So no charter change; the honest Partial is the terminal state, and
the question "is no-god's-eye separable from relational identity?" is the natural seed for Series 9.
Monism does not win: the plurality is real and distributed. All theorems axiom-clean (`axiom-check-log.md`).
