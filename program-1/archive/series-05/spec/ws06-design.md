# WS6 — Relating across levels, and attention as grade-shift

**Design doc. Series 05, the deepest technical workstream. Owns: the depth-graded face; cross-level edges as graded composite faces; leak-free transport of `ws3_faces_never_annihilate` to the graded setting; non-terminating descent; the identification of relating-to with being-composed-of; the inherited + new incompleteness; attention as grade-shift; and the graded weak distributive law (the bialgebra obligation).**

*Standalone. Depends on WS1 (`Tower`, `Winf`, `destInf`, connecting maps), WS2 (`ℤ` index, no-first-level), WS4 (`ws4_no_completing_view`, which has a forward dependency back on this file's cross-level face — see WS4 pre-registration). Transcribes the Series 04 composition `ws3_faces_never_annihilate` / `lcomp` / `NonAtomic`, the incompletenesses `ws6_lawvere_incomplete` and `ws6_omega_nonterminating`, and the Series 03 no-strict-distributive-law `ws3_no_distributive_law` with its Egli–Milner weak-law recovery.*

## The object at stake

Four obligations, in increasing risk:

1. **The graded face and cross-level leak-freeness (the transport hazard, charter §5.5).** Grade the face by depth; define cross-level edges as graded composite faces; prove composition down the tower never drains the face to empty. The inherited `ws3_faces_never_annihilate` is on the *flat-label* carrier; transporting it to the *graded, cross-level* setting is not automatic.
2. **Non-terminating descent and the relating-to = composed-of identification.**
3. **Incompleteness: inherited (diagonal, Ω) + new (tower unknowable from any level), with the coincidence duty against WS4's no-view.**
4. **Attention as grade-shift, and the bialgebra obligation (the graded weak distributive law — the deepest risk).**

**Ambient theory.** WS1's `Winf T`; index `ℤ` (WS2). The **monad** `T` enters here for the first time: composition of relations is a `T`-algebra structure, where `T = P_κ` (bounded powerset, whose monad structure is bounded union). The **functor** `F` is the labelled-powerset observation functor of WS1. The **distributive law** `λ : TF ⇒ FT` is the object of obligation 4; Series 03 proved no *strict* `λ` exists on `P_κ` (`ws3_no_distributive_law`, the Klin–Salamanca four-set diagonal) and recovered the content via a *weak* Egli–Milner law. WS6 must produce a **graded weak** law commuting with observation *and* the depth-grade. The **depth grade** is a `ℤ`-valued (or `ℕ`-valued relative) coordinate on edges, realized — per WS1's C3 salvage — as extra label data `d : ℤ` on the face, which is cheap on the *label* alphabet (`Q ↦ ℤ × Q`) exactly because grading labels does not touch the carrier's boundlessness.

## Part A — The graded face and cross-level leak-freeness

### Candidates

- **GF1 — Grade as a label coordinate; cross-level edge = composite via `lcomp` (the target).**
```lean
/-- A graded label: a quality `q : Q` together with a depth grade `d : ℤ` (relative
    level shift of the edge). The graded carrier is the WS1 labelled carrier at label
    set `ℤ × Q`. -/
abbrev GLabel (Q : Type u) : Type u := ULift ℤ × Q
/-- A cross-level edge composed down through the tower: the `lcomp` of graded edges. -/
noncomputable def crossEdge (T : Tower Q) (path : List (GLabel Q × Winf T)) : Winf T := ...
/-- **Leak-free transport.** A cross-level relation composed through arbitrarily many
    levels never drains its face to the empty object — the inherited
    `ws3_faces_never_annihilate` transported to the graded setting, UNCONDITIONALLY. -/
theorem ws6_crosslevel_never_annihilate (T : Tower Q)
    (t : LkObj κ (GLabel Q) (Winf T)) (ht : t.1.Nonempty)
    (hmem : ∀ p ∈ t.1, NonAtomic p.2) :
    NonAtomic (crossEdge_lcomp T t) ∧ ∀ p ∈ (destInf T (crossEdge_lcomp T t)).succ, NonAtomic p.2
```
- **Success condition:** `ws3_faces_never_annihilate` (transcribed) applies to the graded carrier because grading is *only extra label data* — the composition operator `lcomp` acts on the target/state coordinate, untouched by the `ℤ` grade, so leak-freeness is preserved verbatim.
- **Failure mode (the transport hazard):** if the grade *interacted* with composition — e.g. if composing edges of grades `d₁, d₂` required an operation on `ℤ` that could send the face to empty at some grade — that grade would behave as a floor (a hidden first level), and cross-level relating would fail there. The design forecloses this by making the grade *inert* under composition (grades add: `d₁ + d₂`, and `ℤ` addition never "reaches a bottom" because `ℤ` has no bottom — which is why the index is `ℤ`, not `ℕ`).

**Paper triage — the crux of Part A.** Decidable: does `lcomp` (Series 04's composition) commute with adding a `ℤ`-label coordinate? **Yes, by construction** — `lcomp` is defined by corecursion on the *state* coordinate (`Option (νLk κ Q)`), and `LkMap`/`PkMap` act on targets; a label coordinate rides along untouched (Series 04's `ws3` already carries `Q`-labels through `lcomp` without interaction). So `ws3_faces_never_annihilate` transports *verbatim* with `Q := ℤ × Q`. **The transport hazard is real in general but foreclosed by the inertness of the grade** — and crucially the grade lives in `ℤ` (no bottom), so grade-composition (addition) never manufactures a floor. Winner. **This is the exact payoff of choosing `ℤ` in WS2: it makes grade-composition floor-free.**

- **GF2 — Grade as genuine functor data (a graded functor `F_d`).**
```lean
def GFObj (κ) (Q) (X) := Σ d : ℤ, PkObj κ (Q × X)   -- the functor itself is ℤ-graded
```
**Paper triage.** Makes the grade part of `F`, so leak-freeness must be *re-proved* for the graded functor (its QPF structure and the `lcomp` analogue redone). Higher risk, and the `ws3_faces_never_annihilate` transport is no longer verbatim. **Reject unless GF1's label-coordinate grade proves too weak** — e.g. if the graded weak distributive law (Part D) needs the grade to be functorial rather than a label. Hold as typed fallback.

**Winner: GF1 (grade as inert label coordinate on `ℤ`), GF2 as fallback for Part D.**

## Part B — Non-terminating descent and relating-to = composed-of

```lean
/-- **Descent never terminates.** No first level (WS2 `ws2_no_least`) ⇒ below any
    grade a finer grade of relating, without end; the composite face shrinks toward
    the empty object it never reaches (because the empty object is the atom, and there
    is none). -/
theorem ws6_descent_nonterminating (T : Tower Q) (x : Winf T) :
    ∀ d : ℤ, ∃ (finer : Winf T) (d' : ℤ), d' < d ∧ RelatesAtGrade T x finer d'

/-- **Relating-to IS being-composed-of, at two grades.** A thing at grade `d` and the
    thing it is composed of at grade `d' < d` are related by one graded edge; "is made
    of" is "relates to, read at a finer grade." -/
theorem ws6_relating_is_composition (T : Tower Q) (x y : Winf T) (d d' : ℤ) (h : d' < d) :
    RelatesAtGrade T x y d' ↔ IsComposedOfAtGrade T x y d'
```
**Paper triage.** `ws6_descent_nonterminating` is `ws2_no_least` (no first level) transported through the cross-level edge — decidable, and it genuinely uses the leak-freeness (GF1) to guarantee the finer relatum is non-atomic. `ws6_relating_is_composition` is the *identification duty*: it must be a genuine `↔` between two independently-defined relations (relating-at-grade vs composed-of-at-grade), not a definitional restatement. **Decidable to state; the content is that the two sides are defined separately (one from `destInf`, one from `lcomp`) and proved equal** — a coincidence theorem in the charter's sense. Winner.

## Part C — Incompleteness: inherited + new, with the coincidence duty

### Candidates

- **INC1 — Inherited, carrier-independent (transcribe).**
```lean
theorem ws6_lawvere_incomplete (u : (νPk κ).X) : ¬ Function.Surjective (selfDescription u)  -- transcribed
theorem ws6_omega_nonterminating (hinf : ℵ₀ ≤ κ) : ... -- Ω complete-in-extent, closed at no depth; transcribed
```
**Paper triage.** Both are carrier-independent (they hold at each level and the diagonal is level-local), so they transport for free — exactly as Series 04 imported them from Series 03. Transcribe verbatim. Low risk.

- **INC2 — New: the tower is unknowable from any level (the stratified incompleteness).**
```lean
/-- **Tower-unknowability.** No level knows the whole tower: a total self-survey would
    be a view at a first or last level, and there is none. The epistemic face of
    no-view-from-nowhere. -/
theorem ws6_tower_unknowable (T : Tower Q) (hna : ∀ a, ∃ b, T.le a b ∧ a ≠ b)
    (hnb : ∀ a, ∃ b, T.le b a ∧ a ≠ b) (v : ViewAt T) :
    ∃ y : Winf T, ¬ FaceReaches T v y
```
**Paper triage.** This is *literally WS4's `ws4_no_completing_view`* read epistemically ("no standpoint completes the world" vs "no standpoint is unpositioned"). Decidable — same proof. This raises the **coincidence duty the charter foregrounds**: are `ws6_tower_unknowable` and `ws4_no_completing_view` *one theorem or two*? Paper adjudication: they have the *same proof term* (both are "the view's face misses an object at an unreachable level"), so they are **one theorem read two ways**, not two theorems. WS6 must *state this identity as a theorem*, not conflate them silently:
```lean
/-- **The coincidence: unknowability = no-view, one fact.** The tower-unknowability
    (epistemic) and the no-view-from-nowhere (positional) are the SAME theorem — same
    proof, same missing object — the no-first-no-last fact read once positionally and
    once epistemically. Stated as an identity, per the charter's "one theorem or two"
    duty. -/
theorem ws6_unknowable_eq_noview (T : Tower Q) (hna hnb) (v : ViewAt T) :
    (ws6_tower_unknowable T hna hnb v) = (ws4_no_completing_view T _ v)   -- proof-irrelevant identity
```
**Winner: INC1 (transcribed) + INC2 (new) + the explicit `ws6_unknowable_eq_noview` coincidence** — adjudicating "one theorem," not two.

## Part D — Attention as grade-shift, and the bialgebra obligation

### Candidates for attention

- **AT1 — Attention as the connecting-map action (the target).**
```lean
/-- **Attention is grade-shift.** Attending finer = descending a grade along a
    connecting map; attending coarser = ascending. Attention is the reindexing the
    tower already carries, not a bolted-on dynamics. -/
def attend (T : Tower Q) (Δ : ℤ) (x : Winf T) : Winf T := gradeShift T Δ x
```
**Paper triage.** Decidable to define — it is the graded connecting-map action. But per the charter's coincidence rule (§7, and Series 04's WS6 Part C), definitional grade-shift is *forbidden as a payoff alone*. It must **coincide with an independently motivated attention notion**, or be reported **Trivialized** (attention-vocabulary painted on the maps). Two candidate coincidences:

- **AT2 — Coincidence with the Series 03 feed/starve replicator (recover it as a special case).**
```lean
theorem ws6_attend_recovers_replicator (T : Tower Q) :
    ∀ (special_case), attend T _ = series3_replicator _   -- grade-shift ⊇ feed/starve dynamics
```
**Paper triage.** The charter's first suggested coincidence. Risk: Series 03's replicator was a *quantitative* dynamics (weights on edges, a pitchfork at μ⋆ = ½); grade-shift is a *reindexing*. Whether the reindexing *induces* the replicator on face-mass is the same open question Series 04's WS6 Part C flagged (and did not fully close). **Decidable-on-paper: negative-leaning** — the replicator needs weighted edges, which the tower's grade (a `ℤ` label) does not obviously supply. Hold as the harder coincidence.

- **AT3 — Coincidence with convergence (the long-deferred Lemma B falls out of the connecting-map structure).**
```lean
theorem ws6_attention_converges (T : Tower Q) (x : Winf T) :
    ∃ fixedPoint, Filter.Tendsto (fun n => attend T (-n) x) atTop (𝓝 fixedPoint)  -- Lemma B
```
**Paper triage.** The charter's second suggested coincidence: convergence "falling out of the connecting-map structure." Decidable-on-paper: the descending grade-shift `attend T (-n)` is a cofiltered sequence along the connecting maps; whether it *converges* depends on the limit structure — which WS1's C4 triage found problematic (`P_κ` does not preserve cofiltered limits). **So Lemma B does not fall out for free** — the very limit that would give convergence is the one WS1 could not build. **Decidable verdict: AT3 is negative-leaning on the current carrier** — report convergence as still-open, exactly as Series 03/04 did, unless the colimit-functor fallback (WS1) supplies the missing limit.

**Winner for attention: AT1 (definition) — but reported Partial/Trivialized unless AT2 or AT3 delivers a genuine coincidence.** The honest expected outcome (given the paper triage): **attention-as-grade-shift is definable and structurally natural, but its coincidence with an independent attention notion is open/negative on this carrier — so it is reported Partial, not Discharged, and possibly Trivialized.** This is the charter's signature risk landing exactly where predicted.

### The bialgebra obligation (the deepest risk)

Composition is the algebra (`T = P_κ`, bounded union) side; level-wise unfolding is the coalgebra (`F`) side. Coherence needs a distributive law across levels.

- **DL1 — Strict graded distributive law (target: refute, per Series 03).**
```lean
theorem ws6_no_strict_graded_law (T : Tower Q) : IsEmpty (GradedDistLaw T)   -- transcribe KS diagonal
```
**Paper triage.** Series 03 proved no strict `λ : P_κ P_κ ⇒ P_κ P_κ` exists (`ws3_no_distributive_law`, the four-set Klin–Salamanca diagonal). That diagonal is *carrier-independent* and *grade-independent* (it uses a 4-element `Bool × Bool` carrier, ≤ 2 elements per set, `< κ`). So **no strict graded law exists either** — transcribe the KS diagonal, adding the grade as an inert coordinate that the diagonal ignores. Decidable, low-risk: it is an Impossibility (a success, §7), and it is *inherited* from Series 03. Winner for the strict case.

- **DL2 — Graded weak (Egli–Milner) distributive law commuting with observation AND the depth-grade (the real target).**
```lean
/-- A GRADED weak distributive law: the Egli–Milner union law of Series 03, additionally
    required to commute with the depth-grade `d ↦ d + Δ`. Content: cross-level
    composition coheres with level-wise observation. -/
structure GradedWeakDistLaw (T : Tower Q) where
  weak_law   : WeakEgliMilnerLaw (bounded-union alg) (levelwise dest)   -- transcribed Series 03
  grade_comm : ∀ Δ, commutes weak_law (gradeShift Δ)                    -- NEW: commutes with grade
theorem ws6_graded_weak_law_exists (T : Tower Q) : Nonempty (GradedWeakDistLaw T)
```
**Paper triage — the deepest question in the design.** Series 03 recovered the bidirectional-constitution content via a *weak* Egli–Milner law (`dest (alg t) = ⋃_{x∈t} dest x`, `ws3_weak_bialgebra`). The new requirement is that this weak law *commute with the depth-grade*. Decidable-on-paper: the Egli–Milner union is over the *state* coordinate; the grade is an inert label (GF1); does bounded union commute with `d ↦ d + Δ`? **Union is grade-wise pointwise, and `d + Δ` is a bijection on `ℤ`, so union commutes with grade-shift** (image of a union is the union of images). So the graded weak law exists *if the grade is an inert label (GF1)* — the same inertness that gave leak-freeness gives grade-commutation. **Winner — but conditional on GF1, and this is why GF2 (functorial grade) is the fallback: if the grade must be functorial for some reason, grade-commutation is no longer free.** The bialgebra obligation is dischargeable exactly because `ℤ`-labels are inert; if that inertness breaks, report the graded weak law as failing to commute (a hidden floor/cap, charter §5.5 bialgebra risk).

**Winner for the bialgebra obligation: DL1 (no strict law, transcribed Impossibility) + DL2 (graded weak law exists, conditional on GF1's inert grade).**

## Winner summary and coincidence duties

- **Part A:** GF1 — leak-free transport verbatim, floor-free because `ℤ` has no bottom. **Coincidence duty (i):** leak-freeness must be the genuine transported theorem — checked by the strip test (remove the grade; the theorem is Series 04's `ws3_faces_never_annihilate`, which is real). If composition leaked at some grade, report that grade as a hidden floor (a WS4 no-first-level failure). GF1 passes.
- **Part B:** descent non-termination + relating = composed-of as a genuine `↔`.
- **Part C:** INC1 (transcribed) + INC2 (new) + `ws6_unknowable_eq_noview` (one theorem, adjudicated).
- **Part D:** AT1 defined; **coincidence duty (ii):** AT2/AT3 open/negative on this carrier ⇒ attention reported **Partial, possibly Trivialized**. DL1 (no strict law) + DL2 (graded weak law, conditional on GF1).

### Definitions and lemmas needed

```lean
namespace Series05.WS6
-- transcribed: lcomp, NonAtomic, ws3_faces_never_annihilate, ws6_lawvere_incomplete,
-- ws6_omega_nonterminating, ws3_no_distributive_law, ws3_weak_bialgebra (Egli–Milner)

def GLabel (Q) := ULift ℤ × Q
def gradeShift (T : Tower Q) (Δ : ℤ) : Winf T → Winf T := ...
def RelatesAtGrade (T : Tower Q) (x y : Winf T) (d : ℤ) : Prop := ...
def IsComposedOfAtGrade (T : Tower Q) (x y : Winf T) (d : ℤ) : Prop := ...
def crossEdge_lcomp (T : Tower Q) (t : LkObj κ (GLabel Q) (Winf T)) : Winf T := lcomp t  -- Q := GLabel
```

### Proof architecture

- **Leak-freeness (GF1):** instantiate transcribed `ws3_faces_never_annihilate` at `Q := GLabel Q = ℤ × Q`. The proof is *unchanged* — Series 04's `lcomp` already carries arbitrary `Q`-labels through composition. The only new remark: grade-composition is `ℤ`-addition, which has no bottom, so no grade is a floor.
- **Graded weak law (DL2):** transcribe Series 03's Egli–Milner `ws3_weak_bialgebra`; prove `grade_comm` by "image of bounded union = bounded union of images" (`Set.image_iUnion`) plus "`d ↦ d + Δ` is a bijection."
- **No strict law (DL1):** transcribe `ws3_no_distributive_law`; the four-set diagonal ignores the grade coordinate.
- **Incompleteness coincidence:** `ws6_unknowable_eq_noview` by proof irrelevance (both are `ws4_no_completing_view`).

**Dependencies on imported upstream theorems.** WS1: `Winf`, `destInf`, connecting maps, `gradeShift` from the reindexing. WS2: `ws2_no_least` (Part B descent), the `ℤ` index (Part A floor-freeness, Part D grade-commutation). WS4: `ws4_no_completing_view` (Part C coincidence — the shared theorem). Transcribed Series 04: `ws3_faces_never_annihilate`, `lcomp`, `NonAtomic`, `ws6_lawvere_incomplete`, `ws6_omega_nonterminating`. Transcribed Series 03: `ws3_no_distributive_law`, `ws3_weak_bialgebra` (Egli–Milner weak law).

## What counts as failure

- *Leak at some grade (transport hazard):* if composition drained a face to empty at grade `d`, that grade is a hidden first level — cross-level relating fails there. Foreclosed by GF1's inert `ℤ`-grade; report the grade as a floor if GF1 breaks.
- *No graded weak distributive law (bialgebra risk):* if the weak law does not commute with the grade, cross-level relating and level-wise structure disagree — a hidden floor/cap. Foreclosed by union/grade commutation; report failure if the grade must be functorial (GF2).
- *Attention trivialized:* if neither AT2 nor AT3 gives a genuine coincidence, attention-as-grade-shift is vocabulary on the maps — reported **Trivialized** (a success per §7, an honest negative). This is the expected outcome on the current carrier.
- *Incompleteness conflated:* if `ws6_tower_unknowable` and `ws4_no_completing_view` are silently identified without the `ws6_unknowable_eq_noview` adjudication, the coincidence duty is unmet.

## Outcome classes (per charter §7)

- **Discharged:** Part A (leak-free transport), Part B (descent, relating = composed-of), Part C (INC1 + INC2 + coincidence), Part D DL1 (no strict law, Impossibility) + DL2 (graded weak law, conditional on GF1).
- **Impossibility proved (a success):** DL1 — no strict graded distributive law (inherited KS diagonal).
- **Partial / Trivialized (the expected honest negative):** attention-as-grade-shift — definable, structurally natural, but its coincidence with an independent attention notion (replicator AT2 / convergence AT3) is open or negative on this carrier. Reported Partial, possibly Trivialized. Lemma B (convergence) remains open, blocked by the same cofiltered-limit gap WS1 flagged.

## Deliverable

`series-05/formal/ws6.lean`: transcribed `ws3_faces_never_annihilate`, `lcomp`, `ws6_lawvere_incomplete`, `ws6_omega_nonterminating`, `ws3_no_distributive_law`, `ws3_weak_bialgebra`; `GLabel`, `gradeShift`, `crossEdge_lcomp`, `RelatesAtGrade`, `IsComposedOfAtGrade`; `ws6_crosslevel_never_annihilate` (A), `ws6_descent_nonterminating` + `ws6_relating_is_composition` (B), `ws6_tower_unknowable` + `ws6_unknowable_eq_noview` (C), `attend` + `ws6_no_strict_graded_law` (DL1) + `GradedWeakDistLaw` + `ws6_graded_weak_law_exists` (DL2), with AT2/AT3 typed and reported Partial. Axiom check owed on `ws6_crosslevel_never_annihilate`, `ws6_graded_weak_law_exists`, `ws6_no_strict_graded_law`.
