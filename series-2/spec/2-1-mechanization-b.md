# 2-1b-mechanization — Work Order: The Transfer Theorem and the Design-Ready Group

**This document describes:** `series-2/formal/Spec21b.lean` (new file; imports `Spec21a`)
**Normative sources:** `series-2/2-0.md` and `series-2/2-1.md`. Where this document and the specs disagree, the specs win; report, don't improvise.
**Audience:** Claude Code, executing without further clarification.
**Naming note:** this is `2-1b`, not `2.2`, because every item below is normed by specs 2.0/2.1; the name `2-2-mechanization` is reserved for after spec 2.2 (π, quality-weighting, deployment ratification) is written. A few light definitions ARE introduced here out of necessity; they are quarantined in §8's ratification list and must be flagged as `pending ratification (2.2)` in their doc-comments.

---

## 1. Purpose and scope

This order encapsulates the maximum open ground reachable without new design decisions. The centerpiece is the **transfer theorem**: spec 2.1 §4's literature-verified construction of Ω, machine-checked *modulo the existence of the raw final coalgebra*. With L1 already proved, the covariety argument can be formalized in full: **if the raw universe νF exists, then Ω — the universe of coherent objects — exists and is final among coherent models.** That converts T2's status from [blocked: 2.1 construction] to [transfer proved; blocked only on νF existence], isolating the entire remaining gap in one classical, citable fact (Adámek–Trnková) to be attacked in its own order via `MvQPF`.

| ID | Name | Priority |
|----|------|----------|
| T2t-i | Coherent part: `CoherentAt`, `Good` pairs, `coherentPart` as the greatest good pair | MUST |
| T2t-ii | Image lemma: any hom from a coherent model has a good image pair | MUST |
| T2t-iii | **Transfer theorem**: ambient finality ⟹ unique morphism from every coherent model, landing in the coherent part | MUST |
| T2t-iv | Subtype packaging of the coherent part as a `Model` | SHOULD (droppable; see plumbing warning) |
| PRJb | Deployable attention + the **dichotomy**: proper or self-anchored | MUST |
| T12s | Static mutual clarification: a shared bearing sits in the aperture on every containing side | MUST |
| P1b1 | Inexhaustibility, barrier one: the shared-part bound | MUST |
| P2c | Contexts-differ witness: one shared relation, two unequal apertures | MUST |
| C2d | Connectivity defined; **coproduct disconnection** (C2 fails for general models) | MUST |
| T14q | Qualitative containment predicates + four-corner example models | SHOULD |
| DOC | Spec status-label housekeeping (§7) | MUST |

**Out of scope — do not attempt** (§9): νF existence itself (`MvQPF.Cofix` — the *next* order), P5/dyad construction, witnessing/reveals structure (hence T13's content, T4's ≈w, general P1's barrier two, T7), π's quality-weighting, T11, anything temporal.

---

## 2. Environment and conventions

As in `2-1-mechanization.md` §2, plus:

- **New file** `series-2/formal/Spec21b.lean`, `import Spec21a` (adjust to the actual module path registered in `lake/lakefile.toml`; register `Spec21b` as a library root following the established precedent, and record the wiring in the mapping table).
- Additional imports as needed: `Mathlib.Logic.Relation` (for `Relation.ReflTransGen`, used by C2d). Keep imports minimal; `import Mathlib` acceptable with a note if resolution fights back.
- Namespace: continue `RelEx.TwoSorted`.
- All prior conventions in force: no `sorry`, no new axioms, `#print axioms` audit block, doc-comments with spec IDs against 2-0.md/2-1.md, mapping table at file foot, deviations recorded.

---

## 3. Part A — the transfer theorem (T2t)

**Why this matters (for doc-comments):** spec 2.1 §4 gives Ω a three-step construction: (1) νF exists on Set × Set [classical: Adámek–Trnková 2011]; (2) coherent coalgebras form a covariety [L1 — proved in Spec21a]; (3) Ω is the greatest coherent subcoalgebra of νF. This part mechanizes steps (2)→(3) as a *transfer*: finality of the ambient raw universe transfers to the coherent part. Philosophically: given any lawless universe of raw patterns, **the objects — the coherent patterns — form a universe of their own, and every coherent description specifies exactly one inhabitant of it.** The only unformalized residue after this part is step (1), a single citable classical theorem.

### 3.1 T2t-i: the coherent part

```lean
/-- Coherence at a single relation (elementwise; ambient-absolute). -/
def CoherentAt (Z : Raw) (r : Z.R) : Prop :=
  ∀ x : Z.O, x ∈ Z.endpoints r → r ∈ Z.pat x

/-- A good pair of subsets: elementwise coherent and closed under the two-sorted
structure (endpoints of kept relations are kept objects; patterns of kept objects
are kept relations). Good pairs are the two-sorted subcoalgebras-with-coherence;
`coherentPart` below is their union. -/
structure Good (Z : Raw) (UO : Set Z.O) (UR : Set Z.R) : Prop where
  coh : ∀ r ∈ UR, CoherentAt Z r
  ends : ∀ r ∈ UR, ∀ x ∈ Z.endpoints r, x ∈ UO
  pats : ∀ x ∈ UO, Z.pat x ⊆ UR

/-- The coherent part of a raw universe: the union of all good pairs.
Spec 2.1 §4, step (3): "Ω is the greatest coherent subcoalgebra of νF" —
this is that greatest subcoalgebra, as a pair of subsets. May be empty for
pathological Z; for Z = νF nonemptiness is separate (the self-loop is coherent). -/
def coherentPartO (Z : Raw) : Set Z.O := ⋃₀ { UO | ∃ UR, Good Z UO UR }
def coherentPartR (Z : Raw) : Set Z.R := ⋃₀ { UR | ∃ UO, Good Z UO UR }

/-- The union of all good pairs is itself good: the coherent part is the
GREATEST good pair (Knaster–Tarski by hand, on an elementwise-closed property). -/
theorem coherentPart_good (Z : Raw) :
    Good Z (coherentPartO Z) (coherentPartR Z) := by
  sorry
```

Proof plan for `coherentPart_good`: each field is elementwise. For `coh`: r ∈ the union means r ∈ some UR with a witnessing good pair; apply that pair's `coh`. For `ends`: same unpacking; the endpoint lands in that pair's UO, which is ⊆ the union — but note the union in `coherentPartO` ranges over UO's *paired with some UR*; the witnessing pair supplies exactly that, so membership in the big union follows by `Set.mem_sUnion` with the witness. `pats` symmetric. Pitfall: the two unions are defined by *separate* comprehensions; always carry the full pair witness `⟨UO, UR, hGood⟩` so both memberships are available. Also prove the one-liner `good_le_coherentPart`: any good pair is contained componentwise in the coherent part (`Set.subset_sUnion_of_mem` with the pair witness).

### 3.2 T2t-ii: the image lemma

```lean
/-- Bridge: forget a Model's coherence bundling to get a Raw. -/
def Model.toRaw (M : Model) : Raw :=
  ⟨M.O, M.R, M.endpoints, M.pat, M.pat_nonempty⟩

/-- Spec 2.1 §4 (image lemma): the image of ANY hom from a coherent model is a
good pair. This is L1-quotient reasoning done elementwise — the mechanized form
of "homomorphic images of coherent coalgebras are coherent," the covariety
closure that makes the transfer theorem work. -/
theorem image_good (M : Model) (Z : Raw) (h : Hom M.toRaw Z) :
    Good Z (Set.range h.fO) (Set.range h.fR) := by
  sorry
```

Proof plan: three fields.
- `coh`: given `h.fR r` and `x' ∈ Z.endpoints (h.fR r)`: rewrite by `h.end_comm`, `Sym2.mem_map` to get `x` with `x ∈ M.endpoints r`, `h.fO x = x'`. M's bundled `coherent` gives `r ∈ M.pat x`; then `h.pat_comm` puts `h.fR r ∈ Z.pat x'`. (This is `coherent_of_surjective_hom`'s argument restricted to the image — do NOT try to reuse that theorem directly; it is stated for surjective homs onto all of B. Elementwise is cleaner here.)
- `ends`: `x' ∈ Z.endpoints (h.fR r)` → via `end_comm`/`mem_map`, `x' = h.fO x` → `x' ∈ range h.fO`.
- `pats`: `Z.pat (h.fO x) = h.fR '' M.pat x ⊆ range h.fR`.

### 3.3 T2t-iii: the transfer theorem

```lean
/-- Two-sorted finality for raw universes. -/
def IsFinalRaw (Z : Raw) : Prop :=
  ∀ A : Raw, ∃! _h : Hom A Z, True

/-- Spec 2.1 §4 / Spec 2.0 T2 — THE TRANSFER THEOREM. If the raw universe is
final, then every coherent model admits exactly one morphism into it, and that
morphism lands entirely in the coherent part. Objects exist, modulo the raw
universe: the covariety step of Ω's construction is machine-checked here; the
sole remaining gap is the classical existence of νF (Adámek–Trnková 2011),
scheduled for its own order. Philosophically: every coherent description
specifies exactly one object, and objects live nowhere but the coherent part. -/
theorem transfer (Z : Raw) (hZ : IsFinalRaw Z) (M : Model) :
    ∃! h : Hom M.toRaw Z, True := hZ M.toRaw

theorem transfer_lands (Z : Raw) (M : Model) (h : Hom M.toRaw Z) :
    (∀ x, h.fO x ∈ coherentPartO Z) ∧ (∀ r, h.fR r ∈ coherentPartR Z) := by
  sorry
```

Proof plan for `transfer_lands`: `image_good` gives a good pair; `good_le_coherentPart` (or direct `Set.mem_sUnion`) puts every range element in the coherent part. (`transfer` itself is definitionally the hypothesis — state it anyway; it is the named anchor the spec's T2 entry will point at, and the pairing of the two theorems in one place IS the result.)

### 3.4 T2t-iv (SHOULD): subtype packaging

Package `(coherentPartO Z, coherentPartR Z)` as a bona fide `Model` on subtype carriers, with `endpoints` valued in `Sym2 {x // x ∈ coherentPartO Z}`. **Plumbing warning:** constructing a `Sym2` over a subtype from membership proofs is dependent-elimination territory (`Sym2.ind`/`Quot.recOn`; check whether this mathlib rev has an `attach`-style helper for `Sym2`). Budget ~1.5 hours; if it resists, drop with a note — the transfer theorem above already carries the mathematical content, and the packaging is presentation. If completed, also supply `coherent` for the packaged model from `coherentPart_good.coh` and note that its finality-among-coherent-models is then a corollary of `transfer` + `transfer_lands` (statement optional).

---

## 4. Part B — the design-ready group

### 4.1 PRJb: deployability and the dichotomy

```lean
/-- Spec 2.1 §3.7 (pre-registered definition, D15): an attention is DEPLOYABLE
by `x` iff it is the aperture of some actual attending of `x`. A8 recognizes no
free-floating attention: all attending is along a relation through its context. -/
def Deployable (M : Model) (x : M.O) (A : Set M.R) : Prop :=
  ∃ r ∈ M.pat x, A = ctx M x r

/-- Spec 2.0 §3, PR-J(b), in the exact form the interface supports — the
DICHOTOMY: every deployable attention is proper, or its witnessing relation is
self-anchored. Together with `reflexive_saturation` (Spec21a), this settles
PR-J(b)'s interface-level status completely: properness of deployable attention
is a THEOREM off the self-anchored locus and an AXIOM-candidate on it — the
same address C3 gave A8(i). The full PR-J(b) ("every deployable attention is
proper") is therefore exactly as strong as A8(i)-at-loops, which is the
pre-registered question resolved: the desired answer holds iff the framework's
one axiom is retained at self-reference. -/
theorem deployable_dichotomy (M : Model) (x : M.O) (A : Set M.R)
    (hA : Deployable M x A) :
    A ⊂ M.pat x ∨ ∃ r ∈ M.pat x, A = ctx M x r ∧ SelfAnchored M r := by
  sorry
```

Proof plan: unpack `hA` to `⟨r, hr, rfl⟩`; `by_cases h : SelfAnchored M r`; right branch packages the witness; left branch is `generic_properness M r x hr h`. Note `Classical.choice` will likely enter via `by_cases` — acceptable, record in audit.

### 4.2 T12s: static mutual clarification

```lean
/-- Spec 2.0 §2.5 / T12, static skeleton: a SHARED bearing on `r` sits inside
`r`'s aperture on EVERY side that contains it. This is the statics of mutual
clarification — the same enrichment is aperture-material for both relata at
once, which is the mechanism by which clarifying a shared relation clarifies
both parties (and, across the containment square, both whole and part). The
PROPAGATION of clarification — enrichment arriving over time — is dynamics,
Series 3 (2.0 O9); this lemma is the load-bearing static fact under it. -/
theorem shared_bearing_in_both_apertures (M : Model) (r s : M.R) (x y : M.O)
    (hsx : s ∈ M.pat x) (hsy : s ∈ M.pat y)
    (hbears : M.dy r ∈ M.endpoints s) :
    s ∈ ctx M x r ∧ s ∈ ctx M y r :=
  ⟨⟨hsx, hbears⟩, ⟨hsy, hbears⟩⟩
```

If the term proof above compiles as written, keep it — the symmetry of the two components *is* the point (one bearing, two apertures, same entry).

### 4.3 P1b1: the shared-part barrier

```lean
/-- `y` relates beyond `x`: some part of `y` is not shared with `x`. -/
def RelatesBeyond (M : Model) (y x : M.O) : Prop :=
  ∃ r ∈ M.pat y, r ∉ M.pat x

/-- Spec 2.0 §2.4 / general P1, barrier one (shared-part bound): whenever `y`
relates beyond `x`, the shared part is a PROPER part of `y` — so `x`'s access
to `y`, which runs entirely through shared relations, cannot exhaust `y`.
Barrier two (the foreign-context bound) needs the witnessing structure of a
later spec and is deliberately absent here. -/
theorem shared_part_barrier (M : Model) (x y : M.O) (h : RelatesBeyond M y x) :
    M.pat x ∩ M.pat y ⊂ M.pat y := by
  sorry
```

Proof plan: `Set.inter_subset_right` for ⊆; strictness from `h`'s witness (it is in `pat y`, not in the intersection).

### 4.4 P2c: the contexts-differ witness

```lean
/-- Spec 2.0 §2.4 / P2 with content: one shared relation, two genuinely unequal
apertures. Spec21a's P2 was type-level (the two directions belong to different
objects); this witness shows the difference is MATERIAL — the same relation's
context in `x` contains a bearing its context in `y` lacks, because the bearing
is private to `x`. Same part, different wholes, different lenses. -/
theorem contexts_differ :
    ∃ (M : Model) (r : M.R) (x y : M.O),
      r ∈ M.pat x ∧ r ∈ M.pat y ∧ ctx M x r ≠ ctx M y r := by
  sorry
```

Construction plan: `O := Bool` (x := true, y := false), `R := Bool` (r₀ := true — the shared relation; s₁ := false — x's private bearing). `endpoints r₀ := s(true, false)`; `endpoints s₁ := s(true, true)`; `dy _ := true` (so `dy r₀ = true ∈ endpoints s₁` — s₁ bears on r₀); `pat true := Set.univ` (x holds both), `pat false := {true}` (y holds only the shared r₀). Check coherence by cases (four small goals; `decide`-friendly if you set things up with `Bool`). Then `s₁ ∈ ctx M x r₀` but `s₁ ∉ ctx M y r₀` (not in `pat false`); conclude inequality via `Set.ne_of_mem_of_not_mem`-style reasoning (exact spelling via `exact?`).

### 4.5 C2d: connectivity and the coproduct disconnection

```lean
/-- One step of relational connection between objects (raw level): some relation
has both among its endpoints. -/
def StepR (Z : Raw) (x y : Z.O) : Prop :=
  ∃ r : Z.R, x ∈ Z.endpoints r ∧ y ∈ Z.endpoints r

/-- Spec 2.0 C2 (weak form), the definition — pending ratification (2.2):
a raw universe is connected iff any two objects are linked by a finite chain
of shared-endpoint steps. -/
def Connected (Z : Raw) : Prop :=
  ∀ x y : Z.O, Relation.ReflTransGen (StepR Z) x y

/-- Spec 2.0 C2, SHARPENED: connectivity is NOT interface-forced — the
coproduct of two inhabited raw universes is disconnected. Consequence for the
pre-registered conjecture: C2, if true, is a theorem about Ω SPECIFICALLY
(about what the closure of coherent descriptions produces), not about the
signature. The desired answer ("the fish is a part of me, ever so slightly")
cannot be obtained by definitional accident; it must be earned at 2.2. This
is D15 working as intended. -/
theorem coprod_disconnected (A B : Raw) (a : A.O) (b : B.O) :
    ¬ Connected (coprod A B) := by
  sorry
```

Proof plan: suppose connected; obtain a `ReflTransGen` chain from `Sum.inl a` to `Sum.inr b`. Prove the invariant `IsLeft`: by induction on the chain (`Relation.ReflTransGen.head_induction_on` or `.trans_induction_on`; check the recursor names), a single `StepR (coprod A B)` step preserves left-ness — unfold `coprod`: a relation `Sum.inl r` has endpoints `(A.endpoints r).map Sum.inl`, so both endpoint members are `inl _` (via `Sym2.mem_map`); symmetric for `inr`. So no step connects `inl _` to `inr _`; the chain's endpoints contradict. Pitfall: `Sum.elim` unfolding inside `Sym2.mem_map` — the four-case pattern from Spec21a's `coherent_sum` is the template; reuse its `simp only [coprod, ...]` incantations.

---

## 5. Part C — T14q (SHOULD): the qualitative containment square

Definitions (all `pending ratification (2.2)` — these are the *unweighted shadows* of π; the graded forms need 2.2's quality-weighting):

```lean
def ContainedIn (M : Model) (x y : M.O) : Prop := M.pat x ⊆ M.pat y
def Touches     (M : Model) (x y : M.O) : Prop := (M.pat x ∩ M.pat y).Nonempty
def MutualPartial (M : Model) (x y : M.O) : Prop :=
  Touches M x y ∧ ¬ ContainedIn M x y ∧ ¬ ContainedIn M y x
```

Then a **four-corner witness**: one small `Model` (or, with permission, up to four tiny separate models if one combined model fights coherence) exhibiting: full containment one way (the heart: `ContainedIn heart me ∧ ¬ ContainedIn me heart`), full containment the other (humanity), mutual partiality (musicianship), and touching-without-containment at minimal overlap (the fish: `Touches ∧ ¬ ContainedIn` either way, overlap a single shared relation). Doc-comments should quote the spec's four examples by name; the fish's comment gets the line: *a part of me, ever so slightly — the overlap is one relation, and it is not nothing.* Budget ~1.5 hours; drop to a subset of corners with a note if coherence bookkeeping balloons.

---

## 6. Build, verify, deliver

1. `lake build` clean; no `sorry`; no warnings introduced.
2. Axiom audit block covering every named theorem in this file; baseline only; note which results are choice-free.
3. Declaration order within Part A is normative: `CoherentAt` → `Good` → `coherentPart*` → `coherentPart_good` → `Model.toRaw` → `image_good` → `IsFinalRaw` → `transfer` / `transfer_lands` → (T2t-iv if attempted). Elsewhere order is free.
4. Mapping table at file foot (template below), deviations recorded.

```
-- Specs 2.0 / 2.1 ↔ series-2/formal/Spec21b.lean
-- T2 (transfer, i)    = RelEx.TwoSorted.coherentPart_good (+ CoherentAt, Good, coherentPartO/R)
-- T2 (transfer, ii)   = RelEx.TwoSorted.image_good
-- T2 (transfer, iii)  = RelEx.TwoSorted.transfer, RelEx.TwoSorted.transfer_lands
-- T2 (packaging, iv)  = <name>                          (SHOULD; may be absent)
-- PR-J(b) (dichotomy) = RelEx.TwoSorted.deployable_dichotomy (+ Deployable)
-- T12 (statics)       = RelEx.TwoSorted.shared_bearing_in_both_apertures
-- P1 (barrier one)    = RelEx.TwoSorted.shared_part_barrier (+ RelatesBeyond)
-- P2 (content)        = RelEx.TwoSorted.contexts_differ
-- C2 (sharpening)     = RelEx.TwoSorted.coprod_disconnected (+ StepR, Connected)
-- T14q                = <names>                          (SHOULD; may be absent)
-- Pending ratification (2.2): Deployable*, RelatesBeyond, StepR, Connected,
--   ContainedIn, Touches, MutualPartial   (*Deployable is 2.1 §3.7's definition,
--   transcribed; the rest are new here.)
-- Deviations from 2-1b-mechanization.md: <list, or "none">
```

## 7. Spec status-label housekeeping (MUST)

Apply these edits (smallest faithful diff; preserve surrounding prose):

In `series-2/2-0.md` §5:
- P4 static: `[unblocked]` → `[proved]` (Spec21a; note "static form; dynamic form O9").
- PR-J(a): `[unblocked]` → `[proved]` (Spec21a).
- PR-J(b): → `[dichotomy proved (Spec21b): proper or self-anchored; full form ⟺ A8(i) at self-reference]`.
- T2: → `[transfer proved (Spec21b): Ω exists and is final among coherent models, modulo νF existence (classical: Adámek–Trnková 2011); νF mechanization scheduled]`.
- T12: → `[statics skeleton proved (Spec21b); propagation O9]`.
- General P1: → `[barrier one proved (Spec21b); barrier two needs witnessing structure]`.
- C2: append `— sharpened (Spec21b): fails for general models (coproduct disconnection); if true, a theorem about Ω specifically.`
- T14: if T14q lands, append `— qualitative shadow defined and witnessed (Spec21b); graded form awaits π.`

In `series-2/2-1.md` §5:
- C3: mark both cases `[proved at interface level]` (Spec21a), with the residue note intact.
- L1: `[proved, incl. coproducts]` (Spec21a).
- §7's L1 obligation line: mark discharged.

## 8. Ratification list (for the 2.2 spec author, not for you)

`Deployable` (transcribed from 2.1 §3.7), `RelatesBeyond`, `StepR`/`Connected`, `ContainedIn`/`Touches`/`MutualPartial`. Each is used here in its weakest defensible form; 2.2 will ratify, refine (quality-weighting), or replace them, and D15 requires that their definitions above were chosen without reference to desired outcomes of PR-J(b)/C2/C1 — which is why `coprod_disconnected` (an *anti*-desired-outcome result) is a MUST: it demonstrates the definitions were not tuned.

## 9. Out of scope — do not attempt

νF existence / `MvQPF.Cofix` / terminal sequences (next order, with its own encoding plan); P5 (dyad construction); witnessing/reveals structure and everything downstream (T13 content, T4's ≈w, P1 barrier two, T7); π's quality-weighting and T14's graded laws; T11; C1; anything temporal (O9). If an unblocked-looking lemma outside the list appears, note it in the PR; do not prove it.

---

*End of work order. The transfer theorem is the crown: after it, "objects exist" rests on exactly one classical citation, and everything the framework says about coherence, deployment, barriers, and connection has a machine-checked static skeleton. Write Part A so a philosopher can read `transfer` and its comment and understand: given any raw universe at all, the coherent patterns in it form a universe of their own — and that is what objects are.*
