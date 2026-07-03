# 2.00-mechanization — Work Order: Unblocked Theorems (T1, P0–P3)

**This document describes:** `formal/Spec200.lean`
**Normative source:** `scratch/spec/2.00.md` (Spec 2.00). Where this document and the spec disagree, the spec wins; report the discrepancy rather than improvising.
**Audience:** Claude Code, executing without further human clarification. Everything needed is in this file. Follow it closely; do not expand scope.

---

## 1. Purpose and scope

Spec 2.00 identifies exactly one theorem group as *unblocked* — provable now, independent of all open machinery (the enriched/quantaloid setting of O1 is NOT needed):

| ID | Name | Priority |
|----|------|----------|
| T1a | The Collapse Theorem, final-coalgebra form | MUST |
| T1b | The Collapse Theorem, bisimulation form | MUST |
| T1c | Corollary: any final coalgebra of the shadow functor has subsingleton carrier | SHOULD |
| P0 | Pan-observation | MUST |
| P1s | No transparency to self (self-observation form of P1) | MUST |
| P2 | Asymmetry for free | MUST |
| P3 | Co-requirement satisfied (type-level; see §5.4 — deliverable is a definition + doc-comment, not a theorem) | MUST |

Everything else in the spec (T2–T11, C1, general P1) is **out of scope** — see §7 for the explicit do-not-attempt list.

**Why these matter (context, so the doc-comments you write are accurate):** T1 is the repository's first machine-checked theorem and, under the spec's D5, its "creation story": in the quality-forgetting boolean shadow of the framework, the entire universe provably collapses to a single self-relating point — without graded observation, nothing distinguishes anything. It is also the "non-rigging evidence" of D12: the machinery does *not* automatically produce many objects. P0–P3 are small propositions carrying disproportionate philosophical weight; several are trivial *by design*, and the doc-comments must say so — triviality-by-construction is the point being demonstrated (the signature makes certain errors unformulable rather than forbidden).

---

## 2. Environment and conventions

- **Toolchain:** Lean 4 with mathlib (the repository's `lakefile` and toolchain pin are already configured; do not change them). Build with `lake build`.
- **Imports:** Use the narrowest mathlib imports that work. `import Mathlib.Data.Set.Basic` and `import Mathlib.Data.Set.Image` should suffice; if resolution is painful, `import Mathlib` is acceptable but note it in the PR description. **Do not** import `Mathlib.CategoryTheory.*` — we hand-roll coalgebra structures deliberately (the spec's category theory is tooling, not ontology, and the hand-rolled version keeps this file self-contained).
- **No `sorry`, no new axioms.** After building, run `#print axioms` on every theorem (instructions in §6). `Classical.choice`, `propext`, `Quot.sound` are acceptable (mathlib baseline); anything else is a failure.
- **Namespace:** everything in `namespace RelEx`. Sections: `RelEx.Shadow` (T1), `RelEx.Arena` (P-block).
- **Naming:** theorem names as given below, exactly — they are cross-referenced from the spec. If you must deviate, update the mapping table at the bottom of the Lean file (§6.3).
- **Doc-comments:** every definition and theorem gets a `/-- ... -/` doc-comment containing (a) the spec ID (e.g., "Spec 2.00, T1a"), (b) one sentence of mathematical content, (c) one sentence of philosophical content, drawn from this document.
- **Universe hygiene:** work in a single universe `u` (`variable {X Y : Type u}` style). If universe issues bite, monomorphize to `Type` and note it; nothing here needs polymorphism essentially.

---

## 3. Part A — T1a: the Collapse Theorem, final-coalgebra form

### 3.1 Mathematical statement

Let F be the *boolean-shadow unfolding functor*: `F X = { S : Set X // S.Nonempty }` (an entity's unfolding is a nonempty, unordered set of entities — no pairs, no labels, no qualities; nonemptiness encodes the spec's "emptiness unformulable," D4). Then the one-point coalgebra is final: for every coalgebra `(X, c)` there is exactly one coalgebra morphism into it. Consequently the terminal universe of the shadow is a single self-relating point.

### 3.2 Definitions (write these verbatim, then adjust only if the compiler forces it)

```lean
namespace RelEx
namespace Shadow

/-- Spec 2.00, §2.3 "boolean shadow" / D4. The quality-forgetting unfolding functor:
an unfolding is a nonempty unordered set of successors. Nonemptiness is enforced by
the subtype (emptiness is *unformulable*, not forbidden — the D4 design pattern). -/
def F (X : Type u) : Type u := { S : Set X // S.Nonempty }

/-- Functorial action of `F` on functions (image on the underlying set). -/
def mapF (h : X → Y) (s : F X) : F Y :=
  ⟨h '' s.1, s.2.image h⟩

/-- A coalgebra of `F`: a carrier with an unfolding map. Spec: a "description" (D2, §2.1). -/
structure Coalg where
  X : Type u
  c : X → F X

/-- A coalgebra morphism: a carrier map commuting with unfolding. -/
structure Hom (A B : Coalg) where
  f : A.X → B.X
  comm : ∀ a, B.c (f a) = mapF f (A.c a)

/-- Finality: every coalgebra admits exactly one morphism in. -/
def IsFinal (Z : Coalg) : Prop :=
  ∀ A : Coalg, ∃! h : Hom A Z, True

/-- The one-point coalgebra: the single self-relating point (the spec's ω̂ in the shadow). -/
def unit : Coalg :=
  ⟨PUnit, fun _ => ⟨Set.univ, ⟨PUnit.unit, trivial⟩⟩⟩

end Shadow
end RelEx
```

Notes for the implementer:
- `Set X` in Lean is `X → Prop`; `s.2.image h` uses `Set.Nonempty.image : s.Nonempty → (h '' s).Nonempty`. If the name differs in the pinned mathlib, search with `exact?` — the fact is one `obtain`/`exact ⟨h x, x, hx, rfl⟩` away by hand.
- `ExistsUnique` with a `True` predicate is a slightly awkward but simple way to say "exactly one morphism" without defining a category. Unfold it as: existence + (any two are equal).
- `Hom` equality needs structure eta: two `Hom`s with equal `.f` fields are equal because `comm` is a `Prop` (proof irrelevance). Tactic pattern: `cases h₁; cases h₂; congr 1; ...`.

### 3.3 Theorem and proof, step by step

```lean
/-- Spec 2.00, T1a (Collapse / The One). The one-point coalgebra is final for the
boolean-shadow functor: with quality forgotten, the universe is a single
self-relating point. "Not bang, but becoming" (D5); non-rigging evidence (D12). -/
theorem unit_final : IsFinal Shadow.unit := by
  sorry
```

Proof plan (follow in order):

1. **Intro.** `intro A`. Must produce `∃! h : Hom A unit, True`.
2. **Existence.** Provide `h := ⟨fun _ => PUnit.unit, ?comm⟩`.
   The commuting obligation, unfolded: for all `a`,
   `unit.c (PUnit.unit) = mapF (fun _ => PUnit.unit) (A.c a)`, i.e.
   `⟨Set.univ, _⟩ = ⟨(fun _ => PUnit.unit) '' (A.c a).1, _⟩` in `F PUnit`.
3. **Subtype extensionality.** Reduce to equality of underlying sets via `Subtype.ext`. Goal becomes `Set.univ = (fun _ => PUnit.unit) '' (A.c a).1` (possibly flipped; use `.symm` as needed).
4. **Set extensionality.** `Set.eq_univ_iff_forall` (or `ext p` + `simp`) reduces to: every `p : PUnit` is in the image. Since `p = PUnit.unit` (PUnit is a subsingleton — `Subsingleton.elim` or pattern match), it suffices that the image is inhabited by `PUnit.unit`.
5. **Use nonemptiness — this is the crux.** `obtain ⟨x, hx⟩ := (A.c a).2` gives a point of the unfolding; then `⟨x, hx, rfl⟩ : PUnit.unit ∈ (fun _ => PUnit.unit) '' (A.c a).1`. **This is the only place seriality/nonemptiness is used, and it is essential** — with possibly-empty unfoldings the theorem is false (that is the whole point of T1). If your proof never uses `(A.c a).2`, it is wrong even if it compiles.
6. **Uniqueness.** Given `h₁ h₂ : Hom A unit`, show `h₁ = h₂`: `cases`-destructure both, `congr 1`, then `funext a; exact Subsingleton.elim _ _` (any two elements of `PUnit` are equal). The `comm` fields agree by proof irrelevance automatically after `congr`.

Acceptance for Part A: compiles; `#print axioms RelEx.Shadow.unit_final` shows nothing beyond the mathlib baseline; the doc-comment references T1a, D4, D5, D12; step 5's use of nonemptiness is present.

---

## 4. Part B — T1b: the Collapse Theorem, bisimulation form

### 4.1 Mathematical statement

Between any two *serial* transition systems (every state has at least one successor), the **total relation is a bisimulation**. Hence any state of any serial system is bisimilar to any state of any other: with nothing to observe, everything is identified. This is the elementary, category-free face of T1a and should be provable in under ~25 lines.

### 4.2 Definitions and theorems

```lean
namespace RelEx
namespace Shadow

/-- An unlabeled transition system with the seriality condition (every state steps).
Seriality is the relational face of D4's "emptiness unformulable". -/
structure TS where
  X : Type u
  step : X → Set X
  serial : ∀ x, (step x).Nonempty

/-- The standard (strong) bisimulation conditions for a relation between two systems. -/
def IsBisim (A B : TS) (R : A.X → B.X → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ a' ∈ A.step a, ∃ b' ∈ B.step b, R a' b') ∧
    (∀ b' ∈ B.step b, ∃ a' ∈ A.step a, R a' b')

/-- Spec 2.00, T1b. The total relation is a bisimulation between any two serial
systems: with no labels, no termination, and no quality, observation cannot
distinguish anything. -/
theorem total_isBisim (A B : TS) : IsBisim A B (fun _ _ => True) := by
  sorry

/-- Bisimilarity: relatedness by some bisimulation. -/
def Bisimilar (A B : TS) (a : A.X) (b : B.X) : Prop :=
  ∃ R, IsBisim A B R ∧ R a b

/-- Spec 2.00, T1b corollary. Every state is bisimilar to every state:
the many do not exist in the shadow. -/
theorem all_bisimilar (A B : TS) (a : A.X) (b : B.X) : Bisimilar A B a b := by
  sorry

end Shadow
end RelEx
```

Proof plan for `total_isBisim`: `intro a b _; constructor` then for the forth condition `intro a' _ha'`; use `B.serial b` to obtain `⟨b', hb'⟩`; provide `⟨b', hb', trivial⟩`. Back condition is symmetric using `A.serial a`. For `all_bisimilar`: `exact ⟨fun _ _ => True, total_isBisim A B, trivial⟩`.

**Doc-comment must note:** the proof visibly uses *only* seriality — read it and you can see exactly which axioms produce the collapse, which is the theorem's argumentative job.

---

## 5. Part C — the Arena interface and P0, P1s, P2, P3

### 5.1 What this section is (read before coding)

P0–P3 are propositions about the *graded* signature, whose full enriched form is open (spec O1). They are unblocked because they depend only on the **shape** of the signature — which is settled — not on the enriched machinery. So: define a minimal abstract interface (`Arena`) capturing exactly the settled shape, and prove the propositions **relative to the interface**. Spec 2.01 will later instantiate `Arena`; these theorems then apply to the instance automatically.

Be scrupulously honest in doc-comments about two things:
1. These are interface-relative results. Their content is fully discharged only when 2.01 provides the instance.
2. Several are one-liners *because the interface makes the negation unformulable*. That is a feature being demonstrated (D4's design pattern), not proof-padding. Say so.

### 5.2 The interface (write verbatim)

```lean
namespace RelEx

/-- Spec 2.00 §2.1–§2.4: the minimal settled shape of the graded signature.
Objects; for each object its restrictions (qualities ARE restrictions, D7) and its
aspects (its relating, abstractly); what a restriction witnesses; A8(i) properness;
directed observations indexed by observer and observed (P3 is enforced by this
indexing — an un-owned observation is unformulable); relatedness, symmetric,
entailing observation (D3: relating IS observation). -/
structure Arena where
  Obj : Type u
  Restriction : Obj → Type u
  Aspect : Obj → Type u
  witnesses : {x : Obj} → Restriction x → Set (Aspect x)
  /-- A8(i), lossiness: every restriction misses some aspect of its object.
  Uniform: no special rules for any restriction, including those used reflexively. -/
  proper : ∀ {x : Obj} (r : Restriction x), ∃ a : Aspect x, a ∉ witnesses r
  /-- Observations of `y` by `x`. The indexing over `Obj × Obj` IS proposition P3. -/
  Obs : Obj → Obj → Type u
  /-- The restriction of the OBSERVER through which an observation occurs (A8). -/
  via : {x y : Obj} → Obs x y → Restriction x
  Related : Obj → Obj → Prop
  related_symm : ∀ {x y}, Related x y → Related y x
  /-- D3/D4: relation entails observation at some (nonzero-by-unformulability) quality. -/
  obs_of_related : ∀ {x y}, Related x y → Nonempty (Obs x y)

namespace Arena
variable (A : Arena)
```

### 5.3 The propositions

```lean
/-- Spec 2.00, P0 (Pan-observation). Wherever relation exists, observation exists
in BOTH directions. Near-definitional under D3 — and that near-definitionality is
the content: the signature cannot express one-way or zero-quality relating. -/
theorem P0 {x y : A.Obj} (h : A.Related x y) :
    Nonempty (A.Obs x y) ∧ Nonempty (A.Obs y x) :=
  ⟨A.obs_of_related h, A.obs_of_related (A.related_symm h)⟩

/-- Spec 2.00, P1 in its self-observation form (P1s): no object is transparent to
itself — every self-observation misses some aspect. Direct instance of A8(i)'s
uniformity (D9: no special rules for the reflexive case). The general form of P1
(inexhaustibility to ANY observer) requires the 2.01 channel structure and is
deliberately NOT proved here. -/
theorem P1_self {x : A.Obj} (o : A.Obs x x) :
    ∃ a : A.Aspect x, a ∉ A.witnesses (A.via o) :=
  A.proper (A.via o)

/-- The observer of an observation (definitionally its first index). -/
def observerOf {x y : A.Obj} (_ : A.Obs x y) : A.Obj := x

/-- Spec 2.00, P2 (Asymmetry for free). For a relation between DISTINCT objects,
the two directions of observation are parts of different objects — they can never
be identical, because they are restrictions of different observers. No slots,
no ordered pairs needed (D6): direction exists only as observation. -/
theorem P2 {x y : A.Obj} (hxy : x ≠ y) (o₁ : A.Obs x y) (o₂ : A.Obs y x) :
    A.observerOf o₁ ≠ A.observerOf o₂ :=
  hxy

end Arena
end RelEx
```

Implementation notes:
- If `P0`/`P1_self`/`P2` really do close in one term as written, **leave them as term-mode one-liners**. Do not pad with tactics. The brevity is the exhibit.
- `P2` may need `by simpa [Arena.observerOf] using hxy` depending on reducibility; prefer the term proof, fall back to the tactic if needed.

### 5.4 P3 — deliverable is a definition plus documentation, not a theorem

P3 ("every observation has an observer and an observed, both objects; no free-floating relations exist") is enforced by the **type indexing** `Obs : Obj → Obj → Obj → ...` — wait, it is `Obs : Obj → Obj → Type u`: an observation *cannot be stated* without its observer and observed. There is no non-vacuous theorem to prove; the discharge is architectural. Deliverable:

```lean
/-- Spec 2.00, P3 (Co-requirement satisfied). There is no theorem here, and that is
the result: an observation without an observer and an observed is UNFORMULABLE in
this signature — `Obs` is indexed over `Obj × Obj`, so "free-floating relation" is
not a falsifiable claim but an ill-typed one. This is the same design pattern as
D4's unformulable emptiness. The relata objection (spec §0) is thereby satisfied
structurally: relations never lack relata, by construction.
This declaration exists to carry this documentation and to give the spec's P3 a
stable anchor in the formal development. -/
def P3_note : Unit := ()
```

(If you find a more idiomatic anchor — e.g., an `example` with a doc-comment — use it, but keep the name `P3` findable via the mapping table.)

---

## 6. Build, verify, deliver

### 6.1 Checklist (all MUST pass)

1. `lake build` succeeds with zero warnings you introduced (pre-existing warnings tolerated).
2. `grep -rn "sorry" formal/Spec200.lean` returns nothing.
3. For each of `unit_final`, `total_isBisim`, `all_bisimilar`, `Arena.P0`, `Arena.P1_self`, `Arena.P2`: run `#print axioms <name>` in a scratch section or the file's bottom; confirm nothing beyond `Classical.choice`, `propext`, `Quot.sound` (ideally the P-block and T1b are axiom-free — report what you see).
4. Every definition and theorem has a doc-comment with its spec ID.
5. T1a's proof uses the nonemptiness field (§3.3 step 5) — verify by inspection, not just compilation.

### 6.2 If something fails

- If a mathlib lemma name from this document doesn't resolve: find the equivalent with `exact?` / `apply?`, use it, and note the substitution in the mapping table.
- If a definition as written won't compile after 3 genuine attempts: adjust *minimally*, preserve the mathematical content exactly, and document the change. Do NOT change what is being proved. If the *statement* seems wrong, stop and report — do not "fix" statements.
- T1c (`SHOULD`, below) may be dropped if it exceeds ~1 hour of attempts; note the drop.

### 6.3 T1c (SHOULD, attempt after all MUSTs pass)

Statement: any final coalgebra of the shadow functor has a subsingleton carrier (the collapse is about *all* final coalgebras, not just `unit`). Sketch: define `Hom.comp` and `Hom.id`; given `Z` final, finality of `Z` yields `v : Hom unit Z`; the composite `Hom Z Z` through `unit` (using `unit_final`'s morphism `u : Hom Z unit`) must equal `Hom.id Z` by the uniqueness half of `IsFinal Z` applied to `Z` (both `v.comp u` and `id` are morphisms `Z → Z`); then every `z : Z.X` equals `v.f PUnit.unit`, so `Subsingleton Z.X`. Name it `final_subsingleton`.

### 6.4 Mapping table (append to the bottom of the Lean file as a comment)

```
-- Spec 2.00 ↔ formal/Spec200.lean
-- T1a  = RelEx.Shadow.unit_final
-- T1b  = RelEx.Shadow.total_isBisim, RelEx.Shadow.all_bisimilar
-- T1c  = RelEx.Shadow.final_subsingleton        (SHOULD; may be absent)
-- P0   = RelEx.Arena.P0
-- P1s  = RelEx.Arena.P1_self                    (general P1 deferred to 2.01)
-- P2   = RelEx.Arena.P2
-- P3   = RelEx.P3_note                          (architectural; see doc-comment)
-- Deviations from 2.00-mechanization.md: <list here, or "none">
```

---

## 7. Out of scope — do not attempt

- **T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, C1** — all blocked on the enriched setting (O1) or on T2. Do not define quantaloids, enriched categories, metrics, or any `Fintype`/cardinality machinery for these.
- **General P1** (inexhaustibility to arbitrary observers) — requires the 2.01 channel structure linking observer-restrictions to observed-aspects; proving it now would require inventing unsettled signature, which is exactly what D11's discipline forbids.
- **Any instance of `Arena`** — instantiation is 2.01's job; a toy instance would create a false impression of discharge.
- **mathlib's `CategoryTheory` framework** — hand-rolled structures only, per §2.
- **Refactoring anything outside `formal/Spec200.lean`.**

If, while working, a genuinely unblocked-looking lemma outside this list presents itself: note it in the PR description as a suggestion; do not prove it.

---

*End of work order. The theorems are small; the care is in the doc-comments and the honesty notes. What is being built is not just proofs but a legible argument — write the Lean file so that a philosopher with no Lean can still find T1, read its comment, and understand what was proved and why it matters.*
