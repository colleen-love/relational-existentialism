/-
Spec 2.0 — mechanization of the unblocked theorem group (T1, P0–P3).

Normative source: `series-2/2-0.md` (Spec 2.0). This file mechanizes exactly
the theorem group that Spec 2.0 §5 marks as *unblocked* — provable now, independent
of all open machinery (the enriched/quantaloid setting of O1 is NOT needed):

  T1a  The Collapse Theorem, final-coalgebra form   (RelEx.Shadow.unit_final)
  T1b  The Collapse Theorem, bisimulation form       (RelEx.Shadow.total_isBisim,
                                                        RelEx.Shadow.all_bisimilar)
  T1c  Corollary: every final shadow-coalgebra has subsingleton carrier
                                                      (RelEx.Shadow.final_subsingleton)
  P0   Pan-observation                                (RelEx.Arena.P0)
  P1s  No transparency to self                        (RelEx.Arena.P1_self)
  P2   Asymmetry for free                             (RelEx.Arena.P2)
  P3   Co-requirement satisfied (architectural)       (RelEx.P3_note)

Category-theory machinery is hand-rolled deliberately (Spec 2.0 §2 treats the
category theory as tooling, not ontology); no `Mathlib.CategoryTheory.*` is imported.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image

namespace RelEx

/-! ## Part A/B — T1: the Collapse Theorem (boolean shadow) -/

namespace Shadow

universe u
variable {X Y : Type u}

/-- Spec 2.0, §2.3 "boolean shadow" / D4. The quality-forgetting unfolding functor:
an unfolding is a nonempty unordered set of successors. Nonemptiness is enforced by
the subtype (emptiness is *unformulable*, not forbidden — the D4 design pattern:
subtracting quality, an entity's unfolding is still a nonempty set of entities). -/
def F (X : Type u) : Type u := { S : Set X // S.Nonempty }

/-- Functorial action of `F` on functions (image on the underlying set). Mathematically
the map that carries `F` from a raw type-former to a functor; philosophically, describing
one universe in terms of another transports its patterns of relating along the map. -/
def mapF (h : X → Y) (s : F X) : F Y :=
  ⟨h '' s.1, s.2.image h⟩

/-- A coalgebra of `F`: a carrier with an unfolding map. Spec 2.0: a "description"
(D2, §2.1) — a way of specifying a pattern of relating, cheap and plentiful. -/
structure Coalg where
  X : Type u
  c : X → F X

/-- A coalgebra morphism: a carrier map commuting with unfolding. Mathematically a
structure-preserving translation; philosophically, a re-description that respects how
each point unfolds into its successors. -/
structure Hom (A B : Coalg) where
  f : A.X → B.X
  comm : ∀ a, B.c (f a) = mapF f (A.c a)

/-- Finality: every coalgebra admits exactly one morphism in. Mathematically the
universal property of a terminal object; philosophically, the closure operator A2
requires — a description specifies exactly one object. -/
def IsFinal (Z : Coalg) : Prop :=
  ∀ A : Coalg, ∃! _h : Hom A Z, True

/-- The one-point coalgebra: the single self-relating point (the spec's ω̂ in the
shadow). Its unfolding is the whole (one-element) universe: it relates to itself. -/
def unit : Coalg :=
  ⟨PUnit, fun _ => ⟨Set.univ, ⟨PUnit.unit, trivial⟩⟩⟩

/-- Spec 2.0, T1a (Collapse / The One). The one-point coalgebra is final for the
boolean-shadow functor: with quality forgotten, the entire universe is a single
self-relating point. "Not bang, but becoming" (D5); non-rigging evidence (D12) — fed
the quality-free axioms, the closure machinery outputs exactly one object. The crux
(existence, below) uses the nonemptiness field `(A.c a).2`: with possibly-empty
unfoldings the theorem is FALSE, which is the whole point of T1 (D4). -/
theorem unit_final : IsFinal Shadow.unit := by
  intro A
  refine ⟨⟨fun _ => PUnit.unit, ?comm⟩, trivial, ?uniq⟩
  case comm =>
    -- Commuting square: `unit.c ⋆ = mapF (fun _ => ⋆) (A.c a)`, i.e.
    -- `Set.univ = (fun _ => ⋆) '' (A.c a).1`.
    intro a
    apply Subtype.ext
    show Set.univ = (fun _ => PUnit.unit) '' (A.c a).1
    refine (Set.eq_univ_iff_forall.mpr ?_).symm
    intro p
    -- THE CRUX: seriality/nonemptiness is used here and only here.
    obtain ⟨x, hx⟩ := (A.c a).2
    exact ⟨x, hx, Subsingleton.elim _ _⟩
  case uniq =>
    -- Any two morphisms into `unit` agree: their carrier maps land in `PUnit`
    -- (subsingleton), and `comm` is a `Prop` (proof irrelevance).
    rintro ⟨f₁, c₁⟩ -
    have hf : f₁ = fun _ => PUnit.unit :=
      funext fun _ => Subsingleton.elim (α := PUnit) _ _
    subst hf
    rfl

/-- An unlabeled transition system with the seriality condition (every state steps).
Seriality is the relational face of D4's "emptiness unformulable": no state is a
dead end, just as no object relates to nothing. -/
structure TS where
  X : Type u
  step : X → Set X
  serial : ∀ x, (step x).Nonempty

/-- The standard (strong) bisimulation conditions for a relation between two systems:
matching moves forth and back. Mathematically the coalgebraic notion of behavioural
equivalence; philosophically, "these two are indistinguishable by observation." -/
def IsBisim (A B : TS) (R : A.X → B.X → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ a' ∈ A.step a, ∃ b' ∈ B.step b, R a' b') ∧
    (∀ b' ∈ B.step b, ∃ a' ∈ A.step a, R a' b')

/-- Spec 2.0, T1b. The total relation is a bisimulation between any two serial
systems: with no labels, no termination, and no quality, observation cannot
distinguish anything. The proof visibly uses *only* seriality (`A.serial`, `B.serial`)
— read it and you see exactly which axiom produces the collapse, which is the
theorem's argumentative job (the demonstration that quality is constitutive). -/
theorem total_isBisim (A B : TS) : IsBisim A B (fun _ _ => True) := by
  intro a b _
  refine ⟨?forth, ?back⟩
  case forth =>
    intro a' _
    obtain ⟨b', hb'⟩ := B.serial b
    exact ⟨b', hb', trivial⟩
  case back =>
    intro b' _
    obtain ⟨a', ha'⟩ := A.serial a
    exact ⟨a', ha', trivial⟩

/-- Bisimilarity: relatedness by some bisimulation. -/
def Bisimilar (A B : TS) (a : A.X) (b : B.X) : Prop :=
  ∃ R, IsBisim A B R ∧ R a b

/-- Spec 2.0, T1b corollary. Every state is bisimilar to every state: the many do
not exist in the shadow. Immediate from `total_isBisim`. -/
theorem all_bisimilar (A B : TS) (a : A.X) (b : B.X) : Bisimilar A B a b :=
  ⟨fun _ _ => True, total_isBisim A B, trivial⟩

/-! ### T1c (SHOULD) — every final shadow-coalgebra collapses -/

/-- Identity morphism of a coalgebra. -/
def Hom.id (A : Coalg) : Hom A A :=
  ⟨fun x => x, fun a => by apply Subtype.ext; simp [mapF, Set.image_id']⟩

/-- Composition of coalgebra morphisms. -/
def Hom.comp {A B C : Coalg} (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨fun a => g.f (f.f a), fun a => by
    show C.c (g.f (f.f a)) = mapF (fun a => g.f (f.f a)) (A.c a)
    rw [g.comm (f.f a), f.comm a]
    apply Subtype.ext
    simp [mapF, Set.image_image]⟩

/-- Spec 2.0, T1c. The collapse is about *all* final coalgebras, not just `unit`:
any final coalgebra of the shadow functor has a subsingleton carrier. Mathematically,
finality pins the carrier down to a single point (final objects are unique up to iso,
and `unit` is one); philosophically, in the quality-free shadow every terminal universe
is the same single self-relating point — there is nothing for a second point to be. -/
theorem final_subsingleton (Z : Coalg) (hZ : IsFinal Z) : Subsingleton Z.X := by
  obtain ⟨u, -, -⟩ := unit_final Z          -- u : Hom Z unit
  obtain ⟨v, -, -⟩ := hZ Shadow.unit         -- v : Hom unit Z
  obtain ⟨_, -, huniq⟩ := hZ Z               -- uniqueness of Z → Z
  have h1 : v.comp u = Hom.id Z :=
    (huniq _ trivial).trans (huniq _ trivial).symm
  refine ⟨fun x y => ?_⟩
  have hx : (v.comp u).f x = x := by rw [h1]; rfl
  have hy : (v.comp u).f y = y := by rw [h1]; rfl
  -- `u.f x, u.f y : unit.X` are both `PUnit`, hence equal.
  have hu : u.f x = u.f y := Subsingleton.elim (α := PUnit) _ _
  calc x = (v.comp u).f x := hx.symm
    _ = v.f (u.f x) := rfl
    _ = v.f (u.f y) := by rw [hu]
    _ = (v.comp u).f y := rfl
    _ = y := hy

end Shadow

/-! ## Part C — the Arena interface and P0, P1s, P2, P3

P0–P3 are propositions about the *graded* signature, whose full enriched form is open
(Spec 2.0, O1). They are unblocked because they depend only on the settled *shape* of
the signature, not on the enriched machinery. So: define a minimal abstract interface
(`Arena`) capturing exactly the settled shape, and prove the propositions *relative to
the interface*. Spec 2.1 will instantiate `Arena`; these theorems then apply to the
instance automatically. Two honest flags carried in the doc-comments below:
(1) these are interface-relative results — fully discharged only when 2.1 provides the
instance; (2) several are one-liners *because the interface makes the negation
unformulable* — that is D4's design pattern being demonstrated, not proof-padding. -/

/-- Spec 2.0 §2.1–§2.4: the minimal settled shape of the graded signature.
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

/-- Spec 2.0, P0 (Pan-observation). Wherever relation exists, observation exists
in BOTH directions. Near-definitional under D3 — and that near-definitionality is
the content: the signature cannot express one-way or zero-quality relating (D4). -/
theorem P0 {x y : A.Obj} (h : A.Related x y) :
    Nonempty (A.Obs x y) ∧ Nonempty (A.Obs y x) :=
  ⟨A.obs_of_related h, A.obs_of_related (A.related_symm h)⟩

/-- Spec 2.0, P1 in its self-observation form (P1s): no object is transparent to
itself — every self-observation misses some aspect. Direct instance of A8(i)'s
uniformity (D9: no special rules for the reflexive case). The general form of P1
(inexhaustibility to ANY observer) requires the 2.1 channel structure and is
deliberately NOT proved here (Spec 2.0 §7 out-of-scope; P1 general deferred to 2.1). -/
theorem P1_self {x : A.Obj} (o : A.Obs x x) :
    ∃ a : A.Aspect x, a ∉ A.witnesses (A.via o) :=
  A.proper (A.via o)

/-- The observer of an observation (definitionally its first index). -/
def observerOf {x y : A.Obj} (_ : A.Obs x y) : A.Obj := x

/-- Spec 2.0, P2 (Asymmetry for free). For a relation between DISTINCT objects,
the two directions of observation are parts of different objects — they can never
be identical, because they are restrictions of different observers. No slots,
no ordered pairs needed (D6): direction exists only as observation. -/
theorem P2 {x y : A.Obj} (hxy : x ≠ y) (o₁ : A.Obs x y) (o₂ : A.Obs y x) :
    A.observerOf o₁ ≠ A.observerOf o₂ :=
  hxy

end Arena

/-- Spec 2.0, P3 (Co-requirement satisfied). There is no theorem here, and that is
the result: an observation without an observer and an observed is UNFORMULABLE in
this signature — `Obs` is indexed over `Obj × Obj`, so "free-floating relation" is
not a falsifiable claim but an ill-typed one. This is the same design pattern as
D4's unformulable emptiness. The relata objection (spec §0) is thereby satisfied
structurally: relations never lack relata, by construction.

This declaration exists to carry this documentation and to give the spec's P3 a
stable anchor in the formal development. -/
def P3_note : Unit := ()

end RelEx

/-! ## Axiom audit (Spec 2.0 §6.1, item 3)

`#print axioms` on each mechanized result. Acceptance: nothing beyond the mathlib
baseline `Classical.choice`, `propext`, `Quot.sound`. -/
section AxiomAudit
open RelEx RelEx.Shadow RelEx.Arena
#print axioms unit_final
#print axioms total_isBisim
#print axioms all_bisimilar
#print axioms final_subsingleton
#print axioms P0
#print axioms P1_self
#print axioms P2
end AxiomAudit

/-
-- Spec 2.0 ↔ series-2/formal/Spec20a.lean
-- T1a  = RelEx.Shadow.unit_final
-- T1b  = RelEx.Shadow.total_isBisim, RelEx.Shadow.all_bisimilar
-- T1c  = RelEx.Shadow.final_subsingleton        (SHOULD; present)
-- P0   = RelEx.Arena.P0
-- P1s  = RelEx.Arena.P1_self                    (general P1 deferred to 2.1)
-- P2   = RelEx.Arena.P2
-- P3   = RelEx.P3_note                          (architectural; see doc-comment)
--
-- Deviations from 2.0-mechanization.md:
--   * File lives at `series-2/formal/Spec20a.lean`, not `formal/Spec20a.lean`.
--     Reason: after the handoff-XVIII rename the repo's `/formal/` is a gitignored
--     stale build home; the live Lean source root is `series-2/formal` (Lake library
--     `Series2`, per `lake/lakefile.toml`). Placing the file under `/formal/` would
--     leave it uncommitted. Mathematical content is unchanged.
--   * `Set.Nonempty.image` is used as `s.2.image h` exactly as the work order wrote
--     it (dot notation fills the `Nonempty` hypothesis slot; `h` is the function).
-/
