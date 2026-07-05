/-
Spec 2.1 — mechanization of the two-sorted signature, enlargement, the C3 split, and L1.

Normative sources: `series-2/2-0.md` (ontology) and `series-2/2-1.md`
(signature and definitions). This file realizes the *two-sorted* signature of spec
2.1, the Arena's successor. `Spec200.lean` stays untouched and remains valid.

Deliverables (Spec 2.1, work order 2-1-mechanization.md §1):
  SIG       the two-sorted signature `Model` (+ raw coalgebras and homs)
  P4s       enlargement, static form      (RelEx.TwoSorted.P4_static)
  PRJa      external join totality        (RelEx.TwoSorted.PRJ_a)
  C3-split  the self-anchored case split  (RelEx.TwoSorted.SelfAnchored)
  C3-gen    generic-case properness       (RelEx.TwoSorted.generic_properness)
  C3-refl   reflexive-case saturation     (RelEx.TwoSorted.reflexive_saturation)
  L1-quot   coherence along surjections   (RelEx.TwoSorted.coherent_of_surjective_hom)
  L1-sub    coherence along injections     (RelEx.TwoSorted.coherent_of_injective_hom)
  L1-sum    coherence under coproducts     (RelEx.TwoSorted.coherent_sum)

Per Spec 2.0 D15 (pre-registration), the C3 case split is *defined first*, then the
generic theorem, then the reflexive counterexample. This order is normative; do not
reorder. The C3 pair locates exactly where A8(i) — the framework's only axiom — does
irreducible work: lossiness is derived everywhere except where the lens turns on itself.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Sym.Sym2

namespace RelEx
namespace TwoSorted

universe u

/-! ## Part A — the signature and interface-level results -/

/-- Spec 2.1 §2: the two-sorted signature, interface form. Two sorts (objects `O`,
relations `R`); unordered endpoints (no slots, 2.0 D6; `Sym2` permits diagonal
pairs, so self-relation A5 is representable); patterns as nonempty sets of
relations, with sharing as ordinary set membership (2.0 D3: one relation, two
containers, numerical identity for free); endpoint coherence as a field —
which IS proposition P3 and, as P4s will show, the co-requirement.
`dy` (dyad anchor) is taken as DATA at this interface: its construction from
`close` is P5 (spec 2.1 §3.1), deferred; no axioms govern it here, and results
below are interface-relative in the same sense as Spec200's Arena results. -/
structure Model where
  O : Type u
  R : Type u
  endpoints : R → Sym2 O
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty
  coherent : ∀ (r : R) (x : O), x ∈ endpoints r → r ∈ pat x
  dy : R → O

variable (M : Model)

/-- Spec 2.1 §3.2: the context of `r` in `x` — the relations in `x`'s pattern in
which `r`'s dyad participates. The aperture of `x` at `r` IS this set. -/
def ctx (x : M.O) (r : M.R) : Set M.R :=
  { s ∈ M.pat x | M.dy r ∈ M.endpoints s }

/-- `ctx x r` is a sub-pattern of `x`: a separation subset, so inclusion is
definitional. Aperture comparison is inclusion within one object only (2.0 A3).
(`ctx`/`SelfAnchored` are plain defs in `TwoSorted`, so they are applied as
`ctx M x r` rather than by dot notation; the names match the mapping table.) -/
theorem ctx_subset (x : M.O) (r : M.R) : ctx M x r ⊆ M.pat x :=
  fun _ hs => hs.1

/-- Spec 2.0 §2.3 / 2.1 §5, P4 (static form): to be observed is to be enlarged.
Any relation through which `y` is observed — any relation with `y` among its
endpoints — is a part of `y`. The proof is the coherence field applied: this
brevity is the exhibit, not padding. Observation constitutes the observed
because relations are parts of their endpoints BY SIGNATURE; the critic's
reading is a part of the art. Static form only: the coming-into-being of new
relations is Series 3 (2.0 O9). -/
theorem P4_static (r : M.R) (y : M.O) (hy : y ∈ M.endpoints r) : r ∈ M.pat y :=
  M.coherent r y hy

/-- Spec 2.0 §3, PR-J(a): at the representation layer, proper subsets can union
to the whole. Exists to make PR-J(b)'s contrast exact: EXTERNALLY, totality of
attention is cheap; the framework's question (PR-J(b), via C3 below) is whether
any DEPLOYABLE attention is ever total. Pre-registered pair per 2.0 D15. -/
theorem PRJ_a : ∃ A B : Set (Fin 2), A ⊂ Set.univ ∧ B ⊂ Set.univ ∧ A ∪ B = Set.univ := by
  refine ⟨{0}, {1}, ?_, ?_, ?_⟩
  · exact (Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr ⟨1, Set.mem_univ 1, by simp⟩
  · exact (Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr ⟨0, Set.mem_univ 0, by simp⟩
  · ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    revert x; decide

/-! ### The C3 split — ORDER OF DECLARATIONS IS NORMATIVE (2.0 D15)

The split is defined first, then the generic theorem, then the counterexample. -/

/-- Spec 2.1 §5 (C3): the case split. An attending of `x` along `r` is
SELF-ANCHORED when `r`'s own dyad is among `r`'s endpoints — the relation
participates in its own context; the lens appears in its own field of view.
This is the split on which the derivability of A8(i) turns, and per 2.0 D15
it is stated before any properness result in this file. -/
def SelfAnchored (r : M.R) : Prop := M.dy r ∈ M.endpoints r

/-- Spec 2.1 §5 (C3, generic case): OFF the self-anchored locus, properness is a
THEOREM — the aperture always omits the very relation being attended, because
that relation's dyad is not among its own endpoints. You cannot fully witness
the lens you are looking through. Consequences: PR-J(b) holds for generic
attendings, and A8(i)'s content is derived rather than assumed there. -/
theorem generic_properness (r : M.R) (x : M.O)
    (hr : r ∈ M.pat x) (h : ¬ SelfAnchored M r) :
    ctx M x r ⊂ M.pat x :=
  (Set.ssubset_iff_of_subset (ctx_subset M x r)).mpr ⟨r, hr, fun hmem => h hmem.2⟩

/-- Spec 2.1 §5 (C3, reflexive case): properness is NOT FORCED on the
self-anchored locus. Witness: the one-object, one-relation universe — the
self-loop, the framework's ω̂ — where the sole relation is its own dyad's
self-relation and the context of the attending saturates the entire pattern.

WHAT THIS SHOWS: the interface does not derive A8(i) at self-anchored
attendings; if lossiness holds there, it holds by AXIOM. A8(i)'s irreducible
content is located exactly at self-reference.
WHAT THIS DOES NOT SHOW: that A8(i) is false there. A richer signature (2.1's
full Ω, witnessing structure) may yet derive it, or refute it — either outcome
requires the machinery this file does not build. Per 2.0 D15, this comment is
the required hostile write-up: the project WANTS C3 true twice over (it would
shrink the last axiom and prove PR-J(b) at once), so the reflexive case is
reported at full strength, not softened. The saturating witness is exactly the
self-loop universe of T1 — the One is the place where attention can span
everything, and where lossiness must be legislated rather than derived. -/
theorem reflexive_saturation :
    ∃ (M : Model) (r : M.R) (x : M.O),
      SelfAnchored M r ∧ r ∈ M.pat x ∧ ctx M x r = M.pat x := by
  -- The self-loop universe: O = R = PUnit, the diagonal endpoint, whole-pattern.
  refine ⟨{ O := PUnit, R := PUnit,
            endpoints := fun _ => s(PUnit.unit, PUnit.unit),
            pat := fun _ => Set.univ,
            pat_nonempty := fun _ => ⟨PUnit.unit, trivial⟩,
            coherent := fun _ _ _ => Set.mem_univ _,
            dy := fun _ => PUnit.unit },
          PUnit.unit, PUnit.unit, ?_, ?_, ?_⟩
  · -- SelfAnchored: unit ∈ s(unit, unit)
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  · -- r ∈ pat x = univ
    exact Set.mem_univ _
  · -- ctx x r = pat x : the aperture saturates the whole (one-element) pattern
    refine Set.eq_univ_of_forall (fun s => ?_)
    exact ⟨Set.mem_univ s, Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-! ## Part B — L1: the covariety closures (spec 2.1 §4)

About **raw** two-sorted models, where coherence is a `Prop` (not a bundled field)
whose closure behaviour L1 establishes — this is what makes coherent coalgebras a
covariety, hence Ω = greatest coherent subcoalgebra of νF legitimate. -/

/-- A raw two-sorted model: as `Model` but with coherence NOT bundled —
coherence is the property whose closure behavior L1 establishes. -/
structure Raw where
  O : Type u
  R : Type u
  endpoints : R → Sym2 O
  pat : O → Set R
  pat_nonempty : ∀ x, (pat x).Nonempty

/-- Spec 2.1 §2/§4: endpoint coherence as a property of raw models. -/
def Coherent (A : Raw) : Prop :=
  ∀ (r : A.R) (x : A.O), x ∈ A.endpoints r → r ∈ A.pat x

/-- A homomorphism of raw models: sort maps commuting with endpoints (via
`Sym2.map`) and with patterns (via image — the powerset functor's action,
so equality, not mere inclusion). -/
structure Hom (A B : Raw) where
  fO : A.O → B.O
  fR : A.R → B.R
  end_comm : ∀ r, B.endpoints (fR r) = (A.endpoints r).map fO
  pat_comm : ∀ x, B.pat (fO x) = fR '' A.pat x

/-- Spec 2.1 §4, L1 (quotients): coherence is preserved along surjective homs.
One of the three closures making coherent coalgebras a covariety. Strengthening
recorded (see mapping table): only surjectivity of `fR` is used — the work order's
`hO : Surjective fO` hypothesis is unnecessary and has been dropped. -/
theorem coherent_of_surjective_hom {A B : Raw} (h : Hom A B)
    (hR : Function.Surjective h.fR) (hA : Coherent A) : Coherent B := by
  intro r' x' hx'
  obtain ⟨r, rfl⟩ := hR r'
  rw [h.end_comm r, Sym2.mem_map] at hx'
  obtain ⟨x, hx, rfl⟩ := hx'
  rw [h.pat_comm x]
  exact ⟨r, hA r x hx, rfl⟩

/-- Spec 2.1 §4, L1 (subcoalgebras): coherence is reflected along injective homs. -/
theorem coherent_of_injective_hom {A B : Raw} (h : Hom A B)
    (hR : Function.Injective h.fR) (hB : Coherent B) : Coherent A := by
  intro r x hx
  have hmap : h.fO x ∈ B.endpoints (h.fR r) := by
    rw [h.end_comm r, Sym2.mem_map]; exact ⟨x, hx, rfl⟩
  have hpat : h.fR r ∈ B.pat (h.fO x) := hB (h.fR r) (h.fO x) hmap
  rw [h.pat_comm x, Set.mem_image] at hpat
  obtain ⟨r', hr', hrr'⟩ := hpat
  rw [← hR hrr']
  exact hr'

/-- The binary coproduct of raw models: sorts sum, endpoints and patterns
transported along the injections. -/
def coprod (A B : Raw) : Raw where
  O := A.O ⊕ B.O
  R := A.R ⊕ B.R
  endpoints := Sum.elim (fun r => (A.endpoints r).map Sum.inl)
                        (fun r => (B.endpoints r).map Sum.inr)
  pat := Sum.elim (fun x => Sum.inl '' A.pat x) (fun x => Sum.inr '' B.pat x)
  pat_nonempty := by
    rintro (x | x)
    · obtain ⟨r, hr⟩ := A.pat_nonempty x; exact ⟨Sum.inl r, r, hr, rfl⟩
    · obtain ⟨r, hr⟩ := B.pat_nonempty x; exact ⟨Sum.inr r, r, hr, rfl⟩

/-- Spec 2.1 §4, L1 (sum, SHOULD): coherence is preserved under binary coproducts,
the third covariety closure. -/
theorem coherent_sum {A B : Raw} (hA : Coherent A) (hB : Coherent B) :
    Coherent (coprod A B) := by
  rintro (r | r) (x | x) hx
  · -- inl r, inl x : real case, use hA
    simp only [coprod, Sum.elim_inl, Sym2.mem_map, Sum.inl.injEq] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r, hA r a ha, rfl⟩
  · -- inl r, inr x : endpoints are all `inl _`, cannot contain `inr x`
    simp [coprod, Sym2.mem_map] at hx
  · -- inr r, inl x : symmetric impossible case
    simp [coprod, Sym2.mem_map] at hx
  · -- inr r, inr x : real case, use hB
    simp only [coprod, Sum.elim_inr, Sym2.mem_map, Sum.inr.injEq] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r, hB r a ha, rfl⟩

end TwoSorted
end RelEx

/-! ## Axiom audit (work order §6, item 2) -/
section AxiomAudit
open RelEx.TwoSorted
#print axioms P4_static
#print axioms PRJ_a
#print axioms generic_properness
#print axioms reflexive_saturation
#print axioms coherent_of_surjective_hom
#print axioms coherent_of_injective_hom
#print axioms coherent_sum
end AxiomAudit

/-
-- Specs 2.0 / 2.1 ↔ series-2/formal/Spec201.lean
-- P4 (static)        = RelEx.TwoSorted.P4_static
-- PR-J(a)            = RelEx.TwoSorted.PRJ_a
-- C3 split           = RelEx.TwoSorted.SelfAnchored (definition; order normative)
-- C3 (generic)       = RelEx.TwoSorted.generic_properness
-- C3 (reflexive)     = RelEx.TwoSorted.reflexive_saturation (counterexample)
-- L1 (quotient)      = RelEx.TwoSorted.coherent_of_surjective_hom
-- L1 (subcoalgebra)  = RelEx.TwoSorted.coherent_of_injective_hom
-- L1 (sum)           = RelEx.TwoSorted.coherent_sum
--
-- Deviations from 2-1-mechanization.md:
--   * File registered as a third Lake library root (`Spec201`) alongside
--     `Series2`/`Spec200`, in `lake/lakefile.toml` — same second-root precedent.
--   * `coherent_of_surjective_hom` drops the work order's `hO : Surjective fO`
--     hypothesis: only `hR : Surjective fR` is used, so the theorem is proved in
--     strengthened form (the work order §3.4 sanctions this and asks it be recorded).
-/
