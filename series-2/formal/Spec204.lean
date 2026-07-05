/-
Spec 2.4a — The Corrected Functor: F_C, the coherence triple, and the coherent census.

Normative source: `series-2/2-4.md` (the corrected-functor design: §0 D20, §1 D22 the bare
(C) signature, §2 D23 the coherence triple, §7 the frozen FP predictions) and the work order
`series-2/2-4-mechanization-a.md`. Specs win; discrepancies reported below.

NAMING DISCREPANCY (reported, resolved spec-first). The work order names its target
`Spec205.lean` and cites "2.5 §0/§2/§6" and appends results to "2.5" — but the normative spec
is `2-4.md` (its §0/§2/§6/§7 are exactly what the order cites), and the file-naming convention
is spec `2-0N` → `Spec20N` (2.3 → `Spec203`/`Spec203b`/`Spec203c`). The "2.5"/`Spec205`
references are a systematic off-by-one slip. Per "specs win," this file is `Spec204.lean` and all
citations are to `2-4.md`. The `2.5` open-question labels the spec itself uses (O-2-5-2/3/5)
are left as the spec wrote them — they name a *future* re-anchoring doc, not this one.

SCOPE OF THIS FILE (the "start"). Hostile-first ordering is mandatory (order §3). This file
delivers the head of the order in that order: **Stage 0** (D20 in-file: F_C, FP1a/b/c, the
coherent census) and **Stage 1** (the signature, the K-triple, FP2 = L1-C ×3 per clause, the
holding lemma). Stages 2–7 (the genuinely-mutual MvQPF construction of νF_C/Ω_C, the anti-Mirror
against Ω_C proper, the residue attack, the B3/B5 pack, P3h) are the next chunk and are NOT in
this file; the construction (Stage 2) carries its own sanctioned drop clause and is a multi-
session effort. Nothing here consults 2.4 §8 (the D19 register); FP4's hostile framing is the
only permitted contact and it lives downstream.

Builds on `Spec203c` (transitively the whole chain), reusing `RelEx.Trials.RawC` — which *is*
the corrected raw signature (`pat : O → Set R`, `ends : R → Sym2 (O ⊕ R)`) — and the `Sym2`/
`PfNe` idioms.
-/
import Spec203c

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 0 — D20 discharged in-file (2.4 §0; nothing precedes this)

The corrected functor `F_C`: `F_O(O,R) = P⁺f(R)`, `F_R(O,R) = Sym2(O ⊕ R)`. -/

/-- `F_C` object component: nonempty finite patterns of relations (the `P⁺f` idiom, = `PfNe`). -/
abbrev FO (_O R : Type) : Type := PfNe R

/-- `F_C` relation component: an unordered endpoint pair drawn from either sort. -/
abbrev FR (O R : Type) : Type := Sym2 (O ⊕ R)

/-- FP1a (object side over the point) — the object component is forced: `F_O(1,1) = P⁺f({r̂})`
is a single point. As for every candidate, the object side was never where plurality lives
(2.4 §0). Inhabited by the whole pattern. -/
theorem FP1a_subsingleton : Subsingleton (FO PUnit PUnit) :=
  inferInstanceAs (Subsingleton (PfNe PUnit))

/-- FP1a companion — the object component over the point is inhabited (nonempty finite `{r̂}`). -/
def FP1a_inhabited : FO PUnit PUnit :=
  (⟨{PUnit.unit}, Set.finite_singleton _, Set.singleton_nonempty _⟩ : PfNe PUnit)

/-! ### FP1b — the relation side over the point is exactly three (2.4 §0)

`F_R(1,1) = Sym2({⋆} ⊕ {r̂})` has three elements: the self-relation `s(⋆,⋆)`, the bearing
`s(⋆,r̂)`, and the turning-upon-its-turning `s(r̂,r̂)`. Sort-composition of endpoints is the
individuating resource — relational self-reference, the only escape the Forcing Lemma left open.

The order prefers a `≃ Fin 3`; the `Fintype` instance for `Sym2 (PUnit ⊕ PUnit)` does not
resolve at the ambiguous universe of bare `PUnit`, so we ship the sanctioned drop clause: the
three named elements, pairwise `≠`, plus an exhaustion lemma. This pins "exactly three" and
names the three seeds for the census. -/

/-- The self-relation seed `s(⋆,⋆)`: both endpoints the object. -/
def seedOO : FR PUnit PUnit := s(Sum.inl PUnit.unit, Sum.inl PUnit.unit)
/-- The bearing seed `s(⋆,r̂)`: one object endpoint, one relation endpoint. -/
def seedOR : FR PUnit PUnit := s(Sum.inl PUnit.unit, Sum.inr PUnit.unit)
/-- The higher seed `s(r̂,r̂)`: both endpoints the relation — turning upon its own turning. -/
def seedRR : FR PUnit PUnit := s(Sum.inr PUnit.unit, Sum.inr PUnit.unit)

/-- FP1b (exhaustion) — the relation component over the point has no fourth element. -/
theorem FR_point_exhaustive (z : FR PUnit PUnit) :
    z = seedOO ∨ z = seedOR ∨ z = seedRR := by
  induction z using Sym2.ind with
  | _ a b =>
    rcases a with a | a <;> rcases b with b | b
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact Or.inr (Or.inr rfl)

/-- FP1b (distinctness 1/3): the self-relation and the bearing differ (the bearing carries an
`inr` endpoint the self-relation lacks). -/
theorem seedOO_ne_seedOR : seedOO ≠ seedOR := by
  simp [seedOO, seedOR, Sym2.eq_iff]

/-- FP1b (distinctness 2/3): the self-relation and the higher seed differ. -/
theorem seedOO_ne_seedRR : seedOO ≠ seedRR := by
  simp [seedOO, seedRR, Sym2.eq_iff]

/-- FP1b (distinctness 3/3): the bearing and the higher seed differ (the bearing carries an
object endpoint the higher seed lacks). -/
theorem seedOR_ne_seedRR : seedOR ≠ seedRR := by
  simp [seedOR, seedRR, Sym2.eq_iff]

/-! ## Stage 1 predicates, pulled forward for the census (2.4 §2, D23 the coherence triple)

K1 endpoint coherence; K2 downward closure (relation-endpoints only); K3 context-nonemptiness.
Stated here (order §0 permits pulling Stage 1 predicates forward) so the census can read K3. -/

/-- K1 — endpoint coherence (2.4 §2), carried verbatim from the two-sorted signature: if an
object `x` is an endpoint of `r`, then `r` is part of `x`. Uniform over O–O and O–R ties. -/
def K1 (A : RawC) : Prop :=
  ∀ (r : A.R) (x : A.O), Sum.inl x ∈ A.endpoints r → r ∈ A.pat x

/-- K2 — downward closure (2.4 §2): if `s` is part of `x` and a *relation* `r` is an endpoint
of `s`, then `r` is part of `x`. Relation-endpoints only — object endpoints are never pulled
inward (A2: the far relata are reached through relations, never contained). -/
def K2 (A : RawC) : Prop :=
  ∀ (s : A.R) (x : A.O) (r : A.R), s ∈ A.pat x → Sum.inr r ∈ A.endpoints s → r ∈ A.pat x

/-- K3 — context-nonemptiness (2.4 §2; the old OPEN, now imposed as structure): every held
relation is borne upon within the holder. This makes the bare unwitnessed turn *unformulable*
(the D4 pattern) — the census (§0) shows the pure self-loop is thereby incoherent. -/
def K3 (A : RawC) : Prop :=
  ∀ (x : A.O) (r : A.R), r ∈ A.pat x → ∃ s ∈ A.pat x, Sum.inr r ∈ A.endpoints s

/-- The coherence triple (2.4 §2, D23). A coherent coalgebra of the corrected functor. -/
def CoherentC (A : RawC) : Prop := K1 A ∧ K2 A ∧ K3 A

/-! ### FP1c — the coherent census (2.4 §0)

The three one-point coalgebras. Under the triple the bare self-relation (seed 1) is incoherent
(K3 fails: its context is empty), and the coherent one-point universes are exactly two (the
mixed seed and the higher seed), non-bisimilar at depth 1 by sort-profile. **The One cannot
merely turn; it must turn upon its turning** (2.4 §0). -/

/-- Seed 1 — the bare self-relation, unwitnessed: `ends(r̂) = s(⋆,⋆)`. -/
def seed1 : RawC where
  O := PUnit
  R := PUnit
  endpoints := fun _ => seedOO
  pat := fun _ => {PUnit.unit}
  pat_nonempty := fun _ => ⟨PUnit.unit, rfl⟩

/-- Seed 2 — the mixed/bearing seed: `ends(r̂) = s(⋆,r̂)`. -/
def seed2 : RawC where
  O := PUnit
  R := PUnit
  endpoints := fun _ => seedOR
  pat := fun _ => {PUnit.unit}
  pat_nonempty := fun _ => ⟨PUnit.unit, rfl⟩

/-- Seed 3 — the higher seed: `ends(r̂) = s(r̂,r̂)`, the turning attending its own turning. -/
def seed3 : RawC where
  O := PUnit
  R := PUnit
  endpoints := fun _ => seedRR
  pat := fun _ => {PUnit.unit}
  pat_nonempty := fun _ => ⟨PUnit.unit, rfl⟩

/-- FP1c — seed 1 is INCOHERENT: K3 fails on the bare self-relation. Its context is empty — the
sole relation `r̂` is never borne upon (`s(⋆,⋆)` has no relation endpoint), so the unwitnessed
turn is unformulable (2.4 §0, the D4 pattern). The One cannot merely turn. -/
theorem seed1_incoherent : ¬ CoherentC seed1 := by
  rintro ⟨_, _, hK3⟩
  obtain ⟨s, _, hmem⟩ := hK3 PUnit.unit PUnit.unit rfl
  rw [show seed1.endpoints s = seedOO from rfl, seedOO, Sym2.mem_iff] at hmem
  rcases hmem with h | h <;> simp at h

/-- FP1c — seed 2 (the bearing seed) is COHERENT. -/
theorem seed2_coherent : CoherentC seed2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- K1
    rintro r x _; exact rfl
  · -- K2
    rintro s x r _ _; exact rfl
  · -- K3: r̂ is borne upon by r̂ itself (inr r̂ ∈ s(⋆,r̂))
    rintro x r _
    exact ⟨PUnit.unit, rfl, Sym2.mem_iff.mpr (Or.inr rfl)⟩

/-- FP1c — seed 3 (the higher seed) is COHERENT. -/
theorem seed3_coherent : CoherentC seed3 := by
  refine ⟨?_, ?_, ?_⟩
  · -- K1: vacuous — s(r̂,r̂) has no object endpoint
    rintro r x hx
    rw [show seed3.endpoints r = seedRR from rfl, seedRR, Sym2.mem_iff] at hx
    rcases hx with h | h <;> simp at h
  · -- K2
    rintro s x r _ _; exact rfl
  · -- K3
    rintro x r _
    exact ⟨PUnit.unit, rfl, Sym2.mem_iff.mpr (Or.inr rfl)⟩

/-- The depth-1 object invariant separating the coherent seeds: `x` hosts a relation with an
object endpoint (a first-order bearing). The sort-profile at depth 1 (Spec203b B2-C technique). -/
def ObjHasFirstOrder (A : RawC) (x : A.O) : Prop :=
  ∃ r ∈ A.pat x, ∃ y : A.O, Sum.inl y ∈ A.endpoints r

/-- FP1c — the two coherent seeds are NOT bisimilar at depth 1: seed 2's object hosts a
first-order bearing (`s(⋆,r̂)` has the object endpoint `⋆`), seed 3's does not (`s(r̂,r̂)` is pure
higher-order). The anti-Mirror in miniature, on the coherent part — the collapse criterion fails
even there (2.4 §0). -/
theorem seeds_not_bisimilar :
    ObjHasFirstOrder seed2 PUnit.unit ∧ ¬ ObjHasFirstOrder seed3 PUnit.unit := by
  constructor
  · exact ⟨PUnit.unit, rfl, PUnit.unit, Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · rintro ⟨r, _, y, hy⟩
    rw [show seed3.endpoints r = seedRR from rfl, seedRR, Sym2.mem_iff] at hy
    rcases hy with h | h <;> simp at h

/-! ## Stage 1 — homomorphisms, L1-C (the covariety closures), and the holding lemma (2.4 §2)

The K-triple must be a coequation so the covariety/transfer machinery of 2.1 §4 applies verbatim
(2.4 §2). FP2 = each clause closed under surjective homs, injective homs, and coproducts. -/

/-- A homomorphism of corrected raw coalgebras: sort maps commuting with `ends` (via
`Sym2.map (Sum.map fO fR)` — both sorts now transported) and with `pat` (via image). -/
structure HomC (A B : RawC) where
  fO : A.O → B.O
  fR : A.R → B.R
  end_comm : ∀ r, B.endpoints (fR r) = (A.endpoints r).map (Sum.map fO fR)
  pat_comm : ∀ x, B.pat (fO x) = fR '' A.pat x

/-- FP2 (quotients) — the coherence triple is preserved along surjective homs, proved per clause
(a failure would isolate the failing clause; none does). -/
theorem coherentC_of_surjective_hom {A B : RawC} (h : HomC A B)
    (hO : Function.Surjective h.fO) (hR : Function.Surjective h.fR)
    (hA : CoherentC A) : CoherentC B := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · -- K1
    intro r' x' hx'
    obtain ⟨r, rfl⟩ := hR r'
    obtain ⟨x, rfl⟩ := hO x'
    rw [h.end_comm r, Sym2.mem_map] at hx'
    obtain ⟨e, he, hmap⟩ := hx'
    rcases e with a | b
    · rw [Sum.map_inl, Sum.inl.injEq] at hmap
      rw [← hmap, h.pat_comm a]
      exact ⟨r, hA1 r a he, rfl⟩
    · rw [Sum.map_inr] at hmap; exact absurd hmap (by simp)
  · -- K2
    intro s' x' r' hs' hr'
    obtain ⟨x, rfl⟩ := hO x'
    rw [h.pat_comm x] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    rw [h.end_comm s, Sym2.mem_map] at hr'
    obtain ⟨e, he, hmap⟩ := hr'
    rcases e with a | b
    · rw [Sum.map_inl] at hmap; exact absurd hmap (by simp)
    · rw [Sum.map_inr, Sum.inr.injEq] at hmap
      rw [← hmap, h.pat_comm x]
      exact ⟨b, hA2 s x b hs he, rfl⟩
  · -- K3
    intro x' r' hr'
    obtain ⟨x, rfl⟩ := hO x'
    rw [h.pat_comm x] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    obtain ⟨s, hs, hmem⟩ := hA3 x r hr
    refine ⟨h.fR s, ?_, ?_⟩
    · rw [h.pat_comm x]; exact ⟨s, hs, rfl⟩
    · rw [h.end_comm s, Sym2.mem_map]; exact ⟨Sum.inr r, hmem, rfl⟩

/-- FP2 (subcoalgebras) — the coherence triple is reflected along injective homs, per clause. -/
theorem coherentC_of_injective_hom {A B : RawC} (h : HomC A B)
    (hR : Function.Injective h.fR) (hB : CoherentC B) : CoherentC A := by
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · -- K1
    intro r x hx
    have hmap : Sum.inl (h.fO x) ∈ B.endpoints (h.fR r) := by
      rw [h.end_comm r, Sym2.mem_map]; exact ⟨Sum.inl x, hx, rfl⟩
    have hpat := hB1 (h.fR r) (h.fO x) hmap
    rw [h.pat_comm x, Set.mem_image] at hpat
    obtain ⟨r'', hr'', hEq⟩ := hpat
    rw [← hR hEq]; exact hr''
  · -- K2
    intro s x r hs hr
    have hsB : h.fR s ∈ B.pat (h.fO x) := by rw [h.pat_comm x]; exact ⟨s, hs, rfl⟩
    have hrB : Sum.inr (h.fR r) ∈ B.endpoints (h.fR s) := by
      rw [h.end_comm s, Sym2.mem_map]; exact ⟨Sum.inr r, hr, rfl⟩
    have hpat := hB2 (h.fR s) (h.fO x) (h.fR r) hsB hrB
    rw [h.pat_comm x, Set.mem_image] at hpat
    obtain ⟨r'', hr'', hEq⟩ := hpat
    rw [← hR hEq]; exact hr''
  · -- K3
    intro x r hr
    have hrB : h.fR r ∈ B.pat (h.fO x) := by rw [h.pat_comm x]; exact ⟨r, hr, rfl⟩
    obtain ⟨s', hs', hmem⟩ := hB3 (h.fO x) (h.fR r) hrB
    rw [h.pat_comm x, Set.mem_image] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    rw [h.end_comm s, Sym2.mem_map] at hmem
    obtain ⟨e, he, hmap⟩ := hmem
    rcases e with a | b
    · rw [Sum.map_inl] at hmap; exact absurd hmap (by simp)
    · rw [Sum.map_inr, Sum.inr.injEq] at hmap
      rw [hR hmap] at he
      exact ⟨s, hs, he⟩

/-- The binary coproduct of corrected raw coalgebras: sorts sum; endpoints and patterns
transported along the injections (endpoints via `Sum.map` on each sort). -/
def coprodC (A B : RawC) : RawC where
  O := A.O ⊕ B.O
  R := A.R ⊕ B.R
  endpoints := Sum.elim
    (fun r => (A.endpoints r).map (Sum.map Sum.inl Sum.inl))
    (fun r => (B.endpoints r).map (Sum.map Sum.inr Sum.inr))
  pat := Sum.elim (fun x => Sum.inl '' A.pat x) (fun x => Sum.inr '' B.pat x)
  pat_nonempty := by
    rintro (x | x)
    · obtain ⟨r, hr⟩ := A.pat_nonempty x; exact ⟨Sum.inl r, r, hr, rfl⟩
    · obtain ⟨r, hr⟩ := B.pat_nonempty x; exact ⟨Sum.inr r, r, hr, rfl⟩

/-- FP2 (coproducts) — the coherence triple is preserved under binary coproducts, per clause.
The third covariety closure; with the two above, coherent corrected coalgebras form a covariety
and the 2.1 §4 transfer machinery applies verbatim (2.4 §2). -/
theorem coherentC_sum {A B : RawC} (hA : CoherentC A) (hB : CoherentC B) :
    CoherentC (coprodC A B) := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · -- K1
    rintro (r | r) (x | x) hx
    · -- inl r, inl x : real, use hA1. Object endpoint of an A-relation is `inl (inl a)`.
      simp only [coprodC, Sum.elim_inl, Sym2.mem_map] at hx
      obtain ⟨e, he, hmap⟩ := hx
      rcases e with a | c
      · simp only [Sum.map_inl, Sum.inl.injEq] at hmap
        simp only [coprodC, Sum.elim_inl, Set.mem_image]
        exact ⟨r, hmap ▸ hA1 r a he, rfl⟩
      · simp only [Sum.map_inr] at hmap; exact absurd hmap (by simp)
    · -- inl r, inr x : an A-relation carries no `inl (inr _)` object endpoint
      simp only [coprodC, Sum.elim_inl, Sym2.mem_map] at hx
      obtain ⟨e, _, hmap⟩ := hx
      rcases e with a | c <;> simp [Sum.map] at hmap
    · -- inr r, inl x : symmetric impossible case
      simp only [coprodC, Sum.elim_inr, Sym2.mem_map] at hx
      obtain ⟨e, _, hmap⟩ := hx
      rcases e with c | a <;> simp [Sum.map] at hmap
    · -- inr r, inr x : real, use hB1. Object endpoint of a B-relation is `inl (inr b)`.
      simp only [coprodC, Sum.elim_inr, Sym2.mem_map] at hx
      obtain ⟨e, he, hmap⟩ := hx
      rcases e with c | a
      · simp only [Sum.map_inl, Sum.inl.injEq, Sum.inr.injEq] at hmap
        simp only [coprodC, Sum.elim_inr, Set.mem_image]
        exact ⟨r, hmap ▸ hB1 r c he, rfl⟩
      · simp only [Sum.map_inr] at hmap; exact absurd hmap (by simp)
  · -- K2
    rintro (s | s) (x | x) (r | r) hs hr
    · -- inl s, inl x, inl r : real, use hA2
      simp only [coprodC, Sum.elim_inl, Set.mem_image] at hs
      obtain ⟨s0, hs0, hEq⟩ := hs
      have hss : s0 = s := by simpa using hEq
      rw [hss] at hs0
      simp only [coprodC, Sum.elim_inl, Sym2.mem_map] at hr
      obtain ⟨e, he, hmap⟩ := hr
      rcases e with a | c
      · simp only [Sum.map_inl] at hmap; exact absurd hmap (by simp)
      · simp only [Sum.map_inr, Sum.inr.injEq, Sum.inl.injEq] at hmap
        rw [hmap] at he
        simp only [coprodC, Sum.elim_inl, Set.mem_image]
        exact ⟨r, hA2 s x r hs0 he, rfl⟩
    · -- inl s, inl x, inr r : an A-relation has no `inr (inr _)` relation endpoint
      simp only [coprodC, Sum.elim_inl, Sym2.mem_map] at hr
      obtain ⟨e, _, hmap⟩ := hr
      rcases e with a | c <;> simp [Sum.map] at hmap
    · exact absurd hs (by simp [coprodC])
    · exact absurd hs (by simp [coprodC])
    · exact absurd hs (by simp [coprodC])
    · exact absurd hs (by simp [coprodC])
    · -- inr s, inr x, inl r : a B-relation has no `inr (inl _)` relation endpoint
      simp only [coprodC, Sum.elim_inr, Sym2.mem_map] at hr
      obtain ⟨e, _, hmap⟩ := hr
      rcases e with c | a <;> simp [Sum.map] at hmap
    · -- inr s, inr x, inr r : real, use hB2
      simp only [coprodC, Sum.elim_inr, Set.mem_image] at hs
      obtain ⟨s0, hs0, hEq⟩ := hs
      have hss : s0 = s := by simpa using hEq
      rw [hss] at hs0
      simp only [coprodC, Sum.elim_inr, Sym2.mem_map] at hr
      obtain ⟨e, he, hmap⟩ := hr
      rcases e with c | a
      · simp only [Sum.map_inl] at hmap; exact absurd hmap (by simp)
      · simp only [Sum.map_inr, Sum.inr.injEq] at hmap
        rw [hmap] at he
        simp only [coprodC, Sum.elim_inr, Set.mem_image]
        exact ⟨r, hB2 s x r hs0 he, rfl⟩
  · -- K3
    rintro (x | x) (r | r) hr
    · simp only [coprodC, Sum.elim_inl, Set.mem_image] at hr
      obtain ⟨r0, hr0, hEq⟩ := hr
      have hrr : r0 = r := by simpa using hEq
      rw [hrr] at hr0
      obtain ⟨s, hs, hmem⟩ := hA3 x r hr0
      refine ⟨Sum.inl s, ?_, ?_⟩
      · simp only [coprodC, Sum.elim_inl, Set.mem_image]; exact ⟨s, hs, rfl⟩
      · simp only [coprodC, Sum.elim_inl, Sym2.mem_map]; exact ⟨Sum.inr r, hmem, rfl⟩
    · exact absurd hr (by simp [coprodC])
    · exact absurd hr (by simp [coprodC])
    · simp only [coprodC, Sum.elim_inr, Set.mem_image] at hr
      obtain ⟨r0, hr0, hEq⟩ := hr
      have hrr : r0 = r := by simpa using hEq
      rw [hrr] at hr0
      obtain ⟨s, hs, hmem⟩ := hB3 x r hr0
      refine ⟨Sum.inr s, ?_, ?_⟩
      · simp only [coprodC, Sum.elim_inr, Set.mem_image]; exact ⟨s, hs, rfl⟩
      · simp only [coprodC, Sum.elim_inr, Sym2.mem_map]; exact ⟨Sum.inr r, hmem, rfl⟩

/-- The holding lemma — **"to bear is to hold"** (2.4 §2). K1 and K2 compose on a mixed tie: if
`s` has an object endpoint `y` and a relation endpoint `r`, then K1 forces `s ∈ pat(y)` and then
K2 forces `r ∈ pat(y)`. If my mother bears on my partnership, my partnership-relation becomes a
part of her pattern — the shared-joint surplus of 2.0 §2.5, the per-act mechanism behind
containers-co-attend. (Stated in strengthened form: hosting the tie in some third pattern is not
required — K1 supplies `s ∈ pat(y)` from the endpoint alone.) -/
theorem holding_lemma (A : RawC) (hK1 : K1 A) (hK2 : K2 A)
    (y : A.O) (s r : A.R)
    (hy : Sum.inl y ∈ A.endpoints s) (hr : Sum.inr r ∈ A.endpoints s) :
    r ∈ A.pat y :=
  hK2 s y r (hK1 s y hy) hr

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms FP1a_subsingleton
#print axioms FR_point_exhaustive
#print axioms seedOO_ne_seedOR
#print axioms seedOO_ne_seedRR
#print axioms seedOR_ne_seedRR
#print axioms seed1_incoherent
#print axioms seed2_coherent
#print axioms seed3_coherent
#print axioms seeds_not_bisimilar
#print axioms coherentC_of_surjective_hom
#print axioms coherentC_of_injective_hom
#print axioms coherentC_sum
#print axioms holding_lemma
end AxiomAudit

/-
================================================================================
2.4 §7 FP predictions ↔ this file (Stages 0–1; see 2.4 §9 Results for the transcript)
================================================================================
-- FP1a  FO PUnit PUnit subsingleton + inhabited   → FP1a_subsingleton, FP1a_inhabited  CONFIRMED
-- FP1b  FR PUnit PUnit = 3 (exhaustion + ≠×3)      → FR_point_exhaustive, seed*_ne_*     CONFIRMED
-- FP1c  coherent census = 2; seeds non-bisimilar   → seed1_incoherent, seed2/3_coherent,
--                                                     seeds_not_bisimilar                CONFIRMED
-- FP2   L1-C ×3, per clause                         → coherentC_of_surjective_hom,
--                                                     coherentC_of_injective_hom,
--                                                     coherentC_sum                      CONFIRMED
-- (holding lemma "to bear is to hold")              → holding_lemma                      DELIVERED
--
-- Naming: file = Spec204.lean (spec is 2-4.md; the order's "Spec205"/"2.5" §0/§2/§6 are an
--   off-by-one slip, resolved spec-first — see the header note).
-- Stages 2–7 (νF_C/Ω_C construction, anti-Mirror on Ω_C proper, residue attack, B3/B5, P3h) are
--   the next order-chunk and are NOT in this file. Stage 2's MvQPF mutual construction carries a
--   sanctioned drop clause and is a multi-session effort; FP4/FP5/FP6/FP3/FP7 live downstream.
--
-- Entrant ↔ Lean name:
--   Stage 0 = RelEx.Corrected.FO, FR, FP1a_subsingleton, FP1a_inhabited, seedOO/OR/RR,
--             FR_point_exhaustive, seedOO_ne_seedOR, seedOO_ne_seedRR, seedOR_ne_seedRR,
--             seed1/2/3, seed1_incoherent, seed2_coherent, seed3_coherent,
--             ObjHasFirstOrder, seeds_not_bisimilar
--   Stage 1 = RelEx.Corrected.K1, K2, K3, CoherentC, HomC, coprodC,
--             coherentC_of_surjective_hom, coherentC_of_injective_hom, coherentC_sum,
--             holding_lemma
-/
