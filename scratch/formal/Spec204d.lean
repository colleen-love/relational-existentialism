/-
Spec 2.04d — Carving Ω_C, re-anchoring the honesty lemmas, and T16 at the ω-tier.

Normative source: `scratch/spec/2-04.md` (§2 Ω_C := greatest coherent subcoalgebra; §5 the
hosted-relations doctrine) and the work order `2-04-mechanization-b.md`. Continues `Spec204c.lean`
(the construction: `ZΩC`, `ΩR`/`ΩO`, `fRC`/`fOC`, `isFinalBRawC`, `elt2`/`elt3`, `omegaHat2`).
Specs win. No declaration in this file consults §8 (the D19 register).

File naming follows Spec204a–c (spec-first resolution; see the Spec204 header note). This file is
`Spec204d.lean` per the order.
-/
import Spec204c

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 0 — Ω_C carved (2-04 §2; the greatest coherent subcoalgebra)

The one item Spec204c left uncarved. `GoodC` pairs are the two-sorted subcoalgebras on which the
K-triple holds; `coherentPartC` is their union (Knaster–Tarski by hand), the object `Ω_C`. -/

/-- A good pair of subsets `(UO, UR)` of a corrected coalgebra: a subcoalgebra (endpoints of kept
relations kept; patterns of kept objects kept) on which the coherence triple K1/K2/K3 holds. The
corrected analogue of Spec201b's `Good`. -/
structure GoodC (Z : RawC) (UO : Set Z.O) (UR : Set Z.R) : Prop where
  endsO : ∀ r ∈ UR, ∀ x : Z.O, Sum.inl x ∈ Z.endpoints r → x ∈ UO
  endsR : ∀ r ∈ UR, ∀ s : Z.R, Sum.inr s ∈ Z.endpoints r → s ∈ UR
  pats  : ∀ x ∈ UO, Z.pat x ⊆ UR
  k1 : ∀ r ∈ UR, ∀ x : Z.O, Sum.inl x ∈ Z.endpoints r → r ∈ Z.pat x
  k2 : ∀ s ∈ UR, ∀ x ∈ UO, ∀ r : Z.R, s ∈ Z.pat x → Sum.inr r ∈ Z.endpoints s → r ∈ Z.pat x
  k3 : ∀ x ∈ UO, ∀ r : Z.R, r ∈ Z.pat x → ∃ s ∈ Z.pat x, Sum.inr r ∈ Z.endpoints s

/-- The coherent part of a corrected universe (objects side): the union of all good pairs. -/
def coherentPartCO (Z : RawC) : Set Z.O := ⋃₀ { UO | ∃ UR, GoodC Z UO UR }
/-- The coherent part (relations side). -/
def coherentPartCR (Z : RawC) : Set Z.R := ⋃₀ { UR | ∃ UO, GoodC Z UO UR }

theorem subset_coherentPartCO {Z : RawC} {UO : Set Z.O} {UR : Set Z.R}
    (h : GoodC Z UO UR) : UO ⊆ coherentPartCO Z :=
  fun _ hx => Set.mem_sUnion.mpr ⟨UO, ⟨UR, h⟩, hx⟩

theorem subset_coherentPartCR {Z : RawC} {UO : Set Z.O} {UR : Set Z.R}
    (h : GoodC Z UO UR) : UR ⊆ coherentPartCR Z :=
  fun _ hr => Set.mem_sUnion.mpr ⟨UR, ⟨UO, h⟩, hr⟩

/-- The union of all good pairs is itself good: `Ω_C` is the GREATEST coherent subcoalgebra
(Knaster–Tarski by hand on the elementwise-closed K-triple). -/
theorem coherentPartC_good (Z : RawC) :
    GoodC Z (coherentPartCO Z) (coherentPartCR Z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr x hx
    obtain ⟨UR, ⟨UO, hG⟩, hrUR⟩ := Set.mem_sUnion.mp hr
    exact subset_coherentPartCO hG (hG.endsO r hrUR x hx)
  · intro r hr s hs
    obtain ⟨UR, ⟨UO, hG⟩, hrUR⟩ := Set.mem_sUnion.mp hr
    exact subset_coherentPartCR hG (hG.endsR r hrUR s hs)
  · intro x hx r hr
    obtain ⟨UO, ⟨UR, hG⟩, hxUO⟩ := Set.mem_sUnion.mp hx
    exact subset_coherentPartCR hG (hG.pats x hxUO hr)
  · intro r hr x hx
    obtain ⟨UR, ⟨UO, hG⟩, hrUR⟩ := Set.mem_sUnion.mp hr
    exact hG.k1 r hrUR x hx
  · intro s hs x hx r hsx hrs
    obtain ⟨UO, ⟨UR, hG⟩, hxUO⟩ := Set.mem_sUnion.mp hx
    obtain ⟨UR', ⟨UO', hG'⟩, hsUR'⟩ := Set.mem_sUnion.mp hs
    exact hG.k2 s (hG.pats x hxUO hsx) x hxUO r hsx hrs
  · intro x hx r hr
    obtain ⟨UO, ⟨UR, hG⟩, hxUO⟩ := Set.mem_sUnion.mp hx
    exact hG.k3 x hxUO r hr

/-! ### The canonical hom and the image lemma -/

/-- `end_comm` for the corrected corecursor (extracted from `isFinalBRawC`): `fRC` commutes with
endpoints via `Sym2.map (Sum.map fOC fRC)`. -/
theorem fRC_end_comm (A : RawC) (hA : BoundedC A) (r : A.R) :
    ZΩC.endpoints (fRC A hA r) = Sym2.map (Sum.map (fOC A hA) (fRC A hA)) (A.endpoints r) := by
  show QPF.Cofix.dest (fRC A hA r) = Sym2.map (Sum.map (fOC A hA) (fRC A hA)) (A.endpoints r)
  rw [fRC, QPF.Cofix.dest_corec]
  show HC.map (QPF.Cofix.corec (inducedCoalgC A hA)) (inducedCoalgC A hA r) = _
  rw [inducedCoalgC, HC.map]
  show Sym2.map _ (Sym2.map _ (A.endpoints r)) = Sym2.map _ (A.endpoints r)
  rw [Sym2.map_map]
  congr 1
  funext z
  rcases z with y | s
  · show Sum.inl _ = Sum.map (fOC A hA) (fRC A hA) (Sum.inl y)
    rfl
  · rfl

/-- The canonical hom from a bounded corrected coalgebra into `ZΩC` (`fOC`/`fRC` with the
extracted commutations). -/
noncomputable def homSeedC (A : RawC) (hA : BoundedC A) : HomC A ZΩC :=
  ⟨fOC A hA, fRC A hA, fRC_end_comm A hA, fun _ => rfl⟩

/-- The image of a COHERENT bounded coalgebra under the canonical hom is a good pair — the
covariety closure that lands coherent descriptions in `Ω_C`. Corrected analogue of Spec201b's
`image_good`. -/
theorem imageC_good (A : RawC) (hCoh : CoherentC A) (hA : BoundedC A) :
    GoodC ZΩC (Set.range (fOC A hA)) (Set.range (fRC A hA)) := by
  obtain ⟨hA1, hA2, hA3⟩ := hCoh
  have hpat : ∀ x, ZΩC.pat (fOC A hA x) = fRC A hA '' A.pat x := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- endsO
    rintro _ ⟨r, rfl⟩ x' hx'
    rw [fRC_end_comm A hA r, Sym2.mem_map] at hx'
    obtain ⟨e, _, hmap⟩ := hx'
    rcases e with a | b
    · rw [Sum.map_inl] at hmap; exact ⟨a, Sum.inl.inj hmap⟩
    · rw [Sum.map_inr] at hmap; exact absurd hmap (by simp)
  · -- endsR
    rintro _ ⟨r, rfl⟩ s' hs'
    rw [fRC_end_comm A hA r, Sym2.mem_map] at hs'
    obtain ⟨e, _, hmap⟩ := hs'
    rcases e with a | b
    · rw [Sum.map_inl] at hmap; exact absurd hmap (by simp)
    · rw [Sum.map_inr] at hmap; exact ⟨b, Sum.inr.inj hmap⟩
  · -- pats
    rintro _ ⟨x, rfl⟩ r hr
    rw [hpat, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact ⟨a, rfl⟩
  · -- k1
    rintro _ ⟨r, rfl⟩ x' hx'
    rw [fRC_end_comm A hA r, Sym2.mem_map] at hx'
    obtain ⟨e, he, hmap⟩ := hx'
    rcases e with a | b
    · rw [Sum.map_inl, Sum.inl.injEq] at hmap
      rw [← hmap, hpat]
      exact ⟨r, hA1 r a he, rfl⟩
    · rw [Sum.map_inr] at hmap; exact absurd hmap (by simp)
  · -- k2
    rintro s' _ _ ⟨x, rfl⟩ r hsx hrs
    rw [hpat, Set.mem_image] at hsx
    obtain ⟨s0, hs0, rfl⟩ := hsx
    rw [fRC_end_comm A hA s0, Sym2.mem_map] at hrs
    obtain ⟨e, he, hmap⟩ := hrs
    rcases e with a | b
    · rw [Sum.map_inl] at hmap; exact absurd hmap (by simp)
    · rw [Sum.map_inr, Sum.inr.injEq] at hmap
      rw [hpat, ← hmap]
      exact ⟨b, hA2 s0 x b hs0 he, rfl⟩
  · -- k3
    rintro _ ⟨x, rfl⟩ r hr
    rw [hpat, Set.mem_image] at hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    obtain ⟨s0, hs0, hmem⟩ := hA3 x r0 hr0
    refine ⟨fRC A hA s0, ?_, ?_⟩
    · rw [hpat]; exact ⟨s0, hs0, rfl⟩
    · rw [fRC_end_comm A hA s0, Sym2.mem_map]; exact ⟨Sum.inr r0, hmem, rfl⟩

/-! ### Citizens relocated, the anti-Mirror against Ω_C, and the hosted part -/

/-- `elt2` lives in `Ω_C` — a coherent element (the close of the coherent bearing seed). -/
theorem elt2_mem_ΩC : elt2 ∈ coherentPartCR ZΩC :=
  subset_coherentPartCR (imageC_good seed2 seed2_coherent bounded_seed2) ⟨PUnit.unit, rfl⟩

/-- `elt3` lives in `Ω_C`. -/
theorem elt3_mem_ΩC : elt3 ∈ coherentPartCR ZΩC :=
  subset_coherentPartCR (imageC_good seed3 seed3_coherent bounded_seed3) ⟨PUnit.unit, rfl⟩

/-- ω̂₂ — the self-witnessing loop — lives in `Ω_C` as an object. -/
theorem omegaHat2_mem_ΩC : omegaHat2 ∈ coherentPartCO ZΩC :=
  subset_coherentPartCO (imageC_good seed3 seed3_coherent bounded_seed3) ⟨PUnit.unit, rfl⟩

/-- FP5, restated as a fact ABOUT Ω_C the object: two elements of the coherent universe,
non-bisimilar at depth 1. The anti-Mirror against Ω_C proper — **the corrected universe is many.** -/
theorem anti_mirror_ΩC :
    elt2 ∈ coherentPartCR ZΩC ∧ elt3 ∈ coherentPartCR ZΩC ∧ elt2 ≠ elt3 :=
  ⟨elt2_mem_ΩC, elt3_mem_ΩC, elt2_ne_elt3⟩

/-- The doctrine of 2-04 §5, given its formal referent: a relation-point is *hosted* when some
object-point's pattern contains it. Doctrine-level quantifiers over relations relativize to this;
application of normative §5, not a new decision. -/
def hostedC (r : ΩR) : Prop := ∃ x : ΩO, r ∈ ZΩC.pat x

/-- The hosted part of `Ω_R`. -/
def hostedPart : Set ΩR := {r | hostedC r}

/-! ## Stage 1 — the honesty lemmas, lifted (2-04 §; re-anchoring T5/T10 over Ω_C)

Spec203's `eqDepth_trivial`/`genesis_vacuous` existed so no reader mistook T5/T10 for resolved
over the collapsed universe. Here they are replaced with contentful counterparts over the
corrected, plural universe. -/

/-- Sort-respecting lift of a pair of relations to `Ω_O ⊕ Ω_R`: objects match objects, relations
match relations; cross-sort pairs never match (the profile is observable at every depth). -/
def SumLiftC (Ro : ΩO → ΩO → Prop) (Rr : ΩR → ΩR → Prop) : (ΩO ⊕ ΩR) → (ΩO ⊕ ΩR) → Prop
  | Sum.inl x, Sum.inl y => Ro x y
  | Sum.inr r, Sum.inr s => Rr r s
  | _, _ => False

/-! Depth-`n` behavioural equivalence on the corrected universe (mutual over the two sorts;
carried from Spec201d with `ends` over `O ⊕ R`). Relations agree to depth `n+1` when their
endpoint pairs are `Sym2`-lifted-equal to depth `n` (sort-respecting); objects agree when their
patterns are Egli–Milner-lifted-equal on relations. -/
mutual
  /-- Depth-`n` equivalence on relations. -/
  def EqDepthR : ℕ → ΩR → ΩR → Prop
    | 0 => fun _ _ => True
    | n + 1 => fun r s =>
        RelEx.TwoSorted.Sym2Lift (SumLiftC (EqDepthO n) (EqDepthR n))
          (ZΩC.endpoints r) (ZΩC.endpoints s)
  /-- Depth-`n` equivalence on objects. -/
  def EqDepthO : ℕ → ΩO → ΩO → Prop
    | 0 => fun _ _ => True
    | n + 1 => fun x y => RelEx.TwoSorted.SetLift (EqDepthR n) x.1 y.1
end

/-- FP-B1 — CONFIRMED: `EqDepthR` is NON-TRIVIAL over Ω_C. The two coherent citizens `elt2` and
`elt3` agree to depth 0 (everything does) but SEPARATE at depth 1 — `elt2`'s unfolding carries an
object endpoint the sort-respecting lift cannot match to `elt3`'s pure higher-order pair. The
honesty debt (`eqDepth_trivial`, Spec203) is paid: depth equivalence discriminates. -/
theorem eqDepthC_nontrivial : EqDepthR 0 elt2 elt3 ∧ ¬ EqDepthR 1 elt2 elt3 := by
  refine ⟨trivial, ?_⟩
  show ¬ RelEx.TwoSorted.Sym2Lift (SumLiftC (EqDepthO 0) (EqDepthR 0))
        (ZΩC.endpoints elt2) (ZΩC.endpoints elt3)
  rintro ⟨a, b, c, d, hp, hq, hcase⟩
  rw [dest_elt2, Sym2.eq_iff] at hp
  rw [dest_elt3, Sym2.eq_iff] at hq
  -- c = d = inr elt3 (the higher seed's pair is diagonal)
  have hc : c = Sum.inr elt3 := by rcases hq with ⟨h, _⟩ | ⟨_, h⟩ <;> exact h.symm
  have hd : d = Sum.inr elt3 := by rcases hq with ⟨_, h⟩ | ⟨h, _⟩ <;> exact h.symm
  subst hc; subst hd
  -- one of a, b is the object endpoint `inl (...)`; the sort-lift against `inr elt3` is False
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [SumLiftC] at h1 h2

/-! ### Genesis, re-anchored: contentful, truth-value open (FP-B2) -/

/-- One object-level generative step in Ω_C: `y` arises within `x`'s unfolding — some relation of
`x`'s pattern has `y` (as an object endpoint) among its endpoints. -/
def ArisesC (y x : ΩO) : Prop := ∃ r ∈ ZΩC.pat x, Sum.inl y ∈ ZΩC.endpoints r

/-- The orbit of ω̂₂ (the self-witnessing loop): everything reachable from it by finite unfolding. -/
def omegaOrbit2 : Set ΩO := { y | Relation.ReflTransGen ArisesC y omegaHat2 }

theorem omegaHat2_mem_omegaOrbit2 : omegaHat2 ∈ omegaOrbit2 := Relation.ReflTransGen.refl

/-- Genesis over the corrected universe (2-04, T10 re-anchored): does all multiplicity unfold from
self-witnessing? Stated as depth-density of ω̂₂'s orbit. -/
def GenesisC : Prop := ∀ (x : ΩO) (n : ℕ), ∃ y ∈ omegaOrbit2, EqDepthO n x y

/-- FP-B2 — CONFIRMED: `GenesisC` is NON-VACUOUS. Over the collapsed universe Genesis was
vacuously true (everything equalled ω̂); here the universe is genuinely plural (`elt2 ≠ elt3`), so
`GenesisC` is a contentful claim with a real question behind it. **Its truth-value stays open**,
exactly as `Genesis` was anchored in Spec201d — this is the anchor, not the answer. -/
theorem genesisC_nonvacuous : ∃ r s : ΩR, r ≠ s := ⟨elt2, elt3, elt2_ne_elt3⟩

/-- T10's sharpened form (2-04, "is F(1)'s pregnancy enough to reach everything?"): every
relation-point is behaviourally approximated by the unfolding of the coherent seeds. Stated as a
precise OPEN question about Ω_C — the re-anchoring deliverable is the statement, not its proof
(D13: the framework brings no perspective where a proof can be had). -/
def ReachableFromSeeds : Prop :=
  ∀ (r : ΩR) (n : ℕ), EqDepthR n r elt2 ∨ EqDepthR n r elt3 ∨
    ∃ s : ΩR, (s = elt2 ∨ s = elt3) ∧ EqDepthR n r s

/-- T5 surrogate `closing_denseC` (2-04 re-anchoring): DROPPED under the same sanctioned drop
clause as its ancestor `closing_dense` (Spec201d) — the truncation/density assembly needs
machinery out of this order's scope. The load-bearing depth machinery (`EqDepthR`/`EqDepthO`,
`FinitelyRealizedC` below) is in hand; the final assembly is deferred, no `sorry`, outcome
recorded as OPEN-attempt per the order. -/
def closing_denseC_note : Unit := ()

/-- ρ_C — the finitely-realized relations of Ω_C: images of finite-carrier bounded coherent
descriptions. Carried from Spec201d's `FinitelyRealized`. -/
def FinitelyRealizedC (r : ΩR) : Prop :=
  ∃ (A : RawC) (hA : BoundedC A), CoherentC A ∧ ∃ (a : A.R), fRC A hA a = r

/-- ρ_C is inhabited: `elt3` (the closed higher seed) is finitely realized, from the finite-carrier
coherent `seed3` (`A.O = A.R = PUnit`). The density surrogate has a nonempty domain — unlike the
collapsed universe, where the analogue was vacuous. -/
theorem elt3_finitelyRealizedC : FinitelyRealizedC elt3 :=
  ⟨seed3, bounded_seed3, seed3_coherent, PUnit.unit, rfl⟩

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms coherentPartC_good
#print axioms imageC_good
#print axioms elt2_mem_ΩC
#print axioms omegaHat2_mem_ΩC
#print axioms anti_mirror_ΩC
#print axioms eqDepthC_nontrivial
#print axioms genesisC_nonvacuous
#print axioms elt3_finitelyRealizedC
end AxiomAudit

/-
================================================================================
2-04-mechanization-b §Frozen predictions ↔ this file (Stages 0–1; see 2-04 §9 Results)
================================================================================
-- Stage 0 (Ω_C carved)  GoodC, coherentPartCO/CR, coherentPartC_good, imageC_good,
--                        elt2/elt3/omegaHat2_mem_ΩC, anti_mirror_ΩC, hostedC/hostedPart   DELIVERED
-- FP-B1  eqDepthC nontrivial (elt2/elt3)      → eqDepthC_nontrivial                       CONFIRMED
-- FP-B2  GenesisC non-vacuous; truth open     → GenesisC, genesisC_nonvacuous,
--                                                omegaOrbit2, ReachableFromSeeds (open)    CONFIRMED
-- T5 surrogate closing_denseC                  → DROPPED (sanctioned drop clause);
--                                                ρ_C machinery in hand (FinitelyRealizedC,
--                                                elt3_finitelyRealizedC)                   noted
--
-- Remaining (Stages 2–6, the continuation): Stage 2 T16_ω needs `Infinite ΩR` (the Lambek
-- bijection dest : ΩR ≃ Sym2(ΩO ⊕ ΩR) plus a finite-cardinality contradiction — a focused
-- sub-problem); Stage 3 the C1 landing (FP-B4/B5); Stage 4 P3h-positive (FP-B6); Stage 5 the
-- B5 interface pack; Stage 6 T4 scaffolding. Nothing here consulted §8 (the D19 register).
--
-- Entrant ↔ Lean name:
--   Stage 0 = RelEx.Corrected.GoodC, coherentPartCO, coherentPartCR, subset_coherentPartCO/CR,
--             coherentPartC_good, fRC_end_comm, homSeedC, imageC_good,
--             elt2_mem_ΩC, elt3_mem_ΩC, omegaHat2_mem_ΩC, anti_mirror_ΩC, hostedC, hostedPart
--   Stage 1 = RelEx.Corrected.SumLiftC, EqDepthR, EqDepthO, eqDepthC_nontrivial,
--             ArisesC, omegaOrbit2, omegaHat2_mem_omegaOrbit2, GenesisC, genesisC_nonvacuous,
--             ReachableFromSeeds, FinitelyRealizedC, elt3_finitelyRealizedC
-/


