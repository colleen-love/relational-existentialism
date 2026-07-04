/-
Spec 2.04b — Continuation of 2-04-mechanization-a: the univariate reduction (Stage 2),
the ascent against F_C (Stage 4, FP6), the residue attack + witness (Stage 5, FP4), the
B3/B5 recovery pack (Stage 6, FP7), and P3h (Stage 7, FP3).

Normative source: `scratch/spec/2-04.md` §3 (D24 recovery pack), §4 (construction), §5 (P3h),
§6 (B5/witness), §7 (FP table). Continues `Spec204.lean` (Stages 0–1). Specs win.

Hostile-first note (marked deviation, sanctioned by 2-04-mechanization-a §3). Stages 2–3 — the
genuinely-mutual construction of νF_C/Ω_C — are the order's hardest piece and carry an explicit
drop clause. This file delivers the construction-INDEPENDENT content of Stages 4–7 (which the
order itself frames as "interface-plus-witness," §3/§6) and records the Stage-2 univariate
reduction concretely, while the νF_C QPF construction (and hence FP5 against Ω_C *proper*) is the
documented remaining boundary — see the results write-up (2-04 §9). Nothing here consults §8.
-/
import Spec204

open RelEx.Trials (RawC)

namespace RelEx.Corrected

/-! ## Stage 2 (reduction) — the mutual functor collapses to one univariate fixpoint (2-04 §4)

The corrected terminal coalgebra satisfies `Ω_O ≅ P⁺f(Ω_R)` and `Ω_R ≅ Sym2(Ω_O ⊕ Ω_R)`.
Substituting the first into the second eliminates the mutual recursion:
`Ω_R ≅ Sym2(P⁺f(Ω_R) ⊕ Ω_R) = HC Ω_R`, and then `Ω_O := P⁺f(Ω_R)`. So the whole construction
rests on a SINGLE univariate fixpoint `νHC`. `HC` is recorded here as a genuine functor; building
its QPF instance (the analogue of Spec201c's `instQPFG`, but for this richer shape) and taking
`QPF.Cofix HC` is the remaining heavy step (2-04 §4, Stage 2's sanctioned drop clause). -/

/-- `HC` — the univariate reduction functor: `HC X = Sym2(P⁺f(X) ⊕ X)`, whose greatest fixpoint
is the relation sort `Ω_R` of the corrected universe. -/
def HC (X : Type) : Type := Sym2 (RelEx.Trials.PfNe X ⊕ X)

/-- Functorial action of `HC`: `Sym2.map` over the sum of the finite-powerset image and the
identity. -/
def HC.map {α β : Type} (f : α → β) : HC α → HC β :=
  Sym2.map (Sum.map
    (fun S => (⟨f '' S.1, S.2.1.image _, S.2.2.image _⟩ : RelEx.Trials.PfNe β)) f)

instance : Functor HC := { map := fun f => HC.map f }

/-- `HC` preserves identity — the first functor law, witnessing `HC` is a genuine functor (so
`νHC` exists once its QPF is built). -/
theorem HC_map_id {α : Type} : HC.map (id : α → α) = id := by
  funext z
  induction z using Sym2.ind with
  | _ a b =>
    simp only [HC.map, Sym2.map_pair_eq, id_eq]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Sum.map, Set.image_id, Subtype.ext_iff]

/-! ## Stage 4 (FP6) — the ascent re-verified against F_C exactly, proxy replaced (2-04 §0/§7)

The trial proxy (Spec203c `ascent_R`/`ascent_O`) ran over `PfNe`/`Sym2 ∘ ⊕`, which is `F_C`
verbatim: `FO O R = PfNe R`, `FR O R = Sym2 (O ⊕ R)` are defeq to the stage bodies. The
stage-wise non-collapse therefore holds *against F_C proper*, restated here through `FO`/`FR`. -/

/-- FP6 (relation sort) — CONFIRMED: the `F_C` relation component never re-collapses at any stage
of the terminal sequence. `FR (OStage n) (RStage n)` is `RStage (n+1)` (defeq), so Spec203c's
`ascent_R` transfers verbatim — the Mirror's collapse fails at every storey, against F_C proper. -/
theorem ascentC_R (n : ℕ) :
    ¬ Subsingleton (FR (RelEx.Trials.OStage n) (RelEx.Trials.RStage n)) :=
  RelEx.Trials.ascent_R n

/-- FP6 (object sort) — CONFIRMED: the `F_C` object component never re-collapses from stage 2 on.
`FO (OStage (n+1)) (RStage (n+1))` is `OStage (n+2)` (defeq); Spec203c's `ascent_O` transfers. -/
theorem ascentC_O (n : ℕ) :
    ¬ Subsingleton (FO (RelEx.Trials.OStage (n+1)) (RelEx.Trials.RStage (n+1))) :=
  RelEx.Trials.ascent_O n

/-! ## Stage 5 (FP4) — the residue, attacked; the R-C3 split (2-04 §3, §7)

The context of `r` at host `x`, direct (higher-order in content, no dyads): the pattern-members
that bear on `r`. The C3 split restates as: is `ctxC x r` proper in `pat x`? -/

/-- Direction/context of `r` at host `x` (2-04 §3, D24): the relations in `x`'s pattern that bear
on `r`. First-order in the signature, higher-order in content, no dyads. -/
def ctxC (A : RawC) (x : A.O) (r : A.R) : Set A.R :=
  {s | s ∈ A.pat x ∧ Sum.inr r ∈ A.endpoints s}

theorem ctxC_subset (A : RawC) (x : A.O) (r : A.R) : ctxC A x r ⊆ A.pat x :=
  fun _ h => h.1

/-- Self-anchored at the corrected signature: `r` bears on itself (`inr r` among its own
endpoints) — the genuine self-referential locus, now a locus in the functor rather than a dyad
artifact (2-04 §3). -/
def SelfAnchoredC (A : RawC) (r : A.R) : Prop := Sum.inr r ∈ A.endpoints r

/-- R-C3 (generic case) — CONFIRMS FP4's generic half: OFF the self-anchored locus, properness is
a THEOREM. The aperture omits the very relation attended, because that relation does not bear on
itself. -/
theorem genericC_properness (A : RawC) (x : A.O) (r : A.R)
    (hr : r ∈ A.pat x) (h : ¬ SelfAnchoredC A r) :
    ctxC A x r ⊂ A.pat x :=
  (Set.ssubset_iff_of_subset (ctxC_subset A x r)).mpr ⟨r, hr, fun hmem => h hmem.2⟩

/-- R-C3 (self-anchored case) — CONFIRMS FP4's headline: properness is NOT derivable at
self-anchored loops. The witness is the **coherent higher seed** (`seed3`, `ends(r̂) = s(r̂,r̂)`):
a coherent one-point universe in which the sole relation bears on itself and the context saturates
the entire pattern (`ctxC = pat`). The attack — attempting to *derive* properness at loops in the
ontology — is thereby obstructed by an actual coherent model, exactly at `s(r̂,r̂)`, the turning
attending its own turning.

WHAT THIS SHOWS (interface-plus-witness, same status as `reflexive_saturation` before it): from
the corrected interface and the K-triple, A8(i)'s lossiness at self-reference is NOT derivable —
the residue survives against this material. WHAT IT DOES NOT SHOW: that it is underivable in full
`Ω_C` (that question stays open honestly, 2-04 O-2-05-2, pending the construction). The saturation
now sits on a *coherent* seed — unlike the pre-correction witness, which lived in the collapsed
exclusion zone — so the residue's address has sharpened to the coherent point-universe of pure
self-witnessing. -/
theorem saturationC :
    ∃ (A : RawC) (r : A.R) (x : A.O),
      CoherentC A ∧ SelfAnchoredC A r ∧ r ∈ A.pat x ∧ ctxC A x r = A.pat x := by
  refine ⟨seed3, PUnit.unit, PUnit.unit, seed3_coherent, ?_, rfl, ?_⟩
  · show Sum.inr PUnit.unit ∈ seed3.endpoints PUnit.unit
    rw [show seed3.endpoints PUnit.unit = seedRR from rfl, seedRR]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  · ext s
    simp only [ctxC, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro hs
      refine ⟨hs, ?_⟩
      rw [show seed3.endpoints s = seedRR from rfl, seedRR]
      exact Sym2.mem_iff.mpr (Or.inl rfl)

/-! ## Stage 6 — the B3 recovery pack and B5 conservativity (2-04 §3, §6)

Reveal, remainder (Relocation made definitional), Internal/Windowless, and conservativity
spot-checks against the corrected interface. -/

/-- Reveal (2-04 §3): the relation together with its context. The threefold payload (D17) reads
off this unchanged from 2-02 §3. -/
def RevealC (A : RawC) (x : A.O) (r : A.R) : Set A.R := insert r (ctxC A x r)

/-- Introspection bound: `RevealC ⊆ pat` wherever `r` is held. -/
theorem RevealC_subset (A : RawC) (x : A.O) (r : A.R) (hr : r ∈ A.pat x) :
    RevealC A x r ⊆ A.pat x := by
  intro s hs
  rcases hs with rfl | hs
  · exact hr
  · exact ctxC_subset A x r hs

/-- Remainder — the Relocation Conjecture made definitional (2-04 §3; cf. `relocation_realizes`,
Spec203c): what the attending at `r` misses within `x`. The fish-gradation lives here — loss in
shapes, per relation, not merely in fact. -/
def remC (A : RawC) (x : A.O) (r : A.R) : Set A.R := A.pat x \ RevealC A x r

/-- Containment of an object in another: pattern-inclusion (the ratified parthood, 2-02 §6). -/
def ContainedInC (A : RawC) (y x : A.O) : Prop := A.pat y ⊆ A.pat x

/-- An endpoint (of either sort) contained in `x` (2-04 §3): an object endpoint by
pattern-inclusion, a relation endpoint by pattern-membership — the principled sort asymmetry
(objects contain their relations; relations reach their objects through relations). -/
def EndpointContainedC (A : RawC) (x : A.O) : A.O ⊕ A.R → Prop
  | Sum.inl y => ContainedInC A y x
  | Sum.inr s => s ∈ A.pat x

/-- Internal relations of `x`: those held entirely among contained parts (2-04 §3 / 2-02 §6). The
complement within `pat x` is `x`'s boundary. -/
def InternalC (A : RawC) (x : A.O) : Set A.R :=
  {r | r ∈ A.pat x ∧ ∀ z ∈ A.endpoints r, EndpointContainedC A x z}

theorem internalC_subset (A : RawC) (x : A.O) : InternalC A x ⊆ A.pat x :=
  fun _ h => h.1

/-- A windowless object: no boundary at all (2-02 §6; C1 conjectures these impossible in a
connected, no-total universe). -/
def WindowlessC (A : RawC) (x : A.O) : Prop := InternalC A x = A.pat x

/-- B5 conservativity spot-check 1 — P4-static re-instantiated: one line from K1. To be observed
(as an object endpoint) is to be enlarged. -/
theorem P4_static_C (A : RawC) (hK1 : K1 A) (r : A.R) (y : A.O)
    (hy : Sum.inl y ∈ A.endpoints r) : r ∈ A.pat y := hK1 r y hy

/-- π — the ratified containment overlap (2-04 §6, R1 untouched): the shared relations of two
objects. -/
def piC (A : RawC) (x y : A.O) : Set A.R := A.pat x ∩ A.pat y

/-- B5 conservativity spot-check 2 — a T14 comparative law re-instantiated against the corrected
interface: π is symmetric (sharing is mutual). -/
theorem piC_comm (A : RawC) (x y : A.O) : piC A x y = piC A y x :=
  Set.inter_comm _ _

/-! ### FP7 — the witness model `boolWitnessC` (2-04 §6)

A small coherent model discharging barrier two (contexts of a shared relation differ per host) and
the holding lemma's non-collapse (the two hosts keep distinct patterns). Objects `Bool`; relations
`Bool` — the shared self-loop `rS = false` (`ends = s(r̂S, r̂S)`) and the extra `rU = true`
(`ends = s(r̂S, r̂U)`, bearing on `rS` and itself). Object `true` hosts both; object `false` hosts
only `rS`. (The non-bisimilar-pair requirement of §6 is discharged separately and more sharply by
the coherent seeds, `seeds_not_bisimilar`, Spec204.) -/
def boolWitnessC : RawC where
  O := Bool
  R := Bool
  endpoints := fun r => match r with
    | false => s(Sum.inr false, Sum.inr false)
    | true => s(Sum.inr false, Sum.inr true)
  pat := fun o => match o with
    | true => {false, true}
    | false => {false}
  pat_nonempty := fun o => by cases o <;> exact ⟨false, by simp⟩

/-- FP7 — `boolWitnessC` is coherent (K3 satisfied by the small self-loops, as designed). -/
theorem boolWitnessC_coherent : CoherentC boolWitnessC := by
  refine ⟨?_, ?_, ?_⟩
  · -- K1: no object endpoints
    intro r x hx
    cases r <;>
      · simp only [boolWitnessC] at hx
        rw [Sym2.mem_iff] at hx
        rcases hx with h | h <;> simp at h
  · -- K2
    intro s x r hs hr
    cases x <;> cases s <;> simp_all [boolWitnessC, Sym2.mem_iff]
  · -- K3
    intro x r hr
    cases x <;> cases r
    · exact ⟨false, by simp [boolWitnessC], Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · simp [boolWitnessC] at hr
    · exact ⟨false, by simp [boolWitnessC], Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · exact ⟨true, by simp [boolWitnessC], Sym2.mem_iff.mpr (Or.inr rfl)⟩

/-- FP7 — the `contexts_differ` analogue (barrier two): the shared relation `rS` has DIFFERENT
contexts at its two hosts. In object `true` it is borne upon by both `rS` and `rU`; in object
`false` only by `rS`. Observer-locality survives the correction — visible now in the arena itself
(2-04 §2 requirement (i), §6). -/
theorem contextsC_differ :
    ctxC boolWitnessC true false ≠ ctxC boolWitnessC false false := by
  intro h
  have htrue : (true : Bool) ∈ ctxC boolWitnessC true false := by
    refine ⟨?_, ?_⟩
    · show (true : Bool) ∈ boolWitnessC.pat true; simp [boolWitnessC]
    · show Sum.inr false ∈ boolWitnessC.endpoints true
      rw [show boolWitnessC.endpoints true = s(Sum.inr false, Sum.inr true) from rfl]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
  rw [h] at htrue
  have hf : (true : Bool) ∈ boolWitnessC.pat false := htrue.1
  simp [boolWitnessC] at hf

/-- FP7 — the holding lemma is non-collapsing here: the two hosts keep DISTINCT patterns. The
K-triple neither over- nor under-constrains (2-04 §7). -/
theorem boolWitnessC_pat_distinct : boolWitnessC.pat true ≠ boolWitnessC.pat false := by
  intro h
  have hf : (true : Bool) ∈ boolWitnessC.pat false :=
    h ▸ (show (true : Bool) ∈ boolWitnessC.pat true by simp [boolWitnessC])
  simp [boolWitnessC] at hf

/-! ## Stage 7 (FP3) — P3h and the hosted-relations doctrine (2-04 §5)

`hosted` is a definable predicate; the doctrine relativizes every ontology-level quantifier over
relations to it. FP3 predicts unhosted relation-points exist. -/

/-- A relation is *hosted* when it lies in some object's pattern (2-04 §5). Definable, as the
doctrine requires. -/
def hosted (A : RawC) (r : A.R) : Prop := ∃ x, r ∈ A.pat x

/-- A coherent one-point-plus witness with an UNHOSTED relation: `true` is a self-witnessing
loop (hosted); `false` is a pure higher-order self-loop with no object endpoint, so K1 never
forces it into any pattern — and it is in none. -/
def unhostedWitness : RawC where
  O := PUnit
  R := Bool
  endpoints := fun r => match r with
    | true => s(Sum.inr true, Sum.inr true)
    | false => s(Sum.inr false, Sum.inr false)
  pat := fun _ => {true}
  pat_nonempty := fun _ => ⟨true, rfl⟩

theorem unhostedWitness_coherent : CoherentC unhostedWitness := by
  refine ⟨?_, ?_, ?_⟩
  · -- K1: no object endpoints anywhere
    intro r x hx
    rcases r with _ | _ <;>
      · simp only [unhostedWitness] at hx
        rw [Sym2.mem_iff] at hx
        rcases hx with h | h <;> simp at h
  · -- K2: the only hosted relation is `true`, a self-loop
    intro s x r hs hr
    have hs' : s = true := hs
    subst hs'
    rw [show unhostedWitness.endpoints true = s(Sum.inr true, Sum.inr true) from rfl,
        Sym2.mem_iff] at hr
    rcases hr with h | h <;> (rw [Sum.inr.injEq] at h; subst h; exact hs)
  · -- K3: `true` is borne upon by itself
    intro x r hr
    have hr' : r = true := hr
    subst hr'
    exact ⟨true, rfl, Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- FP3 (interface level) — CONFIRMED against a coherent model: unhosted relation-points exist.
`false` is a coherent, pure higher-order relation that no pattern hosts — finality manufactures
behaviors no object picks up (2-04 §5). The doctrine of §5 (the ontology's relations are the
hosted ones) is thereby necessary, not decorative. The `Ω_C`-proper form of FP3 (an unhosted
point *inside* Ω_C) awaits the construction (2-04 O-2-05-*); this records the phenomenon at the
interface. -/
theorem unhosted_exists :
    ∃ (A : RawC) (r : A.R), CoherentC A ∧ ¬ hosted A r := by
  refine ⟨unhostedWitness, false, unhostedWitness_coherent, ?_⟩
  rintro ⟨x, hx⟩
  have : (false : Bool) ∈ ({true} : Set Bool) := hx
  simp at this

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms HC_map_id
#print axioms ascentC_R
#print axioms ascentC_O
#print axioms genericC_properness
#print axioms saturationC
#print axioms RevealC_subset
#print axioms internalC_subset
#print axioms P4_static_C
#print axioms piC_comm
#print axioms boolWitnessC_coherent
#print axioms contextsC_differ
#print axioms boolWitnessC_pat_distinct
#print axioms unhostedWitness_coherent
#print axioms unhosted_exists
end AxiomAudit

/-
================================================================================
2-04 §7 FP predictions ↔ this file (Stages 2r,4,5,6,7; see 2-04 §9 Results)
================================================================================
-- Stage 2 (reduction)  HC, HC.map, HC_map_id    — univariate reduction recorded; νHC/Ω_C construction DEFERRED
-- FP6  ascent vs F_C exactly (proxy replaced)    → ascentC_R, ascentC_O                  CONFIRMED
-- FP4  residue at self-anchored loops survives   → genericC_properness, saturationC       CONFIRMED (interface+witness)
-- B3   recovery pack (Reveal/rem/Internal)       → RevealC, RevealC_subset, remC, InternalC, WindowlessC  DELIVERED
-- B5   conservativity spot-checks                → P4_static_C, piC_comm                   DELIVERED
-- FP7  boolWitnessC compiles; contexts differ    → boolWitnessC_coherent, contextsC_differ, boolWitnessC_pat_distinct  CONFIRMED
-- FP3  unhosted relation-points exist (interface)→ hosted, unhosted_exists                 CONFIRMED (interface; Ω_C-proper deferred)
--
-- Marked hostile-first deviation (sanctioned, 2-04-mechanization-a §3): Stages 2-3's mutual
-- νF_C/Ω_C construction is the documented remaining boundary (Stage 2 drop clause). This file
-- delivers the construction-INDEPENDENT content of Stages 4-7 plus the Stage-2 reduction. FP5
-- (anti-Mirror against Ω_C PROPER) awaits the construction; its substance — coherent non-bisimilar
-- states — is witnessed by seeds_not_bisimilar (Spec204) and boolWitnessC here.
--
-- Entrant ↔ Lean name:
--   Stage 2r = RelEx.Corrected.HC, HC.map, HC_map_id
--   Stage 4  = RelEx.Corrected.ascentC_R, ascentC_O
--   Stage 5  = RelEx.Corrected.ctxC, ctxC_subset, SelfAnchoredC, genericC_properness, saturationC
--   Stage 6  = RelEx.Corrected.RevealC, RevealC_subset, remC, ContainedInC, EndpointContainedC,
--              InternalC, internalC_subset, WindowlessC, P4_static_C, piC, piC_comm,
--              boolWitnessC, boolWitnessC_coherent, contextsC_differ, boolWitnessC_pat_distinct
--   Stage 7  = RelEx.Corrected.hosted, unhostedWitness, unhostedWitness_coherent, unhosted_exists
-/

