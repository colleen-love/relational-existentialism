/-
Spec 2.3c — Close the Trials: the Relocation Conjecture, the one-bit audit, and the Ascent.

Normative source: `series-2/spec/2-3-mechanization-c.md` — the order — which carries its
own FROZEN predictions (§2, P1–P6), pre-registered hostile-first. This file is that order's
lab notebook: every theorem's doc-comment names the prediction it CONFIRMS or REFUTES; a
surprised prediction is the trial working; no refutation is softened.

Builds on `Spec23b` (the entrants, `PfNe`, `forced_univ`/`forced_empty`, `RawC`, `AttA2`,
`AttB`), which transitively supplies the whole chain (incl. `Spec21c`'s `G`).

Scope note (2-3-mechanization-c §1): (C)'s coherence/parthood design is OUT of scope and
gates B4/B5 — everything here is pre-design. The O-2-3-2 "pairs" check is discharged in
substance by `B2_C_separation` (Spec23b) and is not reproved.
-/
import Spec23b

open RelEx.TwoSorted (G)

namespace RelEx.Trials

/-! ## BIT — the one-bit audit of A2 (2-3-mechanization-c §3; P1)

Spec23b's `B1_A2` showed A2 passes B1 with two witnesses differing only in the emptiness of
the grasp `H`. This section upgrades that observation to a theorem: over the point, A2's
*entire* plurality is the ∅/nonempty bit — the primordial atom D4 refuses. B7's elimination of
A2 rests on a proof, not two examples. -/

/-- Over a subsingleton carrier every set is `∅` or `univ` — the dichotomy behind the forbidden
coin. Companion to `forced_univ`/`forced_empty` (Spec23b). -/
theorem forced_dichotomy {α : Type} [Subsingleton α] (S : Set α) :
    S = ∅ ∨ S = Set.univ := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (forced_univ h)

/-- BIT — CONFIRMS P1: A2's entire plurality over the point is the ∅-bit. `M` is forced to
`univ` (`forced_univ`); `H` ranges over `{∅, univ}` (`forced_dichotomy`); so agreement on the
bit `H = ∅` is equality. This proves, rather than illustrates, §5.6's sentence "the two
`B1_A2` witnesses differ solely in emptiness": B7's audit of A2 — the primordial atom, the coin
D4 refuses — now rests on a theorem. The (A)-family's second elimination is machine-checked end
to end. -/
theorem A2_one_bit : ∀ a b : AttA2 PUnit, (a.1.1 = ∅ ↔ b.1.1 = ∅) → a = b := by
  haveI : Nonempty (Sym2 PUnit) := ⟨s(PUnit.unit, PUnit.unit)⟩
  rintro a b hbit
  have hMa : a.1.2 = Set.univ := forced_univ a.2.2.2
  have hMb : b.1.2 = Set.univ := forced_univ b.2.2.2
  have hH : a.1.1 = b.1.1 := by
    rcases forced_dichotomy a.1.1 with ha | ha
    · rw [ha, hbit.mp ha]
    · have hane : a.1.1 ≠ ∅ := by rw [ha]; exact Set.univ_nonempty.ne_empty
      have hbne : b.1.1 ≠ ∅ := fun hb => hane (hbit.mpr hb)
      rcases forced_dichotomy b.1.1 with hb | hb
      · exact absurd hb hbne
      · rw [ha, hb]
  exact Subtype.ext (Prod.ext_iff.mpr ⟨hH, by rw [hMa, hMb]⟩)

/-- The canonical remainder witness (2.3 §5.1). -/
def r0 : Sym2 PUnit := s(PUnit.unit, PUnit.unit)

/-- The `H = ∅` witness: grasp empty, remainder `{r̂}`. -/
def a2Empty : AttA2 PUnit :=
  ⟨(∅, {r0}), Set.finite_empty, Set.finite_singleton r0, Set.singleton_nonempty r0⟩

/-- The `H = {r̂}` witness: grasp full, remainder `{r̂}`. -/
def a2Full : AttA2 PUnit :=
  ⟨({r0}, {r0}), Set.finite_singleton r0, Set.finite_singleton r0, Set.singleton_nonempty r0⟩

open Classical in
/-- BIT (equivalence form) — A2 over the point is exactly one bit. Powered by `A2_one_bit`
(the bit determines the element) and the two `B1_A2` witnesses (both bits realized). Classical
(the bit is decided by choice). The forbidden coin, exhibited as an iso to `Bool`. -/
noncomputable def A2_equiv_bool : AttA2 PUnit ≃ Bool where
  toFun a := if a.1.1 = ∅ then true else false
  invFun b := if b then a2Empty else a2Full
  left_inv a := by
    refine A2_one_bit _ a ?_
    by_cases h : a.1.1 = ∅ <;>
      simp [h, a2Empty, a2Full, Set.singleton_ne_empty]
  right_inv b := by
    cases b <;> simp [a2Empty, a2Full, Set.singleton_ne_empty]

/-! ## RELOC — the Relocation Conjecture (2-3-mechanization-c §4; C-B6, P2/P3)

Inside (C): aperture = higher-order neighborhood, remainder = its complement. The naive
(symmetric) neighborhood cannot be directed (`tied_symm`, P2); direction is bought one storey
up, by ownership marks (`OwnedTie`, P3). -/

/-- Bare higher-order tie: some relation's endpoints are exactly these two, as relations. The
naive neighborhood generator. -/
def Tied (A : RawC) (r q : A.R) : Prop :=
  ∃ m : A.R, A.endpoints m = s(Sum.inr r, Sum.inr q)

/-- RELOC-SYM — CONFIRMS P2, the hazard on record: bare ties are symmetric, because `Sym2` is
unordered. The naive neighborhood cannot be directed; whatever "aperture" means in (C), it is
not this alone. -/
theorem tied_symm (A : RawC) (r q : A.R) : Tied A r q → Tied A q r :=
  fun ⟨m, hm⟩ => ⟨m, hm.trans Sym2.eq_swap⟩

/-- Owned tie: a tie links `r` and `q`, and a further relation links the tie back to `r` — the
tie is *r's*. Direction purchased with one more storey of the tower, not with an ordering: A6's
unorderedness is intact at every level. -/
def OwnedTie (A : RawC) (r q : A.R) : Prop :=
  ∃ m : A.R, A.endpoints m = s(Sum.inr r, Sum.inr q) ∧
    ∃ o : A.R, A.endpoints o = s(Sum.inr m, Sum.inr r)

/-- The aperture of `r` at `x`, definably inside (C): the pattern-members `r`'s owned ties
reach. -/
def apertureC (A : RawC) (x : A.O) (r : A.R) : Set A.R :=
  {q | q ∈ A.pat x ∧ OwnedTie A r q}

/-- The remainder: what the attending misses — the neighborhood's complement in the pattern. -/
def remainderC (A : RawC) (x : A.O) (r : A.R) : Set A.R :=
  A.pat x \ apertureC A x r

/-- RELOC-DEF (partition, half one): aperture and remainder cover the pattern. -/
theorem aperture_union_remainder (A : RawC) (x : A.O) (r : A.R) :
    apertureC A x r ∪ remainderC A x r = A.pat x :=
  Set.union_diff_cancel (fun _ hp => hp.1)

/-- RELOC-DEF (partition, half two): aperture and remainder are disjoint. Together with
`aperture_union_remainder` this is the D17-payload shape appearing inside the arena — the B3
down payment. -/
theorem aperture_disjoint_remainder (A : RawC) (x : A.O) (r : A.R) :
    Disjoint (apertureC A x r) (remainderC A x r) :=
  Set.disjoint_left.mpr (fun _ hp hp' => hp'.2 hp)

/-- (A)'s shape over an arbitrary carrier: a finite nonempty pattern with a proper division per
member. `AttA = AttAGen (Sym2 PUnit)` definitionally, and `AttAGen ρ` is defeq to
`DivisionData ρ Set.Finite (↥·)` — the very class the Forcing Lemma kills over the point, now
realized inside the tower over any carrier. -/
def AttAGen (ρ : Type) : Type :=
  Σ S : PfNe ρ, ∀ _r : ↥S.1, {T : Set ρ // T ⊂ S.1}

/-- FORGET — (B) is (A) with the anatomy forgotten: per attending, keep the bare division pair.
`AttB` (Spec23b) is the instance at `ρ := Sym2 PUnit`. Its existence is its content: proved
reductions dissolve the fork into a lattice (2.3 §5.2 B6). -/
def forgetAnatomy {ρ : Type} (a : AttAGen ρ) (r : ↥a.1.1) :
    { p : Set ρ × Set ρ // p.1.Finite ∧ p.1.Nonempty ∧ p.2 ⊂ p.1 } :=
  ⟨(a.1.1, (a.2 r).1), a.1.2.1, a.1.2.2, (a.2 r).2⟩

/-- The tie-index for `a`: pairs `(r, q)` with `r` a pattern member and `q` a member of `r`'s
aperture-target. One tie relation and one ownership mark per such pair. -/
def RelocTies {ρ : Type} (a : AttAGen ρ) : Type := Σ r : ↥a.1.1, ↥(a.2 r).1

/-- The (C)-shape realizing an (A)-datum `a` (2-3-mechanization-c §4 construction plan). One
object; base relations = pattern members; one tie per aperture-pair; one ownership mark per tie
(linking the tie back to its owner `r`). -/
def relocC {ρ : Type} (a : AttAGen ρ) : RawC where
  O := PUnit
  R := ↥a.1.1 ⊕ (RelocTies a ⊕ RelocTies a)
  endpoints := fun rel => match rel with
    | Sum.inl _ => s(Sum.inl PUnit.unit, Sum.inl PUnit.unit)
    | Sum.inr (Sum.inl ⟨r, q⟩) =>
        s(Sum.inr (Sum.inl r), Sum.inr (Sum.inl ⟨q.1, (a.2 r).2.subset q.2⟩))
    | Sum.inr (Sum.inr ⟨r, q⟩) =>
        s(Sum.inr (Sum.inr (Sum.inl ⟨r, q⟩)), Sum.inr (Sum.inl r))
  pat := fun _ => Set.range (fun r : ↥a.1.1 => (Sum.inl r : ↥a.1.1 ⊕ (RelocTies a ⊕ RelocTies a)))
  pat_nonempty := fun _ => by
    obtain ⟨w, hw⟩ := a.1.2.2
    exact ⟨Sum.inl ⟨w, hw⟩, ⟨w, hw⟩, rfl⟩

/-- The junk check (the hostile direction of the Relocation iff): an `OwnedTie` between two base
relations in `relocC a` can only have come from the constructed family, so it witnesses genuine
aperture membership. The ownership mark is what collapses the `Sym2`-swap ambiguity: a bare tie
`s(inr (e r), inr (e q))` also reads as `s(inr (e q), inr (e r))`, but the mark forces the
tie's owner to be `r`. -/
theorem relocC_owned_imp {ρ : Type} (a : AttAGen ρ) (r q : ↥a.1.1)
    (hown : OwnedTie (relocC a) (Sum.inl r) (Sum.inl q)) : q.1 ∈ (a.2 r).1 := by
  obtain ⟨m, hm, o, ho⟩ := hown
  rcases m with m₀ | (⟨r', q'⟩ | ⟨r', q'⟩)
  · -- m a base relation: endpoints on the O side, cannot equal an all-`inr` pair
    simp [relocC, Sym2.eq_iff] at hm
  · -- m a tie ⟨r', q'⟩
    simp only [relocC, Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- straight match: h1 : r' = r, h2 : ⟨q'.1, _⟩ = q
      have hqq : q'.1 = q.1 := congrArg Subtype.val h2
      rw [← hqq, ← h1]; exact q'.2
    · -- swap: h1 : r' = q, h2 : ⟨q'.1, _⟩ = r — resolve with the ownership mark o
      rcases o with o₀ | (⟨ρ₀, σ₀⟩ | ⟨ρ₀, σ₀⟩)
      · simp [relocC, Sym2.eq_iff] at ho
      · -- o another tie: its endpoints are inner-`inl`, but `Sum.inr m` is inner-`inr` — clash
        simp [relocC, Sym2.eq_iff] at ho
      · -- o a mark ⟨ρ₀, σ₀⟩: forces ρ₀ = r' (owner of m) and ρ₀ = r (mark's back-link)
        simp only [relocC, Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq] at ho
        rcases ho with ⟨g1, g2⟩ | ⟨g1, _⟩
        · have hρr' : ρ₀ = r' := congrArg Sigma.fst g1
          have hr'r : r' = r := hρr'.symm.trans g2
          have hq'r : q'.1 = r.1 := congrArg Subtype.val h2
          have hqr : q.1 = r.1 := congrArg Subtype.val (h1.symm.trans hr'r)
          have hqq : q.1 = q'.1 := hqr.trans hq'r.symm
          rw [hqq, ← hr'r]; exact q'.2
        · exact absurd g1 (by simp)
  · -- m a mark used as a tie: endpoints inner-`inr`, cannot match inner-`inl` base pair
    simp [relocC, Sym2.eq_iff] at hm

/-- RELOC — the Relocation Conjecture (C-B6), directed form; CONFIRMS P3. Every (A)-datum over
an arbitrary carrier is realized inside a (C)-shape: the pattern embeds as base relations,
aperture reads off by owned ties (`relocC_owned_imp`), and properness relocates as
remainder-nonemptiness. Direction is bought one storey up — the ownership mark — not with an
ordered pair, so A6's unorderedness is intact. Consequently **(C) is the arena; (A) is its
phenomenology, derived; (B) is (A) with the anatomy forgotten** (`forgetAnatomy`) — the fork
dissolves into a lattice and the recorded hybrid (C)+(A) stays closed. -/
theorem relocation_realizes (ρ : Type) (a : AttAGen ρ) :
    ∃ (A : RawC) (x : A.O) (e : ↥a.1.1 → A.R),
      Function.Injective e ∧
      A.pat x = Set.range e ∧
      (∀ r q : ↥a.1.1, e q ∈ apertureC A x (e r) ↔ q.1 ∈ (a.2 r).1) ∧
      (∀ r : ↥a.1.1, (remainderC A x (e r)).Nonempty) := by
  refine ⟨relocC a, PUnit.unit, (fun r => Sum.inl r), ?_, rfl, ?_, ?_⟩
  · intro r₁ r₂ h; exact Sum.inl.inj h
  · intro r q
    simp only [apertureC, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, hown⟩
      exact relocC_owned_imp a r q hown
    · intro hq
      refine ⟨⟨q, rfl⟩, Sum.inr (Sum.inl ⟨r, ⟨q.1, hq⟩⟩), rfl,
        Sum.inr (Sum.inr ⟨r, ⟨q.1, hq⟩⟩), rfl⟩
  · intro r
    obtain ⟨w, hwmem, hwnot⟩ := Set.exists_of_ssubset (a.2 r).2
    refine ⟨Sum.inl ⟨w, hwmem⟩, ⟨⟨w, hwmem⟩, rfl⟩, ?_⟩
    simp only [apertureC, Set.mem_setOf_eq, not_and]
    intro _ hown
    exact hwnot (relocC_owned_imp a r ⟨w, hwmem⟩ hown)

/-! ## ASCENT — stage-wise non-collapse and growth (2-3-mechanization-c §5; P4/P6)

The terminal sequence of the (C)-functor over the initial point never re-collapses, and the
collapsed control stays flat forever. -/

/-! The terminal-sequence stages of the (C)-functor over the initial point:
`(O₀,R₀) = (1,1)`; `O_{n+1} = P⁺f(R_n)`; `R_{n+1} = Sym2(O_n ⊕ R_n)`. Set-based (`PfNe`). -/
mutual
  /-- Object-sort stage: `O₀ = 1`, `O_{n+1} = P⁺f(R_n)`. -/
  def OStage : ℕ → Type
    | 0 => PUnit
    | n+1 => PfNe (RStage n)
  /-- Relation-sort stage: `R₀ = 1`, `R_{n+1} = Sym2(O_n ⊕ R_n)`. -/
  def RStage : ℕ → Type
    | 0 => PUnit
    | n+1 => Sym2 (OStage n ⊕ RStage n)
end

/-- Both sorts are nonempty at every stage (the One can always attend). -/
theorem stage_nonempty : ∀ n, Nonempty (OStage n) ∧ Nonempty (RStage n) := by
  intro n
  induction n with
  | zero => exact ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩⟩
  | succ n ih =>
    obtain ⟨⟨o⟩, ⟨r⟩⟩ := ih
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · exact (⟨{r}, Set.finite_singleton r, Set.singleton_nonempty r⟩ : PfNe (RStage n))
    · exact (s(Sum.inl o, Sum.inl o) : Sym2 (OStage n ⊕ RStage n))

/-- Two concrete distinct relations at every stage `n+1`: the self-relation and a bearing on a
lower relation, separated by an `inr` endpoint (the `B1_C` separation, at every storey). -/
theorem RStage_succ_two (n : ℕ) : ∃ a b : RStage (n+1), a ≠ b := by
  obtain ⟨o⟩ := (stage_nonempty n).1
  obtain ⟨r⟩ := (stage_nonempty n).2
  refine ⟨s(Sum.inl o, Sum.inl o), s(Sum.inl o, Sum.inr r), ?_⟩
  intro heq
  have hmem : (Sum.inr r : OStage n ⊕ RStage n) ∈
      (s(Sum.inl o, Sum.inr r) : Sym2 (OStage n ⊕ RStage n)) := Sym2.mem_iff.mpr (Or.inr rfl)
  rw [← heq, Sym2.mem_iff] at hmem
  rcases hmem with h | h <;> simp at h

/-- ASC-NC — CONFIRMS P4 at the relation sort: it never re-collapses. The Mirror's collapse
argument fails at every stage of the terminal sequence. -/
theorem ascent_R (n : ℕ) : ¬ Subsingleton (RStage (n+1)) := by
  obtain ⟨a, b, hne⟩ := RStage_succ_two n
  exact fun h => hne (@Subsingleton.elim _ h a b)

/-- HONESTY LEMMA (P4) — at depth 1 the object sort is still a point: `O₁ = P⁺f(1) ≅ 1`. The
depth-1 B1 pass of (C) is carried entirely by the relation sort; the object sort inherits
plurality one stage later (`ascent_O`). Kept so no reader mistakes `B1_C` for more than it is. -/
theorem O1_subsingleton : Subsingleton (OStage 1) := by
  haveI : Subsingleton (RStage 0) := inferInstanceAs (Subsingleton PUnit)
  exact inferInstanceAs (Subsingleton (PfNe (RStage 0)))

/-- ASC-NC — CONFIRMS P4 at the object sort, from stage 2 on: two distinct stage-`n+1`
relations give two distinct singleton patterns. -/
theorem ascent_O (n : ℕ) : ¬ Subsingleton (OStage (n+2)) := by
  obtain ⟨r₁, r₂, hne⟩ := RStage_succ_two n
  intro h
  let P₁ : PfNe (RStage (n+1)) := ⟨{r₁}, Set.finite_singleton r₁, Set.singleton_nonempty r₁⟩
  let P₂ : PfNe (RStage (n+1)) := ⟨{r₂}, Set.finite_singleton r₂, Set.singleton_nonempty r₂⟩
  have hEq : P₁ = P₂ := @Subsingleton.elim (OStage (n+2)) h P₁ P₂
  have h2 : ({r₁} : Set (RStage (n+1))) = {r₂} := congrArg Subtype.val hEq
  exact hne (Set.singleton_eq_singleton_iff.mp h2)

/-! ### ASC-STRICT — strict growth of the stages (P5, SHOULD-strong) -/

/-- Stage embeddings: each sort embeds into its successor stage. O-step: image under the
relation embedding (injective, `Set.image_injective`); R-step: `Sym2.map (Sum.map · ·)` with
injectivity (`Sym2.map.injective`, `Function.Injective.sum_map`). Base cases into the singleton
stages (domains subsingleton). -/
def stageEmbed : ∀ n, (OStage n ↪ OStage (n+1)) × (RStage n ↪ RStage (n+1))
  | 0 =>
    (⟨fun _ => (⟨{(PUnit.unit : RStage 0)}, Set.finite_singleton _, Set.singleton_nonempty _⟩ :
        PfNe (RStage 0)),
      fun _ _ _ => Subsingleton.elim (α := PUnit) _ _⟩,
     ⟨fun _ => (s(Sum.inl PUnit.unit, Sum.inl PUnit.unit) : Sym2 (OStage 0 ⊕ RStage 0)),
      fun _ _ _ => Subsingleton.elim (α := PUnit) _ _⟩)
  | n+1 =>
    let eO := (stageEmbed n).1
    let eR := (stageEmbed n).2
    (⟨fun S => (⟨eR '' S.1, Set.Finite.image _ S.2.1, S.2.2.image _⟩ : PfNe (RStage (n+1))),
      fun _ _ h =>
        Subtype.ext (Set.image_injective.mpr eR.injective (Subtype.ext_iff.mp h))⟩,
     ⟨Sym2.map (Sum.map eO eR),
      Sym2.map.injective (eO.injective.sum_map eR.injective)⟩)

/-- ASC-STRICT — CONFIRMS P5, the Ascent: every storey holds something fresh — a relation
missed by the stage embedding. Induction: stage 1 misses the bearing `s(inl ⋆, inr ⋆)`; and if
`z*` is missed at stage `n+1`, then `s(inr z*, inr z*)` is missed at stage `n+2` (an image
relation has both endpoints in the image of `Sum.map`, so an `inr z*` endpoint forces a
preimage of `z*` under the relation embedding — contradiction). This substantiates §5.3's
"F(1) infinite" at the stage level; the limit's cardinality is not decided here (an inverse
limit of strictly growing finite stages need not be infinite without further structure). -/
theorem ascent_strict : ∀ n, ∃ z : RStage (n+1), z ∉ Set.range (stageEmbed n).2 := by
  intro n
  induction n with
  | zero =>
    refine ⟨s(Sum.inl PUnit.unit, Sum.inr PUnit.unit), ?_⟩
    rintro ⟨w, hw⟩
    -- (stageEmbed 0).2 w = s(inl ⋆, inl ⋆); it cannot carry an `inr` endpoint
    have hmem : (Sum.inr PUnit.unit : OStage 0 ⊕ RStage 0) ∈
        (s(Sum.inl PUnit.unit, Sum.inr PUnit.unit) : Sym2 (OStage 0 ⊕ RStage 0)) :=
      Sym2.mem_iff.mpr (Or.inr rfl)
    rw [← hw] at hmem
    revert hmem
    have hval : (stageEmbed 0).2 w = s(Sum.inl PUnit.unit, Sum.inl PUnit.unit) := rfl
    rw [hval, Sym2.mem_iff]
    rintro (h | h) <;> simp at h
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨s(Sum.inr z, Sum.inr z), ?_⟩
    rintro ⟨w, hw⟩
    -- `Sum.inr z` is an endpoint of the RHS, hence in `Sym2.map (Sum.map eO eR) w`
    have hmem : (Sum.inr z : OStage (n+1) ⊕ RStage (n+1)) ∈
        (s(Sum.inr z, Sum.inr z) : Sym2 (OStage (n+1) ⊕ RStage (n+1))) :=
      Sym2.mem_iff.mpr (Or.inl rfl)
    rw [← hw] at hmem
    have hmap : (stageEmbed (n+1)).2 w =
        Sym2.map (Sum.map (stageEmbed n).1 (stageEmbed n).2) w := rfl
    rw [hmap, Sym2.mem_map] at hmem
    obtain ⟨c, _, hc⟩ := hmem
    -- `Sum.map eO eR c = Sum.inr z` forces `c = inr c₁` with `eR c₁ = z` — a preimage
    rcases c with c₀ | c₁
    · simp [Sum.map] at hc
    · exact hz ⟨c₁, by simpa [Sum.map] using hc⟩

/-! ### CTRL — the flat control (P6) -/

/-- Generalization of `G_unit_subsingleton` (Spec23a): `G` preserves subsingletons — `G X` is
defeq to `PfNe (Sym2 X)`, so `PfNe.subsingleton` applies. -/
theorem G_subsingleton_of (X : Type) [Subsingleton X] : Subsingleton (G X) :=
  inferInstanceAs (Subsingleton (PfNe (Sym2 X)))

/-- CTRL — CONFIRMS P6: the control's terminal sequence over the point is FLAT — one point at
every stage, forever. The collapsed functor does not merely fail F(1); it fails at every depth,
while (C) ascends. This is the discriminating power of the stage checks, stated as a theorem. -/
theorem control_flat : ∀ n, Subsingleton ((fun X => G X)^[n] PUnit) := by
  intro n
  induction n with
  | zero => exact inferInstanceAs (Subsingleton PUnit)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact @G_subsingleton_of _ ih

end RelEx.Trials

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Trials
#print axioms A2_one_bit
#print axioms A2_equiv_bool
#print axioms tied_symm
#print axioms aperture_union_remainder
#print axioms aperture_disjoint_remainder
#print axioms relocation_realizes
#print axioms stage_nonempty
#print axioms ascent_R
#print axioms O1_subsingleton
#print axioms ascent_O
#print axioms ascent_strict
#print axioms control_flat
end AxiomAudit

/-
================================================================================
2-3-mechanization-c §2 predictions ↔ outcomes  (see 2.3 §5.7 for the prose transcript)
================================================================================
-- One bit:        A2_one_bit (+ A2_equiv_bool)          — P1                → CONFIRMED
-- Sym hazard:     tied_symm                             — P2                → CONFIRMED
-- Relocation:     relocation_realizes (directed)        — P3 / C-B6         → CONFIRMED
-- Forgetting:     forgetAnatomy                         — C-B6 lattice      → DELIVERED
-- No re-collapse: ascent_R, ascent_O, O1_subsingleton   — P4                → CONFIRMED
-- The Ascent:     ascent_strict                         — P5                → CONFIRMED
-- Control flat:   control_flat                          — P6                → CONFIRMED
-- Pairs check (O-2-3-2): discharged by B2_C_separation (Spec23b) — cited, not reproved.
--
-- All predictions confirmed; nothing refuted. P3 (the directed Relocation) holds: (A)'s
-- directed anatomy relocates into pure (C) — direction bought by the ownership mark, one storey
-- up, not by an ordered pair. So (C) is the arena, (A) its derived phenomenology, (B) the
-- forgotten anatomy; the fork is a lattice and the hybrid (C)+(A) stays closed.
--
-- Deviations from 2-3-mechanization-c.md:
--   * ascent_fin (the "at least n+1 elements" stretch, §5, marked "drop freely with note") is
--     DROPPED: ascent_strict already substantiates "F(1) infinite" at the stage level, and the
--     cardinality-of-the-limit claim is out of scope per the order's own honesty note.
--   * The B2-C pairs check is cited from Spec23b (B2_C_separation), not reproved, per §1.
--
-- Entrant ↔ Lean name:
--   BIT       = RelEx.Trials.forced_dichotomy, A2_one_bit, A2_equiv_bool
--   RELOC     = RelEx.Trials.Tied, tied_symm, OwnedTie, apertureC, remainderC,
--               aperture_union_remainder, aperture_disjoint_remainder, AttAGen, forgetAnatomy,
--               RelocTies, relocC, relocC_owned_imp, relocation_realizes
--   ASCENT    = RelEx.Trials.OStage, RStage, stage_nonempty, RStage_succ_two, ascent_R,
--               O1_subsingleton, ascent_O, stageEmbed, ascent_strict
--   CTRL      = RelEx.Trials.G_subsingleton_of, control_flat
-/
