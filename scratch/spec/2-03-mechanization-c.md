# 2.03-mechanization-c — Work Order: Close the Trials (the Relocation Conjecture, the One-Bit Audit, and the Ascent)

**This document describes:** `scratch/formal/Spec203c.lean` (new file; imports `Spec203b` — which transitively supplies the whole chain)
**Normative sources:** `scratch/spec/2-03.md` §5 (the battery: B6, B7; the frozen C-B6 prediction of §5.3; the results of §5.6) and §8 (O-2-03-1b, O-2-03-2). Specs win; report discrepancies.
**Audience:** Claude Code. All conventions in force. **This order carries its own frozen predictions (§2) — they are pre-registered as of this document's commit, hostile-first, and amendable afterward only as clearly-marked post-hoc annotations.** Same lab-notebook discipline as `-b`: every theorem's doc-comment names the prediction it CONFIRMS or REFUTES; a surprised prediction is the trial working; no refutation is softened.

---

## 1. Purpose and scope

Spec203b ran B1 on every entrant and the fork narrowed to (C) by elimination — twice over for the (A)-family. Three pieces of trial content remain mechanizable *before* the (C) coherence design (which is spec-side and gates B4/B5):

1. **RELOC** — the Relocation Conjecture (C-B6, frozen in 2-03 §5.3, still untested): inside (C), an attending's aperture and remainder are *definable* as its higher-order neighborhood and that neighborhood's complement. If proved, (C) is the arena, (A) is its phenomenology derived, (B) is (A) with the anatomy forgotten — the fork dissolves into a lattice, and the recorded hybrid (C)+(A) is shown unnecessary.
2. **BIT** — the one-bit audit of A2: upgrade §5.6's observation ("the two `B1_A2` witnesses differ solely in emptiness") to the theorem that *all* of A2's plurality over the point is the ∅-bit. This converts B7's spec-level elimination of A2 from an audit resting on two examples into an audit resting on a proof.
3. **ASCENT** — O-2-03-2's first two sufficiency checks for (C): the collapse argument fails at *every* stage of the terminal sequence, not just the first — plus the honesty lemma that at depth 1 the pass is carried entirely by the relation sort (the object sort over the point is still a point until stage 2).

| ID | Name | Prediction under test (§2) | Priority |
|----|------|---------------------------|----------|
| BIT | `A2_one_bit` — the individuating resource is exactly the forbidden coin | P1 | MUST |
| RELOC-DEF | `Tied`/`apertureC`/`remainderC` — definability + partition | C-B6 (first half) | MUST |
| RELOC-SYM | `tied_symm` — the symmetrization hazard, on record | P2 | MUST |
| RELOC | `relocation_realizes` — directed recovery via owned ties | C-B6 + P3 | SHOULD-strong |
| FORGET | `forgetAnatomy` — the (A)→(B) reduction map | C-B6 ("(B) is (A) forgotten") | MUST (small) |
| ASC-NC | stages never re-collapse; `O1` honesty lemma | P4 | MUST |
| ASC-STRICT | strict stage growth (fresh element every storey) | P5 | SHOULD-strong |
| CTRL | the control's stages are flat forever | P6 | SHOULD (cheap) |
| DOC | results annotation + spec labels | — | MUST |

**Out of scope:** (C)'s coherence/parthood design (what is endpoint-coherence over `O ⊕ R`? — O-2-03-1b, *spec-side*, and the explicit gate on everything below this line); B4 and B5 (both need that design: the covariety hypotheses and the Model-analogue cannot be checked against a functor whose coherence predicate does not exist yet); νF construction for (C) (the winner's construction is its own order, via the Spec201c template, after the corrected-functor spec with its D20 F(1) pre-registration at the head); B3 beyond what RELOC delivers incidentally (RELOC *is* the down payment: aperture/remainder anatomy inside the arena is D17-payload material); the limit's cardinality (ASCENT proves the stages grow without bound; the infinitude of the final coalgebra itself is a further claim about the inverse limit — not chased, per the honesty note in P5); fog-vs-edges; D19.

**Note on O-2-03-2's pairs check:** "does F distinguish over pairs" is discharged in substance by `B2_C_separation` (Spec203b): a two-point (C)-shape with an observable, machine-checked difference. Record the discharge in the mapping table; do not write a separate theorem.

## 2. Predictions (FROZEN at this document's commit; hostile-first)

- **P1 — A2 is one bit.** Over the point, the ∅/nonemptiness of `H` *determines the element*: any two elements of `AttA2 PUnit` agreeing on whether `H = ∅` are equal (and both values are realized — the `B1_A2` witnesses). Consequently `AttA2 PUnit ≃ Bool`. High confidence. If this somehow *fails*, A2 has an individuating resource nobody has identified, and the B7 elimination is unsound as argued — report loudly.
- **P2 — the symmetrization hazard.** The bare higher-order neighborhood is symmetric: `Sym2` is unordered, so a tie `m` with endpoints `s(inr r, inr q)` witnesses `Tied r q` and `Tied q r` alike. Therefore the *naive* reading of C-B6 (aperture := bare neighborhood) cannot recover (A)'s per-attending *directed* division exactly; it recovers it only up to symmetry. This is a hazard named in advance, not a refutation of C-B6 — the conjecture as frozen says "higher-order neighborhood," and the honest question is what "neighborhood" must mean.
- **P3 — direction is one more storey, not an ordering.** The directed division *is* recoverable without violating A6's unorderedness: define ownership — `q` is in `r`'s aperture iff some tie `m` links `r` and `q` *and* some further relation links `m` back to `r` (the tie is r's). With ownership, exact recovery closes: every (A)-datum, over an arbitrary carrier, is realized inside a (C)-shape with aperture and remainder read off definably, properness relocating as remainder-nonemptiness. Moderate confidence — this is the order's real experiment. **If it fails, do not soften:** the finding would be that (A)'s directed anatomy does *not* relocate into pure (C), the Relocation Conjecture holds only in symmetrized form, and the recorded hybrid (C)+(A) re-enters under its admission clause. That outcome feeds the declared anatomy residue (fog-vs-edges) and is worth exactly as much as a confirmation.
- **P4 — no stage re-collapses.** In the terminal sequence of the (C)-functor over the initial point ((O₀,R₀) = (1,1); O_{n+1} = P⁺f(R_n); R_{n+1} = Sym2(O_n ⊕ R_n)): every stage is nonempty in both sorts; the relation sort is non-subsingleton from stage 1 on; the object sort from stage 2 on. **Honesty lemma alongside (mandatory):** O₁ ≅ 1 — at depth 1 the B1 pass is carried entirely by the relation sort; the object sort inherits plurality one stage later. High confidence.
- **P5 — the Ascent.** Growth is strict: each stage embeds into the next and misses something — a fresh element every storey (the new ways the One can turn upon its own turning). Stage n therefore holds at least n+1 relation-sort elements. This substantiates §5.3's "F(1) infinite" *at the stage level*; the cardinality of the limit itself is not decided here (an inverse limit of strictly growing finite sets is not automatically infinite without further structure — honesty over reach). High confidence.
- **P6 — the control is flat.** The collapsed G's stage sequence over the point is constant at one point: `Subsingleton (G^[n] PUnit)` for all n. The sharpest available contrast with P4/P5, and the reason the stage checks have discriminating power. Near-certain (one induction over `G_unit_subsingleton`'s generalization).

## 3. BIT — the one-bit audit (MUST; small)

```lean
namespace RelEx.Trials

/-- Over a subsingleton carrier every set is ∅ or univ — the dichotomy behind the
forbidden coin. Companion to `forced_univ`/`forced_empty` (Spec203b). -/
theorem forced_dichotomy {α : Type} [Subsingleton α] (S : Set α) :
    S = ∅ ∨ S = Set.univ := by
  sorry -- rcases on S.eq_empty_or_nonempty; forced_univ on the nonempty side.

/-- BIT — CONFIRMS P1: A2's entire plurality over the point is the ∅-bit. `M` is
forced to univ (`forced_univ`); `H` ranges over {∅, univ} (`forced_dichotomy`); so
agreement on the bit is equality. This proves, rather than illustrates, §5.6's
sentence "the two B1_A2 witnesses differ solely in emptiness": B7's audit of A2 —
the primordial atom, the coin D4 refuses — now rests on a theorem. The (A)-family's
second elimination is machine-checked end to end. -/
theorem A2_one_bit : ∀ a b : AttA2 PUnit, (a.1.1 = ∅ ↔ b.1.1 = ∅) → a = b := by
  sorry

/-- The same fact as an equivalence (noncomputable; classical). -/
noncomputable def A2_equiv_bool : AttA2 PUnit ≃ Bool := by
  sorry -- decide the bit classically; the B1_A2 witnesses provide the inverse.
```

`A2_equiv_bool` is SHOULD: if the `Equiv` plumbing fights, `A2_one_bit` plus the two existing witnesses already carry the audit — record the drop.

## 4. RELOC — the Relocation Conjecture (the order's centerpiece)

**The honest work here is the statement, as it was for FL.** Budget a day. The frozen conjecture (2-03 §5.3 C-B6): inside (C), aperture = higher-order neighborhood, remainder = its complement. Two readings, both mechanized:

```lean
/-- Bare higher-order tie: some relation's endpoints are exactly these two, as
relations. The naive neighborhood generator. -/
def Tied (A : RawC) (r q : A.R) : Prop :=
  ∃ m : A.R, A.endpoints m = s(Sum.inr r, Sum.inr q)

/-- RELOC-SYM — CONFIRMS P2, the hazard on record: bare ties are symmetric, because
`Sym2` is unordered. The naive neighborhood cannot be directed; whatever "aperture"
means in (C), it is not this alone. -/
theorem tied_symm (A : RawC) (r q : A.R) : Tied A r q → Tied A q r := by
  sorry -- Sym2.eq_swap.

/-- Owned tie: a tie links r and q, and a further relation links the tie back to r —
the tie is *r's*. Direction purchased with one more storey of the tower, not with
an ordering: A6's unorderedness is intact at every level. -/
def OwnedTie (A : RawC) (r q : A.R) : Prop :=
  ∃ m : A.R, A.endpoints m = s(Sum.inr r, Sum.inr q) ∧
    ∃ o : A.R, A.endpoints o = s(Sum.inr m, Sum.inr r)

/-- The aperture of r at x, definably inside (C): the pattern-members r's owned
ties reach. -/
def apertureC (A : RawC) (x : A.O) (r : A.R) : Set A.R :=
  {q | q ∈ A.pat x ∧ OwnedTie A r q}

/-- The remainder: what the attending misses — the neighborhood's complement in
the pattern. -/
def remainderC (A : RawC) (x : A.O) (r : A.R) : Set A.R :=
  A.pat x \ apertureC A x r

/-- RELOC-DEF — definability and partition: aperture and remainder split the
pattern. (Two small lemmas; the partition is definitional but state it, because
it is the D17-payload shape appearing inside the arena — the B3 down payment.) -/
theorem aperture_union_remainder (A : RawC) (x : A.O) (r : A.R) :
    apertureC A x r ∪ remainderC A x r = A.pat x := by sorry
theorem aperture_disjoint_remainder (A : RawC) (x : A.O) (r : A.R) :
    Disjoint (apertureC A x r) (remainderC A x r) := by sorry
```

**The recovery theorem.** Generalize `-b`'s (A)-shape off the point first (`AttA` is the instance at `Sym2 PUnit`; note the defeq — and note `AttAGen ρ` is also defeq to `DivisionData ρ Set.Finite (↥·)`, the very class the Forcing Lemma kills over the point, now realized inside the tower over any carrier):

```lean
/-- (A)'s shape over an arbitrary carrier: a finite nonempty pattern with a proper
division per member. `AttA = AttAGen (Sym2 PUnit)` definitionally. -/
def AttAGen (ρ : Type) : Type :=
  Σ S : PfNe ρ, ∀ _r : ↥S.1, {T : Set ρ // T ⊂ S.1}

/-- RELOC — the Relocation Conjecture (C-B6), directed form; CONFIRMS or REFUTES P3.
Every (A)-datum is realized inside a (C)-shape: the pattern embeds as the base
relations, aperture reads off by owned ties, and properness relocates as
remainder-nonemptiness. If this holds: (C) is the arena; (A) is its phenomenology,
derived; the hybrid clause stays closed. -/
theorem relocation_realizes (ρ : Type) (a : AttAGen ρ) :
    ∃ (A : RawC) (x : A.O) (e : ↥a.1.1 → A.R),
      Function.Injective e ∧
      A.pat x = Set.range e ∧
      (∀ r q : ↥a.1.1, e q ∈ apertureC A x (e r) ↔ q.1 ∈ (a.2 r).1) ∧
      (∀ r : ↥a.1.1, (remainderC A x (e r)).Nonempty) := by
  sorry
```

Construction plan (verify every mathlib name with `exact?`):

- `O := PUnit`; `R := ↥a.1.1 ⊕ (Ties ⊕ Ties)` where `Ties := Σ r : ↥a.1.1, ↥(a.2 r).1` — base relations, one tie per (r, q ∈ ap r), one ownership mark per tie.
- `endpoints (.inl _) := s(Sum.inl PUnit.unit, Sum.inl PUnit.unit)` (base relations sit on the object's self-pair); `endpoints (.inr (.inl ⟨r,q⟩)) := s(Sum.inr (.inl r), Sum.inr (.inl ⟨q.1, (a.2 r).2.subset q.2⟩))` (the tie); `endpoints (.inr (.inr ⟨r,q⟩)) := s(Sum.inr (.inr (.inl ⟨r,q⟩)), Sum.inr (.inl r))` (the mark: the tie is r's).
- `pat _ := Set.range Sum.inl`; nonempty from `a.1.2.2`.
- Forward direction of the iff: unfold; the constructed tie and mark witness `OwnedTie`.
- **The hostile direction is the junk check:** an `OwnedTie (e r) (e q)` witness must come from the constructed family. Case-split `m` and `o` over the three-way sum; `Sym2` pair equations against `Sum.inl`/`inr` disjointness kill every stray case (the pattern of `B2_C_separation`'s negative half, repeated; the two-sided `Sym2.eq_iff` is the workhorse). The subtle case: both `q ∈ ap r` and `r ∈ ap q` produce ties with *equal* endpoints (`Sym2` swap) — harmless, since ownership marks discriminate; walk it explicitly in a comment.
- Properness → remainder nonempty: `(a.2 r).2` gives a pattern member outside `ap r`; its image is outside the aperture by the junk check.

**Fallback (pre-registered, P2/P3):** if the directed form will not close in budget, ship the symmetric form — recovery of the iff with `Tied` in place of `OwnedTie` and `q ∈ ap r ∨ r ∈ ap q` on the right — plus `tied_symm`, state the directed form as a documented conjecture at the file's foot, and record the drop. That outcome is a *finding* (P3 refuted or undecided in budget): (A)'s anatomy relocates only up to symmetry; say so in §5.7 without softening, and note the hybrid clause's status accordingly.

**FORGET (MUST, small).** The other half of C-B6's lattice sentence:

```lean
/-- (B) is (A) with the anatomy forgotten: per attending, keep the bare division
pair. `AttB` (Spec203b) is the instance at `ρ := Sym2 PUnit`. Proved reductions
dissolve the fork into a lattice (2-03 §5.2 B6). -/
def forgetAnatomy {ρ : Type} (a : AttAGen ρ) (r : ↥a.1.1) :
    { p : Set ρ × Set ρ // p.1.Finite ∧ p.1.Nonempty ∧ p.2 ⊂ p.1 } :=
  ⟨(a.1.1, (a.2 r).1), a.1.2.1, a.1.2.2, (a.2 r).2⟩
```

Its existence is its content; no theorem needed beyond type-correctness. Doc-comment carries the lattice moral.

## 5. ASCENT — stage-wise non-collapse and growth (O-2-03-2, first two checks)

```lean
/-- The terminal-sequence stages of the (C)-functor over the initial point:
(O₀,R₀) = (1,1); O_{n+1} = P⁺f(R_n); R_{n+1} = Sym2(O_n ⊕ R_n). Set-based
(`PfNe`); no Fintype plumbing needed for the MUSTs. -/
mutual
  def OStage : ℕ → Type
    | 0 => PUnit
    | n+1 => PfNe (RStage n)
  def RStage : ℕ → Type
    | 0 => PUnit
    | n+1 => Sym2 (OStage n ⊕ RStage n)
end
-- (Verified: this mutual def elaborates as written against the pinned toolchain.
-- If a later edit upsets the equation compiler anyway, define
-- `Stage : ℕ → Type × Type` by one recursion and project.)

theorem stage_nonempty : ∀ n, Nonempty (OStage n) ∧ Nonempty (RStage n) := by
  sorry -- induction; singleton set for the O-step.

/-- ASC-NC — CONFIRMS P4: the relation sort never re-collapses. With both sorts
nonempty at stage n, `s(inl o, inl o) ≠ s(inl o, inr r)` at stage n+1 — the B1_C
separation, at every storey. The Mirror's collapse argument fails at every stage
of the terminal sequence. -/
theorem ascent_R : ∀ n, ¬ Subsingleton (RStage (n+1)) := by sorry

/-- HONESTY LEMMA (P4) — at depth 1 the object sort is still a point: O₁ = P⁺f(1) ≅ 1.
The depth-1 B1 pass of (C) is carried entirely by the relation sort; the object sort
inherits plurality one stage later (`ascent_O`). Kept so no reader mistakes B1_C for
more than it is. -/
theorem O1_subsingleton : Subsingleton (OStage 1) := by
  sorry -- PfNe of a subsingleton is a subsingleton: PfNe.subsingleton (Spec203b).

/-- ASC-NC — CONFIRMS P4 at the object sort, from stage 2 on: two distinct stage-1
relations give two distinct singleton patterns. -/
theorem ascent_O : ∀ n, ¬ Subsingleton (OStage (n+2)) := by sorry
```

**ASC-STRICT (SHOULD-strong; budget a half-day, FL-style drop clause).** Strict growth by mutual embeddings plus a fresh element:

```lean
/-- Stage embeddings: O and R each embed into the next stage (O-step: image of a
set under an injection, `Set.Finite.image` + `Set.image_injective`; R-step:
`Sym2.map (Sum.map · ·)` with injectivity — `Sym2.map.injective` and
`Function.Injective.sum_map`, both verified present in the pinned mathlib).
Base cases into the singleton stages. -/
def stageEmbed : ∀ n, (OStage n ↪ OStage (n+1)) × (RStage n ↪ RStage (n+1)) := sorry

/-- ASC-STRICT — CONFIRMS P5, the Ascent: every storey holds something fresh.
Induction: the base misses `s(inl ⋆, inr ⋆)`; and if r* at stage n+1 misses the
embed image, `s(inr r*, inr r*)` misses it at stage n+2 (an image element with both
components `inr` forces a preimage, contradiction). -/
theorem ascent_strict :
    ∀ n, ∃ z : RStage (n+1), z ∉ Set.range (stageEmbed n).2 := by sorry

/-- Stretch (drop freely with note): stage n carries at least n+1 relation-sort
elements — `Fin (n+1) ↪ RStage n` by composing embeddings with fresh elements.
Substantiates §5.3's "F(1) infinite" at the stage level; the limit's cardinality
is NOT decided here (honesty: an inverse limit of strictly growing finite stages
is not automatically infinite without further structure — that claim belongs to
the corrected-functor spec if it wants it). -/
theorem ascent_fin : ∀ n, Nonempty (Fin (n+1) ↪ RStage n) := by sorry
```

If the embedding plumbing exceeds budget: ship `ascent_R`/`ascent_O`/`O1_subsingleton` (the MUSTs), state strictness as a documented conjecture at the file's foot, record the drop. Do **not** reach for Fintype cardinalities as a rescue — the instance plumbing through a mutual recursion costs more than the embeddings.

**CTRL (SHOULD; cheap).** The contrast that gives the Ascent its meaning:

```lean
/-- Generalization of `G_unit_subsingleton` (Spec203): G preserves subsingletons —
G X is defeq to PfNe (Sym2 X), so `PfNe.subsingleton` applies. -/
theorem G_subsingleton_of (X : Type) [Subsingleton X] : Subsingleton (G X) := by sorry

/-- CTRL — CONFIRMS P6: the control's terminal sequence over the point is FLAT —
one point at every stage, forever. The collapsed functor does not merely fail F(1);
it fails at every depth, while (C) ascends. This is the discriminating power of the
stage checks, stated as a theorem. -/
theorem control_flat : ∀ n, Subsingleton ((G ·)^[n] PUnit) := by
  sorry -- induction over G_subsingleton_of; mind the iterate direction
        -- (Function.iterate_succ_apply' or unfold by hand).
```

## 6. Build, verify, deliver

Standard: clean build, no `sorry`, axiom audit (`#print axioms` block; BIT and the ASCENT MUSTs plausibly choice-light — report per theorem), gate green (`scripts/gate.sh` — repaired and live again as of this order's commit; `Spec203c` imports only `Spec203b`), registered as the tenth root in `lake/lakefile.toml`. Mapping table with the prediction-outcome column:

```
-- 2-03-mechanization-c §2 predictions ↔ outcomes (fill in: CONFIRMED / REFUTED / DROPPED-to-conjecture)
-- One bit:      A2_one_bit (+ A2_equiv_bool)    — P1                       → ____
-- Sym hazard:   tied_symm                        — P2                       → ____
-- Relocation:   relocation_realizes (directed)   — P3 / C-B6                → ____
-- Forgetting:   forgetAnatomy                    — C-B6 lattice             → ____
-- No re-collapse: ascent_R, ascent_O, O1_subsingleton — P4                  → ____
-- The Ascent:   ascent_strict (+ ascent_fin)     — P5                       → ____
-- Control flat: control_flat                     — P6                       → ____
-- Pairs check (O-2-03-2): discharged by B2_C_separation (Spec203b) — cited, not reproved.
```

Deviations recorded, as always.

## 7. DOC (MUST)

- `2-03.md`: append **§5.7 Results of the closing trials** (post-hoc-marked; this order's §2 predictions stay frozen as written), transcribing the outcome column; every REFUTED or DROPPED entry gets one honest sentence. If P3 confirmed: one sentence noting the hybrid clause stays closed and C-B6's lattice sentence is now proved, with direction bought by the tower's next storey. Update O-2-03-1b/O-2-03-2 statuses (delivered parts marked; the coherence design remains the open gate).
- `2-00.md` §5, T2's entry: one line — stage checks recorded (`Spec203c`): the tower never re-collapses and strictly ascends; relocation outcome noted.
- `2-02.md` §7: update the roadmap sentence — after this order, the remaining path is: **(C) coherence design (O-2-03-1b, spec-side) → corrected-functor spec with its D20 F(1) computation at the head → νF_C construction (Spec201c template) → B4/B5 against it → re-anchoring (2-03 §6) → S1 pigeonhole, T4, T7.**

---

*End of work order. This is the last mechanization the trials can support before design re-enters: after it, every question left open is a question about what (C) IS — its coherence, its parthood, its functor — and those answers belong in a spec with an F(1) computation at its head, per the discipline the Mirror bought. If P3 confirms, the arena's most striking property is already on record: the tower converts order into structure — direction without ordered pairs, anatomy without new atoms — which is A6 and D4 holding hands. If P3 refutes, the hybrid returns and the anatomy residue sharpens. Either way the battery, not the authors, decides.*
