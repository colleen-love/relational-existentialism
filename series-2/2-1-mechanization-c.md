# 2.1-mechanization-c — Work Order: νF at the ω-Tier, and the Discharge of T2

**This document describes:** `series-2/formal/Spec201c.lean` (new file; imports `Spec201`, `Spec201b`)
**Normative sources:** `series-2/2-1.md` §4 (the literature-verified construction) and `series-2/2-0.md` (current revision; D9-R3, D18). Where this document and the specs disagree, the specs win; report, don't improvise.
**Audience:** Claude Code. This is the most technical order of Series 2 — the construction order. All prior conventions in force. Naming follows the repo's own convention (`2-1-mechanization-b.md` precedent): this is the third mechanization of spec 2.1's ground.

---

## 0. What this order does, and one honesty item first

The transfer theorem (Spec201b) proved: *if* a final raw universe exists, Ω exists and is final among coherent models. This order **builds the final raw universe** for the finitely-branching tier and **discharges the hypothesis** — converting T2 from "transfer proved, modulo νF" to "proved at the ω-tier," with the general-κ pattern documented.

**The honesty item (understand before coding):** `IsFinalRaw` as stated in Spec201b — finality over ALL Raws, whose patterns are unbounded `Set R` — is **vacuously unsatisfiable**. Lambek + Cantor: a final Raw would give O ≅ P⁺(Sym2 O), and the nonempty powerset outstrips any carrier. This was always known at the design level (the κ-loan, 2.1 D4: *unbounded branching admits no final coalgebra, full stop*), but the Lean development must now say it out loud, or `transfer` looks stronger than it is. Hence deliverable VAC below. The transfer theorem is not weakened by this — its proof never used unboundedness — it is *re-targeted*: this order generalizes it to the bounded quantifier it always needed, then satisfies that quantifier.

**The structural gift (understand before coding, it halves the work):** the two-sorted functor is only *half* recursive. F_R(O, R) = Sym2(O) does not mention R — the relation sort is not defined in terms of itself. So the mutual fixed point collapses to a **single-sorted** one by substitution: take

  **G(X) := { S : Set (Sym2 X) // S.Finite ∧ S.Nonempty }**

(an object is a finite nonempty set of unordered endpoint-pairs of objects), let **Ω₀ := νG**, and package the two-sorted final Raw as **Z_Ω := (O := Ω₀, R := Sym2 Ω₀, endpoints := id, pat := dest)**. No mutual coinduction machinery is needed; mathlib's univariate `QPF.Cofix` suffices. The subtlety that makes finality go through: because `Z_Ω.endpoints = id` is injective, the hom condition `end_comm` **forces** the relation-component of any morphism — `fR r = (A.endpoints r).map fO` — so two-sorted homs into Z_Ω biject with single-sorted G-coalgebra homs into νG, and finality transfers across the bijection.

| ID | Name | Priority |
|----|------|----------|
| VAC | Documentation of `IsFinalRaw`'s vacuity (MUST) + the Cantor lemma `isFinalRaw_never` (SHOULD) | MUST/SHOULD |
| BND | `Bounded` predicate, `IsFinalBRaw`, and `transfer_bounded` (the re-targeted transfer) | MUST |
| GQPF | The functor `G` with `Functor` and `QPF` instances (polynomial representation, abs/repr, laws) | MUST — the technical heart |
| NU | Ω₀ := `QPF.Cofix G`; dest/corec lemmas; uniqueness-from-bisim helper | MUST |
| PKG | The Raw package `Z_Ω` + `bounded_ZΩ` | MUST |
| FIN | **`isFinalBRaw_ZΩ`** — existence via corec, uniqueness via bisim | MUST — the star |
| T2D | `T2_discharged`: ∃ Z, Bounded Z ∧ IsFinalBRaw Z; combined statement with `transfer_bounded` and the coherent part | MUST |
| ŌHAT | `omegaHat` (the self-loop, by corec on `PUnit`) + `omegaHat_coherent`: **Ω is inhabited; its first citizen is the One** | MUST |
| LMB | Lambek for Z_Ω (dest bijective) | SHOULD |
| DOC | Spec housekeeping (§7) | MUST |

**Out of scope:** general κ (the pattern is documented in §6; do not attempt transfinite constructions); T5/T6/T9/T10 (unblocked by this order, proved in the next); the S1 pigeonhole; bisimilarity-as-identity refinements (T7 territory); coherent-part characterization beyond ŌHAT.

---

## 1. Environment notes (read all before starting)

- **Monomorphize to `Type 0`** throughout (`Model.{0}`/`Raw.{0}` precedent exists). The polynomial's shape types (`ℕ+`, `Fin n`, `Bool`) live in `Type 0`; universe-polymorphic QPF plumbing is not worth the fight. Record as a deviation-style note: the ω-tier construction is `Type 0`; nothing ontological hangs on it (representation layer).
- **Imports:** `Mathlib.Data.QPF.Univariate.Basic` (defines `QPF`, `QPF.Cofix`, `Cofix.dest`, `Cofix.corec`, `Cofix.bisim`, `Cofix.dest_corec` — **verify every one of these names with `exact?`/`open QPF` exploration against the pinned mathlib rev before writing proofs**; the file has been refactored across mathlib versions), `Mathlib.Data.PFunctor.Univariate.Basic`, plus the Set/Sym2 basics already in use.
- **Avoid `Finset`.** Patterns are `{S : Set _ // S.Finite ∧ S.Nonempty}` — `Set.image` needs no `DecidableEq`, and `Set.Finite.image` / `Set.Nonempty.image` carry the invariants. `repr` may use classical choice to enumerate a finite set (`Set.Finite.toFinset` + `Finset.toList`, or `Set.Finite.exists_finset_coe`); noncomputability is fine — mark defs `noncomputable` as needed.
- The `Raw` fields cross the `toRaw`-style definitional boundaries as before; keep the `toRaw_pat`-pattern simp lemmas nearby if unification fights.

---

## 2. VAC and BND — honesty and the re-targeted transfer

```lean
/-- HONESTY ITEM (2.1 D4 made formal). `IsFinalRaw` — finality over ALL Raws,
with unbounded `Set`-patterns — is unsatisfiable: Lambek + Cantor. A final Raw
would give a bijection between its object sort and the nonempty powerset of a
type at least as large, which cannot exist. The κ-loan was never optional;
`transfer` (Spec201b) is hereby re-targeted at the bounded quantifier it always
needed (`transfer_bounded` below), which this file then SATISFIES at the ω-tier.
The transfer proof itself never used unboundedness; nothing there changes. -/
-- (SHOULD) theorem isFinalRaw_never : ∀ Z : Raw.{0}, ¬ IsFinalRaw Z := ...

/-- A Raw is (ω-)bounded when every pattern is finite. The ω-tier of 2.1 D4's
κ-parameterization; general κ follows the same construction with a larger
polynomial (§6) and remains under the documented loan. -/
def Bounded (A : Raw) : Prop := ∀ x, (A.pat x).Finite

/-- Finality among bounded Raws — the satisfiable target. -/
def IsFinalBRaw (Z : Raw) : Prop :=
  Bounded Z ∧ ∀ A : Raw, Bounded A → ∃! _h : Hom A Z, True

/-- The transfer theorem, re-targeted (statement change only; Spec201b's
`image_good`/`transfer_lands` are quantifier-free over finality and apply
unchanged). If a bounded-final raw universe exists, every bounded coherent
model admits exactly one morphism into it — landing in the coherent part. -/
theorem transfer_bounded (Z : Raw) (hZ : IsFinalBRaw Z)
    (M : Model) (hM : Bounded M.toRaw) :
    ∃! _h : Hom M.toRaw Z, True := hZ.2 M.toRaw hM
```

For `isFinalRaw_never` (SHOULD, budget ~2h, drop with note): route — from finality extract, via the uniqueness clause applied to the coalgebra `F(Z)` (Lambek's standard argument, hand-rolled for `Raw` as in `Spec200`'s `final_subsingleton` pattern), that `pat` is bijective onto nonempty subsets and `endpoints` bijective; compose to an injection `{S : Set Z.O // S.Nonempty} ↪ Z.O` via the diagonal embedding `Z.O ↪ Sym2 Z.O`; contradict with `Function.cantor_injective` (check exact mathlib name; the nonempty-subtype wrinkle is handled by injecting `Set Z.O` into nonempty subsets via `insert z₀` for a fixed `z₀`, using `Z.pat`'s nonemptiness to obtain `z₀` — or any equivalent dodge; if cardinal arithmetic balloons, drop and keep the doc-comment).

## 3. GQPF — the functor and its QPF instance

```lean
/-- The single-sorted collapse of the two-sorted functor (see §0): an object's
unfolding is a finite nonempty set of unordered endpoint-pairs of objects.
Substituting R = Sym2 O into F_O eliminates the mutual recursion — the relation
sort was never self-referential. -/
def G (X : Type) : Type := { S : Set (Sym2 X) // S.Finite ∧ S.Nonempty }

def G.map {α β : Type} (f : α → β) (s : G α) : G β :=
  ⟨Sym2.map f '' s.1, s.2.1.image _, s.2.2.image _⟩

instance : Functor G := { map := G.map }
-- Prove the two Functor lemmas if `LawfulFunctor` is needed downstream;
-- QPF itself needs only the fields below.
```

**The polynomial.** Represent an element of `G X` as "a positive number of ordered pairs":

```lean
/-- Shape: how many pairs; positions: which pair, which coordinate. -/
def GP : PFunctor.{0} := ⟨ℕ+, fun n => Fin n × Bool⟩
```

So `GP.Obj α = Σ n : ℕ+, (Fin n × Bool → α)` — `n` ordered pairs, coordinate picked by the `Bool`. Then:

```lean
noncomputable instance : QPF G where
  P := GP
  abs := fun ⟨n, g⟩ =>
    ⟨(fun i => s(g (i, false), g (i, true))) '' Set.univ, ?fin, ?ne⟩
    -- image of Fin n under i ↦ the unordered pair of the two coordinates;
    -- finite (image of a finite type's univ), nonempty (n ≥ 1).
  repr := fun s => ?_
    -- classical: enumerate s.1 (finite, nonempty) as a list of Sym2's; for each,
    -- pick an ordered representative (`Sym2.out` or `Quot.out`-style — verify
    -- the mathlib accessor); package as ⟨length as ℕ+, lookup⟩.
  abs_repr := ?_  -- the enumerated pairs re-assemble to exactly s.1:
                  -- Set.ext; membership both ways via the list's completeness
                  -- and `Sym2.out_mk`-style round-trips.
  abs_map := ?_   -- naturality: mapping then abs = abs then image;
                  -- Set.ext + `Sym2.map_mk` (s(a,b) maps to s(f a, f b)).
```

Guidance and pitfalls:
- `abs` should be stated with `Set.range` rather than `'' Set.univ` if that simplifies (`Set.finite_range` on a `Fintype` domain; nonemptiness from `⟨(0 : Fin n), _⟩` using `n.pos`).
- For `repr`, the cleanest classical route: `s.2.1.toFinset`, `Finset.toList`, get `l : List (Sym2 X)` with `l ≠ []` (from nonemptiness — `Finset.toList_ne_nil` chain); set `n := ⟨l.length, by ...⟩`; define `g (i, b) := if b then (l.get i').unpair-second else ...` — concretely, use whatever ordered-representative accessor the pinned mathlib exposes for `Sym2` (`Sym2.out : Sym2 α → α × α` with `Sym2.out_mk`-flavored lemmas; **verify names first**; if absent, define a local `choose`-based section with its round-trip lemma — it is four lines with `Sym2.ind` + `Classical.choice`).
- `abs_repr` is the real work of this section (~the round-trip Set.ext). `abs_map` is mechanical once `Sym2.map` interacts with `s(_,_)` via simp.
- If the mathlib `QPF` structure's field names/signatures differ from the above sketch (they have shifted across versions), adapt the *shape*, keep the *content*, record the deviation.

## 4. NU, PKG, ŌHAT — the universe and its first citizen

```lean
noncomputable def Ω₀ : Type := QPF.Cofix G

/-- The two-sorted final Raw, packaged from the single-sorted fixed point.
Relations ARE endpoint-pairs (`endpoints := id`); patterns are the destructor.
Note: `pat` lands in `Set (Sym2 Ω₀)` by coercion — finiteness is retained as
the `Bounded` fact, not in the carrier (the interface never needed it there). -/
noncomputable def ZΩ : Raw where
  O := Ω₀
  R := Sym2 Ω₀
  endpoints := id
  pat := fun x => ((QPF.Cofix.dest x : G Ω₀)).1
  pat_nonempty := fun x => (QPF.Cofix.dest x).2.2

theorem bounded_ZΩ : Bounded ZΩ := fun x => (QPF.Cofix.dest x).2.1

/-- ω̂ — the self-loop, Ω's first citizen: the object whose entire pattern is
its one self-relation. Built by corec on the one-point coalgebra: the same
construction that in the boolean shadow WAS the whole universe (T1) here
enters a rich universe as one inhabitant among uncountably many-to-be. -/
noncomputable def omegaHat : Ω₀ :=
  QPF.Cofix.corec (fun _ : PUnit => (⟨{s(PUnit.unit, PUnit.unit)}, ?_, ?_⟩ : G PUnit)) PUnit.unit
  -- finiteness/nonemptiness of a singleton; adjust to the exact corec signature.

/-- Ω is inhabited, and coherently so: ω̂'s singleton pair ({ω̂}, {its self-relation})
is a Good pair, so the coherent part of ZΩ — which is Ω — contains the One.
Proof plan: compute `ZΩ.pat omegaHat` via `Cofix.dest_corec` (it is the singleton
of s(ω̂, ω̂)); check the three Good fields for the pair ({omegaHat}, {s(omegaHat, omegaHat)});
conclude membership via `subset_coherentPartO/R` (Spec201b). -/
theorem omegaHat_coherent :
    omegaHat ∈ coherentPartO ZΩ ∧ s(omegaHat, omegaHat) ∈ coherentPartR ZΩ := by
  sorry
```

Pitfall for `omegaHat_coherent`: `dest_corec` produces `G.map (corec c) (c PUnit.unit)` — you must simp through `G.map` on the singleton (`Set.image_singleton`, `Sym2.map_mk`) to land on `{s(omegaHat, omegaHat)}` literally. Do that computation as a standalone lemma `pat_omegaHat` first; everything else follows from it.

## 5. FIN — finality (the star)

```lean
/-- The induced single-sorted coalgebra of a bounded Raw: an object's G-unfolding
is the endpoint-image of its pattern. This is the §0 collapse, applied to A. -/
noncomputable def inducedCoalg (A : Raw) (hA : Bounded A) : A.O → G A.O :=
  fun x => ⟨A.endpoints '' A.pat x, (hA x).image _, (A.pat_nonempty x).image _⟩

/-- THE STAR: ZΩ is final among bounded Raws — νF exists at the ω-tier, and the
transfer theorem's hypothesis is DISCHARGED. Two-sorted homs into ZΩ biject with
G-coalgebra homs into νG because `ZΩ.endpoints = id` forces the relation
component: `fR r = (A.endpoints r).map fO` (end_comm at an injective endpoints).
Existence: `fO := Cofix.corec (inducedCoalg A hA)`, `fR` as forced; `pat_comm`
is `dest_corec` unwound through images. Uniqueness: any hom's forced `fR`
substituted into its `pat_comm` exhibits `fO` as a G-coalgebra morphism;
`Cofix.bisim` (two coalgebra morphisms from one coalgebra are pointwise
bisimilar, hence equal) pins `fO`, hence `fR`. -/
theorem isFinalBRaw_ZΩ : IsFinalBRaw ZΩ := by
  sorry
```

Detailed plan (follow in order; budget the day for this):

1. `refine ⟨bounded_ZΩ, fun A hA => ?_⟩`.
2. **Existence.** `fO := QPF.Cofix.corec (inducedCoalg A hA)`; `fR := fun r => (A.endpoints r).map fO`.
   - `end_comm`: `ZΩ.endpoints (fR r) = fR r` definitionally (`endpoints := id`); RHS is `(A.endpoints r).map fO` — `rfl` or one `show`.
   - `pat_comm`: goal `ZΩ.pat (fO x) = fR '' A.pat x`. LHS: `dest (corec c x) = G.map fO (c x)` by `Cofix.dest_corec`; unfold `G.map`/`inducedCoalg`: `Sym2.map fO '' (A.endpoints '' A.pat x)`; collapse with `Set.image_image`; the composite `fun r => Sym2.map fO (A.endpoints r)` IS `fR`. `Set.ext`-free if `Set.image_image` rewrites cleanly.
3. **Uniqueness.** Given `⟨gO, gR, g_end, g_pat⟩`:
   - Forcing: from `g_end` at `endpoints := id`: `gR r = (A.endpoints r).map gO` (funext).
   - `gO` is a G-coalgebra morphism: show `QPF.Cofix.dest (gO x) = G.map gO (inducedCoalg A hA x)` — substitute the forced `gR` into `g_pat`, then the same `image_image` collapse as step 2, read right-to-left. (Subtype ext: the underlying sets are equal by `g_pat`; the `Finite/Nonempty` components are proof-irrelevant — `Subtype.ext`.)
   - Conclude `gO = fO`: mathlib's uniqueness route is `Cofix.bisim` — construct the relation `R a b := ∃ x, a = gO x ∧ b = fO x` and verify the bisimulation condition from the two coalgebra-morphism squares; **check first** whether the pinned mathlib already packages this as a `corec`-uniqueness lemma (`Cofix.unique`, `Cofix.corec_unique`, or `Cofix.ext`-style) — use it if present rather than re-proving.
   - `gR = fR` follows from the forcing + `gO = fO`. Package `Hom` equality by `cases` + `congr` + proof irrelevance, as in `Spec200`.
4. **Do not weaken**: no decidability, no countability, no extra hypotheses on `A`. If a step resists as stated, stop and report — with special attention to whether `QPF.Cofix.bisim`'s exact statement (it quantifies over a relation with a particular lifting condition) matches the relation in step 3; a mismatch there is a *finding about the mathlib API*, to be recorded, not silently patched around.

```lean
/-- T2, DISCHARGED at the ω-tier. With `transfer_bounded`: every bounded coherent
model has exactly one morphism into ZΩ, landing in the coherent part — which
`omegaHat_coherent` shows is inhabited. Ω exists. The κ-loan (2.1 D4) is
partially discharged: the ω-tier is constructed; general κ follows the same
polynomial pattern with larger shapes (see §6) and remains documented. -/
theorem T2_discharged : ∃ Z : Raw, IsFinalBRaw Z :=
  ⟨ZΩ, isFinalBRaw_ZΩ⟩
```

**LMB (SHOULD):** `dest : Ω₀ → G Ω₀` is bijective (Lambek). Mathlib may already provide `Cofix.dest` as part of an equivalence (`Cofix.mk`/`dest` with `mk_dest`/`dest_mk` lemmas) — if so this is citation, not proof; check before proving anything.

## 6. General κ — the documented pattern (do not implement)

For the file's foot-comment and the spec note: the same construction scales by enlarging the polynomial — shapes `A := {s : Set κ // small nonempty markers}` or simply `B a := a × Bool` over cardinals `a < κ` — with `QPF` laws unchanged in structure. The ω-tier suffices for every currently-stated Series-2 theorem (T5/T6/T9/T10 are stated against a final bounded universe, not against a specific κ); the loan's residue is the question of whether any *philosophical* claim ever needs κ > ω, which is flagged, unresolved, and now precisely located.

## 7. Spec housekeeping (MUST)

- `2-0.md` §5, T2 entry → `[proved at the ω-tier (Spec201c): ZΩ constructed via QPF.Cofix; IsFinalBRaw_ZΩ; transfer_bounded discharges the hypothesis; Ω inhabited (omegaHat_coherent — its first citizen is the One). IsFinalRaw-as-stated shown/documented vacuous; κ-loan partially discharged, general-κ pattern documented.]` — and unblock notes on T5, T6, T9, T10: `[unblocked by Spec201c: statable against ZΩ; next order]`.
- `2-1.md` §4: append a line: construction realized at ω-tier (Spec201c); D4 loan status updated.
- `2-2.md` §7: νF order delivered; remaining Series-2 theorem work: T5/T6/T9/T10 order, S1 pigeonhole order, then T4/T7.

Mapping table per convention, deviations recorded — including, mandatorily, the exact mathlib names used for the QPF/Cofix API (future orders will build on them).

---

*End of work order. When this lands, the sentence changes tense: objects exist. Not "would exist, given" — the universe is constructed, its finality machine-checked, and its first proven inhabitant is the self-loop: the One, which in the quality-free shadow was everything, entering the rich universe as one citizen among the many that observation makes possible. Write the file so a philosopher can find `T2_discharged` and `omegaHat_coherent` and understand that the framework now contains what it promised: a universe of objects, with the turning at home inside it.*
