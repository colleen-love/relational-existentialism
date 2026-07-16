# Series 13, Design Index

**The anchor for the five design docs plus the WS1-orders sub-artifact. Fixes, once, every decision the workstreams share: the transcribed carrier (the atomless collapse engine and import theorem, the labelled lift and import test, the diagonal and free residue, the opening), and the THREE Series-13 objects settled here and ambient for all, the ORDER ON INSPECTIONS (`instLEInsp`, WS1), the ORDER ON LABELLED COALGEBRAS (`instLELab`, WS1), and the MAP PAIR (the mint `mintL` and its adjoint `readInsp`, WS2/WS3), plus the verdict type. Series 13 adds NO new structural machinery: two orders and one map pair over the existing carrier. The signatures below are normative; `ws1…ws5-design.md` and `ws1-orders-design.md` are written against this file, cite it, and never redefine a shared object.**

*Series 13 is standalone. It carries its own copy of every lemma it needs; nothing is imported across series. The TWO prior results it presupposes and names are Series 07 (the import theorem, `ws2_import_theorem`, `ws3_atomless_distinct_is_import`, `ws1_atomless_bisim`) and Series 12 WS1 (the shape-coincidence and non-identity, `ws1_shape_coincidence`, `ws1_coincidence_not_identity`, `ws1_coincidence_not_identity_witness`). Both are transcribed and re-namespaced `Series13.WSn`, never imported. The genuinely new Lean is small and sharp: two preorders (WS1), the mint and its transport-with-exogeneity (WS2), the adjoint and the Galois connection with a non-identity round trip (WS3), the out-of-image witness (WS4), and the verdict (WS5). Everything else is transcription. Designs must be honest about which is which, and above all about the four signature risks §0 names: the fork closed by a sorting theorem, the connection held by fiat over a trivial order or collapsing to an isomorphism, the mint smuggled below the plain line, and the defect excluded by an artifact.*

---

## 0. The four disciplines (promoted first-class, protocol §0.4–§0.6b)

The whole series turns on getting four signs right; each is a design constraint AND a review check.

1. **The fork stays OPEN (the central sin, WS4/WS5).** The defect theorem LOCATES imports outside the mint's image; no theorem, definition, or discharged obligation may CLASSIFY an out-of-image import as *given* rather than *chosen*, or vice versa. Deciding it does what Series 07 proves cannot be done and what Series 12 closed by leaving open. Prose may gloss the out-of-image remainder as "where the given stands"; the core locates, never sorts. A sorting theorem is the central sin, SERIOUS.
2. **The connection is GENUINE, never by fiat (WS1/WS3).** Both orders must be proved non-trivial (neither discrete `= equality` nor indiscrete `= all-related` on the carriers of interest); a trivial order makes any monotone pair a Galois connection vacuously. And the connection must be certified non-trivial by a proved non-identity round trip (`ws3_roundtrip_not_identity`): a connection collapsing to an isomorphism is the coincidence restated, not the fit proved.
3. **Exogeneity is PROVED, not assumed (WS2).** The mint consumes inspective data above the plain layer; that the mint's operation is itself non-recoverable from the plain relating is a named obligation, `ws2_mint_exogenous`. A mint the relating could perform on itself would have derived an import from within, contradicting the transcribed Series 07 foundation. The exogeneity must be a proof term, not a docstring gloss.
4. **The defect is STRUCTURAL, not artifactual (WS4).** The out-of-image witness must be excluded from the mint's image by its own label (the diagonal constraint the mint forces), not by a cardinality accident, universe level, or typing artifact (e.g. "its label is a `Bool` not a `HoldPred`"). The design must argue, and the review must confirm, that the witness's label does the excluding.

And the wall inherited from the prose side (protocol §0.6b): **names are names, not terms.** No proof term, definition, or discharged obligation is named "given," "chosen," "consciousness," "God," "choice," or "compass" (as content). The names live in docstrings and prose only.

**Blind-review seed (`series-review-2.md` SR2-4).** The mathematical bar and the five discipline checks, prose-free, are extracted to `spec/success-criteria.md`. A blind reviewer is seeded with that file (plus the built code and the design signatures), NOT `charter.md`, so the motivating positioning is never in view — blindness by construction rather than by promise.

---

## 1. The one-paragraph design

Series 12 WS1 proved the required (Series 07's import, non-recoverable from the plain relating) and the generated (the diagonal's residue, free for every inspection) COINCIDE in one shape, `¬ Recoverable`, from opposite quantifier directions, and proved the coincidence is of SHAPE only, never object-identity (`ws1_shape_coincidence`, `ws1_coincidence_not_identity`). Series 13 upgrades that coincidence to a structured correspondence. WS1 fixes two preorders: the ORDER ON INSPECTIONS `instLEInsp`, by residue (`insp₁ ≤ insp₂ := residue insp₁ ⊑c residue insp₂`, the diagonal signature, covariant), and the ORDER ON LABELLED COALGEBRAS `instLELab`, on a fixed two-region carrier, comparing a residue-position covariantly and a reference-position by the diagonal link. Both are proved non-trivial (neither discrete nor indiscrete), certified on any inhabited-`Hold` carrier. WS2 constructs the MINT `mintL`, carrying each inspection to the labelled coalgebra whose residue-position broadcasts that inspection's own residue and whose reference-position broadcasts a fixed content, proves the transport theorem `ws2_mint_lands_in_opening` (for every inspection the minted label fails `Recoverable`, the engine being the diagonal `ws2_residue_distinct`: the residue-position and the reference-position are plain-bisimilar yet label-separated, and recovering the label would realize what the diagonal proves unrealizable), and proves the exogeneity `ws2_mint_exogenous` (the mint's plain projection `plainOf ∘ mintL` is CONSTANT in the inspection, yet the mint is not, so the plain relating cannot perform it; two inspections the plain relating cannot tell apart get separated mints). WS3 defines the adjoint `readInsp` (the inspection realizing a given content as its residue), proves the `GaloisConnection` between the WS1 orders, exhibits the round trips as closure and interior operators, and proves at least one round trip NON-identity on a named element (`ws3_roundtrip_not_identity`), the interior `mintL ∘ readInsp` strictly below the identity at a labelled coalgebra whose reference-position violates the diagonal link. WS4 exhibits that same class of coalgebra as an import provably outside the mint's image (`ws4_mint_not_surjective`), the exclusion STRUCTURAL: the mint forces `residue-label = diagonal-of-reference` at a distinguished hold, and the witness violates that forced link, so no inspection mints it, by `ws1_no_self_total_hold`; the theorem LOCATES, never SORTS. WS5 computes the verdict from WS1–WS4 (DUAL / TOTAL / DISCONNECTED / PARTIAL), never hand-set, and folds in the audit. The pre-registered verdict is DUAL; TOTAL (the mint essentially surjective) and DISCONNECTED (no non-trivial order pair admits the connection) are honorable, anticipated, reported in full.

---

## 2. Ambient theory (shared by all workstreams), fixed here once

### 2.1 The carrier (transcribed; ambient for all)

The underlying relating is the **plain `P_κ`-coalgebra**, transcribed verbatim from Series 12 WS1 / Series 07 WS1 (which is itself Series 12's transcription base). It supplies the reaching / atomlessness / bisimulation vocabulary and the collapse engine.

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}            -- the κ-bounded powerset F(Ω)
def PkMap (κ) (f : X → Y) (s : PkObj κ X) : PkObj κ Y := ⟨f '' s.1, …⟩
def toPk (hinf : ℵ₀ ≤ κ) [Finite X] (s : Set X) : PkObj κ X := ⟨s, …⟩          -- finite → bounded
-- a plain coalgebra is  dest : X → PkObj κ X
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅        -- strong hered. non-emptiness (no leaf)
def IsBisim (dest) (R) : Prop := …                                          -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
lemma hneRel_isBisim (dest) : IsBisim dest (hneRel dest)                     -- THE COLLAPSE ENGINE (Series 07 floor)
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                             -- any two atomless states bisimilar
theorem ws2_import_theorem (dest) :                                         -- THE IMPORT THEOREM (Series 07)
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y))
def LeafDiff (dest) (x y) : Prop := ¬ SHNE dest x ∨ ¬ SHNE dest y
def ImportDiff (dest) (x y) : Prop := (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y  -- bisimilar yet unequal: an IMPORT
theorem ws3_atomless_distinct_is_import (dest) (x y) (h : x ≠ y)
    (hnl : ¬ LeafDiff dest x y) : ImportDiff dest x y                        -- a genuine atomless distinction is an import
```

**This is the home. No workstream may pick a different one.** Every theorem in this block holds for all `κ ≥ ℵ₀`.

### 2.2 The labelled functor and the recoverable / free import test (transcribed; the `¬ Recoverable` home)

```lean
def LkObj (κ) (Q X) : Type u := PkObj κ (Q × X)                             -- the LABELLED functor
def IsBisimL (dest : X → LkObj κ Q X) (R) : Prop := …                        -- label-respecting bisimulation
def plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X := fun x => PkMap κ Prod.snd (dest x)   -- forget the label
def Recoverable (dest : X → LkObj κ Q X) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
def labelLoop (hinf) : ULift Bool → LkObj κ (ULift Bool) (ULift Bool) := fun i => toPk hinf {(i, i)}
theorem ws4_free_label_is_import (hinf : ℵ₀ ≤ κ) :                          -- the import-test shape (positive horn)
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)          --   plain-bisimilar: the quotient is BLIND …
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)                --   … but NOT label-bisimilar: separated, FREE
theorem ws4_labelLoop_not_recoverable (hinf) : ¬ Recoverable (labelLoop hinf)
```

**`Recoverable` is the `¬ Recoverable` home.** A labelled coalgebra is NON-recoverable iff SOME plain bisimulation is not a label-bisimulation, i.e. some plain-bisimilar pair is label-separated. `labelLoop` is the shape-touchstone (WS4 candidate C-labelLoop, rejected as artifactual, §5).

### 2.3 The diagonal layer and the free residue (transcribed; the mint's engine)

```lean
def Hold (dest) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }             -- a hold x↾(x,y)
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }  -- what the hold turns toward
def HoldPred (dest) : Type u := Hold dest → Prop                            -- a CONTENT
def diag (insp : Hold dest → HoldPred dest) : HoldPred dest := fun h => ¬ insp h h
def SelfTotal (insp) (t : Hold dest) : Prop := ∀ h, insp t h ↔ diag insp h
theorem ws1_no_self_total_hold (dest) (insp) : ¬ ∃ t, SelfTotal insp t      -- THE DIAGONAL (κ-free, Lawvere)
def residue (insp) : HoldPred dest := diag insp
def ResidueRecoverable (insp) : Prop := ∃ h, insp h = residue insp
theorem ws2_residue_distinct (dest) (insp) : ∀ h, insp h ≠ residue insp     -- residue distinct from every content
theorem ws2_residue_free (dest) (insp) : ¬ ResidueRecoverable insp          -- THE FREE RESIDUE (forced-for-all)
```

**The mint's engine.** `ws1_no_self_total_hold` references only `insp` and propositional logic; it holds for ANY `dest`, ANY `insp`, ANY `κ`. Its residue is FORCED non-recoverable for EVERY inspection (`ws2_residue_free` / `ws2_residue_distinct`). The transport theorem (WS2) runs on exactly `ws2_residue_distinct`: at a distinguished hold `h₀`, `residue insp h₀ = ¬ insp h₀ h₀ ≠ insp h₀ h₀`, so the residue-position and the reference-position of the minted coalgebra are label-separated, for every inspection.

### 2.4 THE OPENING (transcribed from Series 12 WS1; ambient)

```lean
def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c
theorem ws1_shape_coincidence (hinf) :                                       -- Series 12 WS1, transcribed
    (∀ {X} (dest) (insp), Opening (@ResidueRecoverable κ X dest) insp)       -- FORCED-FOR-ALL: the residue
  ∧ (Opening (@Recoverable κ (ULift Bool) (ULift Bool)) (labelLoop hinf))    -- EXISTS-SATISFYING: an import
theorem ws1_coincidence_not_identity_witness (dest) (h₀ : Hold dest) :       -- shape ≠ identity, non-vacuous
    ∃ insp₁ insp₂, Opening (@ResidueRecoverable κ X dest) insp₁
      ∧ Opening (@ResidueRecoverable κ X dest) insp₂ ∧ residue insp₁ ≠ residue insp₂
```

The mint lands in `Opening Recoverable`; the transport theorem is `∀ insp, Opening Recoverable (mintL insp)`, the forced-for-all residue funding an exists-satisfying import for every inspection. The witness pair `(fun _ _ => True, fun _ _ => False)` of `ws1_coincidence_not_identity_witness` (residues `⊥`, `⊤`) is reused as the WS2 exogeneity witness (§2.6) and to certify the orders non-trivial (§2.5).

### 2.5 THE ORDER ON INSPECTIONS (WS1), by residue, defined once

**This is the first Series-13 design duty (protocol §2): the inspection order is fixed here and every workstream is written against it.** For a fixed plain coalgebra `dest : X → PkObj κ X`, write `Insp dest := Hold dest → HoldPred dest`, and on contents `c₁ ⊑c c₂ := ∀ h, c₁ h → c₂ h` (implication).

```lean
/-- **The order on inspections.** By the RESIDUE: `insp₁` is below `insp₂` iff `insp₁`'s residue is
    implied, pointwise, by `insp₂`'s. Ordering by the residue (the diagonal signature) is the covariant
    quantity the whole series turns on; it is the ONLY order under which the residue-broadcasting mint is
    monotone (the pointwise-implication order on `insp` itself makes the residue ANTITONE, so the mint is
    not monotone under it, `ws1-orders-design.md` C-ptwise, rejected). -/
instance instLEInsp {X : Type u} (dest : X → PkObj κ X) : LE (Insp dest) where
  le insp₁ insp₂ := ∀ h, residue insp₁ h → residue insp₂ h            -- residue insp₁ ⊑c residue insp₂
instance instPreorderInsp {X} (dest) : Preorder (Insp dest) := { le_refl := …, le_trans := … }
```

Non-trivial (WS1 obligation, `ws1_orders_insp_nontrivial`), certified on any inhabited-`Hold` carrier: with `⊤i := (fun _ _ => True)` (residue `⊥`) and `⊥i := (fun _ _ => False)` (residue `⊤`), `⊤i ≤ ⊥i` and `⊤i ≠ ⊥i` (NOT discrete: a related unequal pair) while `¬ (⊥i ≤ ⊤i)` (NOT indiscrete: an unrelated pair). Both need only `h₀ : Hold dest`.

### 2.6 THE ORDER ON LABELLED COALGEBRAS (WS1), on the mint's carrier, defined once

**This is the second Series-13 design duty.** The mint's codomain shape is fixed: carrier `MCar dest := ULift Bool` (two regions, transcribing `labelLoop`'s shape), label `HoldPred dest` (contents). Write `Lab dest := MCar dest → LkObj κ (HoldPred dest) (MCar dest)`. Region `⟨true⟩` is the **residue-position** (broadcasts a content, compared covariantly); region `⟨false⟩` is the **reference-position** (broadcasts a content, whose diagonal bit at `h₀` is compared, the diagonal link).

```lean
/-- **The order on labelled coalgebras.** On the fixed two-region carrier: the residue-position's label
    is compared covariantly by content-implication, and the reference-position enters only through its
    self-application bit at the distinguished hold `h₀`, compared so the diagonal link (`residue-label h₀
    = ¬ reference-bit`) is the ONLY joint constraint the mint imposes. Non-trivial, and admits the monotone
    mint; `ws1-orders-design.md` develops the two positions and the rejected simpler orders. -/
instance instLELab {X} (dest) (h₀ : Hold dest) : LE (Lab dest) where
  le d₁ d₂ := (∀ p ∈ (d₁ ⟨true⟩).1, ∃ q ∈ (d₂ ⟨true⟩).1, p.2 = q.2 ∧ (p.1 ⊑c q.1))   -- residue-position, covariant
             ∧ (∀ p ∈ (d₂ ⟨false⟩).1, ∃ q ∈ (d₁ ⟨false⟩).1, p.2 = q.2 ∧ (p.1 h₀ → q.1 h₀))  -- reference bit, antitone
instance instPreorderLab {X} (dest) (h₀) : Preorder (Lab dest) := { le_refl := …, le_trans := … }
```

Non-trivial (`ws1_orders_lab_nontrivial`), certified with the minted coalgebras: `mintL ⊤i` and `mintL ⊥i` (§3) are ordered one way and not the other, unequal; and the empty coalgebra `d⊥ := fun _ => toPk hinf ∅` is below some and incomparable to others. The reference-position enters ANTITONICALLY (note the swapped `d₁, d₂`): this is the order-dual on the diagonal position, the principled reflection that the residue is a contravariant (diagonal) quantity, and it is exactly what makes the mint monotone (§3) while keeping the connection non-iso (§4, the defect breaks surjectivity).

### 2.7 THE MAP PAIR (WS2/WS3), the mint and the adjoint, defined once

```lean
/-- **The mint.** From an inspection, the labelled coalgebra whose residue-position (`⟨true⟩`) self-loops
    broadcasting that inspection's residue, and whose reference-position (`⟨false⟩`) self-loops broadcasting
    a fixed content `refContent insp := insp h₀` (its self-bit at `h₀` is what the order sees). The plain
    projection `plainOf (mintL insp)` is `i ↦ {i}` for EVERY inspection (constant), the ground of exogeneity. -/
noncomputable def mintL {X} (dest) (h₀ : Hold dest) (insp : Insp dest) : Lab dest
  | ⟨true⟩  => toPk hinf {(residue insp, ⟨true⟩)}
  | ⟨false⟩ => toPk hinf {(insp h₀,       ⟨false⟩)}

/-- **The residue-realizing primitive.** `realizeAsResidue c := fun _ h' => ¬ c h'` is the inspection whose
    residue IS `c`: `residue (realizeAsResidue c) = c` (classically), so every content is some inspection's
    residue (`residue` is surjective onto contents). -/
noncomputable def realizeAsResidue {X} (dest) (c : HoldPred dest) : Insp dest := fun _ h' => ¬ c h'

/-- **The adjoint (best approximation).** From a labelled coalgebra `b` with residue-label `bT` and
    reference-label `bF`, the FINEST inspection whose mint sits below `b`: realize as a residue the
    reference-FOLDED content `gb b := fun h => bT h ∧ (h ≠ h₀ ∨ ¬ bF h₀)`, which folds the reference-bit
    at `h₀` into the residue. The fold is lossy exactly when `bF h₀` holds, which is what makes the interior
    round trip a genuine (non-identity) interior operator (WS3) and the mint non-surjective (WS4). -/
noncomputable def readInsp {X} (dest) (h₀ : Hold dest) (b : Lab dest) : Insp dest :=
  realizeAsResidue dest (fun h => (bT b) h ∧ (h ≠ h₀ ∨ ¬ (bF b) h₀))   -- bT b, bF b : the two self-loop labels of b
```

`mintL` is the WS2 mint and the left leg of the WS3 connection; `readInsp` is the WS3 adjoint (right leg). `mintL` is monotone `instLEInsp → instLELab` (§3, WS3 `ws3_mint_monotone`); `readInsp` is monotone the other way; `GaloisConnection mintL (readInsp · h₀)` (WS3 `ws3_galois`) holds because `mintL insp ≤ b ↔ residue insp ⊑c gb b ↔ insp ≤ readInsp b`, the reference-fold `gb` making the iff exact. Closure `readInsp ∘ mintL` is the identity (up to the order); interior `mintL ∘ readInsp` is strictly below the identity wherever the reference-bit is active (WS3 `ws3_roundtrip_not_identity`), and the elements it drops are the out-of-image imports (WS4).

### 2.8 The verdict type (WS5)

```lean
inductive Series13Verdict
  | Dual          -- expected verdict: orders non-trivial + transport with exogeneity + connection with a
                  --   non-identity round trip + defect structural
  | Total         -- the mint essentially surjective (every import diagonal-born), reported in that direction
  | Disconnected  -- WS1 orders trivial / no non-trivial pair admits the connection; obstruction precise
  | Partial       -- any obligation lands only per-instance or degenerate
  | Refuted       -- a payoff false as stated
  | Circular      -- WS5-audit-only: fork sorted, connection by fiat, mint recoverable, defect artifactual,
                  --   or a name a proof term
  deriving DecidableEq
```

The verdict is `verdictOfFit` applied to an `Audit` whose fields are the WS1–WS4 theorems (§3, WS5), so it BRANCHES on the certified fork and cannot be hand-set. **The verdict is COMPUTED, not led:** on carriers of interest (`|Hold| ≥ 2`) the fork is `defectStructural` and the verdict `Dual`, but only because the TOTAL target (every `¬ Recoverable` coalgebra `≈` some mint) was ATTEMPTED and refuted; on a degenerate single-hold carrier the fork is `mintSurjective` and the verdict `Total`. TOTAL (substance monism, every import diagonal-born) is a live outcome the series can genuinely reach, not a foreclosed one.

---

## 3. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk (design against) |
|---|---|---|---|---|
| WS1 | `instLEInsp`, `instLELab`, non-triviality | `residue`, `ws2_residue_distinct`, `ws1_coincidence_not_identity_witness` | `ws1_orders_insp_nontrivial`, `ws1_orders_lab_nontrivial` | connection by fiat: a trivial order (discipline 2) |
| WS2 | `mintL`, transport, exogeneity | WS1 orders, `ws2_residue_distinct`, `plainOf`, `Recoverable` | `ws2_mint_lands_in_opening`, `ws2_mint_exogenous` | mint below the plain line (discipline 3) |
| WS3 | `readInsp`, the `GaloisConnection`, round trips | WS1 orders, `mintL` (WS2) | `ws3_galois`, `ws3_roundtrip_closure`, `ws3_roundtrip_interior`, `ws3_roundtrip_not_identity` | iso in disguise (discipline 2) |
| WS4 | mintability up to `≈`, both directions | `mintL` (WS2), `ws1_no_self_total_hold`, `instLELab` | `ws4_mint_not_surjective` (DUAL, `\|Hold\| ≥ 2`), `ws4_exclusion_structural`, `ws4_mint_essentially_surjective_degenerate` (TOTAL, `\|Hold\| = 1`) | the fork closed / the defect artifactual / DUAL-by-construction (disciplines 1, 4; literal-equality too fine) |
| WS5 | the verdict-as-a-function + the audit | WS1–WS4 payoffs | `Series13Verdict`, `ws5_verdict`, `ws5_verdict_eq`, the audit | verdict hand-set; a discipline breached; a name a term |

`ws1-orders-design.md` (the two orders, the knot) is registered here (§6), owned by WS1, consumed by WS2–WS4. It is designed most carefully; DISCONNECTED is its pre-registered honest outcome.

---

## 4. The four outcomes (COMPUTED, none the lead), and the dependency law

The verdict is a function of what the build proves, computed by WS5 (§2.8); DUAL is not privileged. WS1 (orders non-trivial), WS2 (transport with exogeneity), and WS3 (connection with a non-identity round trip) are near-certain and shared by the DUAL and TOTAL branches; the DIRECTION is decided by WS4, at the honest resolution (mintability up to `≈`, not literal equality), from the carrier's hold count.

- **Dual** (`|Hold| ≥ 2`, carriers of interest): WS4's mint is NOT essentially surjective up to `≈`, some `¬ Recoverable` coalgebra (`outWit`, off the diagonal link) is `≈` no mint, the exclusion structural. Reached BECAUSE the TOTAL target was attempted and refuted, not assumed.
- **Total** (`|Hold| = 1`, degenerate; and a LIVE outcome the series is genuinely open to), AT THE FLAT LAYER: WS4's mint IS essentially surjective up to `≈` over FLAT imports, every flat `¬ Recoverable` coalgebra `≈` some mint. Substance monism at the flat layer. Reported in its direction, bounded by the tower (tower-laden imports untestable, the layer-stability open), the positioning rewritten honestly, not defended. Degenerate on the single-hold carrier here, but stated first-class so that were a carrier of interest to fall surjective, "TOTAL at the flat layer, tower open" would be the finding.
- **Disconnected** (first-class): WS1 fails, no non-trivial pair of orders admits a monotone mint and a non-vacuous connection. The obstruction (the variance wall, `ws1-orders-design.md` §triage) is the result. **If WS1 lands DISCONNECTED, the whole series reports Disconnected and WS2–WS5 are not built.**
- **Partial**: any obligation lands only per-instance or degenerate (a per-inspection transport, an iso-in-disguise connection, a literal-equality-only defect that fails to survive `≈`).

**The dependency law (protocol §4).** WS1 blocks WS2–WS4; WS2 blocks WS3 (adjoint) and WS4 (defect is about the WS2 mint); WS5 consumes all and cannot compute until WS4 settles. Upstream changes invalidate downstream builds; the ledger shows it.

---

## 5. The strip test, pre-annotated (protocol §0.3, aggregated by WS5)

For every payoff, delete "duality / fit / wound / rescue / given / chosen / mint / factory / connection / defect" and check the residue.

- **Transport** (`ws2_mint_lands_in_opening`) SHOULD strip to: *"for every inspection, the two-region labelled coalgebra whose regions broadcast the residue and the reference-content is not `Recoverable`, because at `h₀` the residue-label `¬ insp h₀ h₀` differs from the reference-label's self-value `insp h₀ h₀` (`ws2_residue_distinct`)."* A `Recoverable`/diagonal fact.
- **Connection** (`ws3_galois` + `ws3_roundtrip_not_identity`) SHOULD strip to: *"a `GaloisConnection` between two non-trivial preorders whose interior round trip is not the identity on a named element."* A bare Galois-connection fact.
- **Defect** (`ws4_mint_not_surjective`) SHOULD strip to: *"a `¬ Recoverable` labelled coalgebra order-equivalent (`≈`) to no `mintL insp`, excluded because every `mintL insp` satisfies the diagonal link `bT h₀ = ¬ bF h₀`, `≈` preserves that link data, and the witness violates it (`ws1_no_self_total_hold`)."* An out-of-image-up-to-`≈` `¬ Recoverable` fact with structural exclusion. (Its companion, `ws4_mint_essentially_surjective_degenerate`, strips to *"on a single-hold carrier every `¬ Recoverable` coalgebra `≈` some mint"*, the TOTAL fact.)

Any payoff that survives stripping as something OTHER than its named fact, or that needs the deleted word, is flagged. Any name doing a proof's work is SERIOUS.

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-13/formal/Series13/`)

Re-namespaced `Series13.WSn`, transcribed (not imported), as every prior series transcribed. The entire block is already assembled, verbatim, in `series-12/formal/Series12/ws1.lean` (Series 12's WS1 transcription base), which is the cleanest single source:

- **Carrier + bisimulation + collapse engine + import theorem:** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `.ne_empty`, `.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim`, `ws1_atomless_bisim`, `ws1_recovers_static`, `ws2_import_theorem_static`, `ws2_import_theorem`, `LeafDiff`, `ImportDiff`, `ws3_dichotomy`, `ws3_atomless_distinct_is_import` (**Series 07**).
- **The labelled / import test:** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `ws4_recoverable_not_import`, `labelLoop`, `labelLoop_val`, `ws4_label_survives_quotient`, `plainOf_labelLoop_val`, `plainOf_labelLoop_reaches`, `labelLoop_atomless`, `plainOf_labelLoop_true_bisim`, `ws4_free_label_is_import`, `ws4_labelLoop_not_recoverable`.
- **The diagonal spine and the free residue:** `Hold`, `afford`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `ws1_insp_not_surjective`, `ws1_diagonal_not_bisim`, `residue`, `ResidueRecoverable`, `ws2_residue_distinct`, `ws2_residue_free`, `ws2_residue_is_import`.
- **The opening (Series 12 WS1):** `Opening`, `ws1_two_halves`, `ws1_shape_coincidence`, `ws1_coincidence_not_identity`, `ws1_coincidence_not_identity_witness`.

**Deliberately NOT transcribed (the single-layer scope, a named open, not a silent omission):** the reification tower (`IsReify`, `reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`). Series 13's carrier is FLAT; every labelled coalgebra in scope is a flat two-region self-loop. So the whole fit is drawn at the flat layer, and the LAYER-STABILITY question, does the mint commute with reification, does any tower-carrying import survive outside the mint's image up to `≈`, is left OPEN as a theorem-shaped question (WS5, the close). Any TOTAL is TOTAL AT THE FLAT LAYER (essentially surjective over flat imports, the tower unexamined), a bounded finding whose bound is the tower; any DUAL is DUAL at the flat layer (a flat import `≈` no mint).

The **genuinely new Series 13 Lean**, defined here and expanded in the designs: `Insp`, `⊑c`, `instLEInsp`/`instPreorderInsp`, `MCar`, `Lab`, `instLELab`/`instPreorderLab`, and the non-triviality theorems (WS1); `mintL`, `ws2_mint_lands_in_opening`, `ws2_mint_exogenous` (WS2); `readInsp`, `ws3_mint_monotone`, `ws3_read_monotone`, `ws3_galois`, `ws3_roundtrip_closure`, `ws3_roundtrip_interior`, `ws3_roundtrip_not_identity` (WS3); the out-of-image witness `outWit`, `ws4_outWit_not_recoverable`, `ws4_mint_not_surjective`, `ws4_exclusion_structural` (WS4); `Series13Verdict`, `FitFork`, `verdictOfFit`, the `Audit`, `ws5_verdict`, `ws5_verdict_eq`, and the audit checks (WS5). Nothing is `import`ed across series.

---

*Design index for Series 13. Read this before any `wsN-design.md`; the shared objects, the transcribed carrier, the two orders (`instLEInsp`, `instLELab`), and the map pair (`mintL`, `readInsp`) are defined here ONCE and cited, never redefined. The four disciplines (§0) are the spine of the review: the fork stays open (the defect locates, never sorts); the connection is genuine (orders non-trivial, round trip non-identity, not an iso in disguise); the mint is exogenous (above the plain layer, a proof term); the defect is structural (the diagonal link excludes, not an artifact); and the names, given, chosen, consciousness, choice, God, the compass, stay in prose, never proof terms. The verdict fork is Dual / Total / Disconnected / Partial, the verdict a function, never assumed. Series 12's result stands; this series names the fit and lets that interval stand open. No em dashes in final academic paper copy; this working design index is not final copy.*
