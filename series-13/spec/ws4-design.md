# WS4, The defect (the fork in order-theoretic clothes)

**Design doc. Series 13, uncertain in direction. Owns: an import provably OUTSIDE the mint's image (`ws4_mint_not_surjective`), a labelled coalgebra failing `Recoverable` that no inspection mints, with the exclusion argued STRUCTURAL (`ws4_exclusion_structural`): the mint forces the diagonal link `residue-label h₀ = ¬ reference-label-self-value` at the distinguished hold, and the witness violates it, so no inspection mints it, by `ws1_no_self_total_hold`. The theorem LOCATES the import outside the image; it NEVER classifies it as given or chosen (discipline 1, the central sin). WS4 is the guard against the degenerate defect (discipline 4) and carries the fork that must stay open. Honest alternative, first-class: TOTAL (every import mintable), reported in its direction.**

*Series 13 is standalone; the diagonal (`ws1_no_self_total_hold`, `residue`, `diag`), the import test (`Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `labelLoop`), and the mint (`mintL`, WS2) are transcribed/consumed from `spec/README.md` and WS2. WS4 DEFINES the out-of-image witness `outWit` and proves the two obligations. The two signature risks: the fork closed by a sorting theorem (discipline 1, foreclosed by stating only "outside the image", never "given"/"chosen"), and the defect artifactual (discipline 4, foreclosed by the diagonal-link exclusion, not a cardinality/universe/typing accident).*

## The object at stake

The charter's WS4 (§2): exhibit an import provably outside the mint's image, a labelled coalgebra failing `Recoverable` that no inspection mints, non-degenerately, the witness not excluded by a mere size or typing artifact; the design must argue the exclusion is structural, the witness's label doing the excluding. If the witness lands, `ws4_mint_not_surjective` is the series' deepest theorem: the class of imports properly contains the diagonal-born ones, and the remainder, the imports with no self-inspective genealogy, is where the charter's prose places the given. If instead every import proves mintable, that is TOTAL, pre-registered and honorable: self-reference can manufacture the entire rescue.

**The structural key (from `spec/ws1-orders-design.md`, `spec/ws3-design.md`).** Every minted coalgebra `mintL insp = (residue insp, insp h₀)` satisfies the DIAGONAL LINK at `h₀`: `residue insp h₀ = ¬ (insp h₀) h₀` (because `residue = diag`, `diag insp h = ¬ insp h h`). So a labelled coalgebra `b = (bT, bF)` is mintable ONLY IF `bT h₀ = ¬ bF h₀`. A witness with `bT h₀ = bF h₀` is out-of-image, and the excluder is the diagonal, `ws1_no_self_total_hold`, not the bookkeeping. This is Series 07's undecidable fork wearing order-theoretic clothes: what self-reference can manufacture is exactly the pairs on the diagonal link; what lies off it must simply arrive.

**Ambient theory.** `spec/README.md` §2.2 (import test), §2.3 (diagonal), §2.6–§2.7 (labelled order, mint); `spec/ws3-design.md` (the interior drops these). Notation: `bT b`, `bF b` the two self-loop labels of `b : Lab dest`; a distinguished pair of holds `h₀ h₁ : Hold dest` with `h₁ ≠ h₀`.

## The out-of-image witness, fixed

```lean
/-- **The out-of-image witness.** Residue-position labelled `⊤` (const-true); reference-position labelled
    `bFwit := fun h => h ≠ h₁` (true everywhere except at the second hold `h₁`). Then `bT h₀ = ⊤ h₀ = True`
    and `bF h₀ = (h₀ ≠ h₁) = True` (since `h₀ ≠ h₁`), so `bT h₀ = bF h₀`: the diagonal link is VIOLATED,
    the witness is out-of-image. And `bT ≠ bF` (they differ at `h₁`: `⊤ h₁ = True`, `bFwit h₁ = False`), so
    the residue-position and reference-position are label-separated: `outWit` fails `Recoverable`, a genuine
    import. -/
noncomputable def outWit {X} (dest) (h₀ h₁ : Hold dest) (hinf : ℵ₀ ≤ κ) : Lab dest :=
  fun i => match i with
    | ⟨true⟩  => toPk hinf {((fun _ => True),      ⟨true⟩)}    -- bT = ⊤
    | ⟨false⟩ => toPk hinf {((fun h => h ≠ h₁),    ⟨false⟩)}   -- bF = (≠ h₁)
```

## Candidates (the out-of-image witness)

### D-C1, `outWit`, excluded by the diagonal link (the lead)

```lean
/-- **THE DEFECT.** `outWit` fails `Recoverable` (an import) and is NOT in the image of `mintL` (no inspection
    mints it). The theorem LOCATES it outside the image; it does not classify it. -/
theorem ws4_mint_not_surjective {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (outWit dest h₀ h₁ hinf)                                   -- an IMPORT (¬ Recoverable) …
  ∧ ¬ ∃ insp : Insp dest, mintL dest h₀ insp = outWit dest h₀ h₁ hinf := by  -- … outside the mint's image
  refine ⟨?_, ?_⟩
  · -- ¬ Recoverable: ⊤ is a plain-bisim (i ↦ {i}) but not a label-bisim, since bT ≠ bF (differ at h₁)
    intro hrec
    have hlab : IsBisimL (outWit dest h₀ h₁ hinf) (fun _ _ => True) := hrec _ (by …)   -- ⊤ plain-bisim
    obtain ⟨hf, _⟩ := hlab ⟨true⟩ ⟨false⟩ trivial
    obtain ⟨q, hq, hfst, _⟩ := hf ((fun _ => True), ⟨true⟩) (by simp [outWit])
    simp [outWit, Set.mem_singleton_iff] at hq; subst hq
    exact absurd (congrFun hfst h₁) (by simp [hne.symm …])         -- ⊤ h₁ = True ≠ (h₁ ≠ h₁) = False
  · -- out of image: mintL insp = outWit ⟹ residue insp = ⊤ ∧ insp h₀ = bFwit, but the diagonal link forces
    -- residue insp h₀ = ¬ insp h₀ h₀ = ¬ bFwit h₀ = ¬ True = False ≠ True = ⊤ h₀, contradiction.
    rintro ⟨insp, he⟩
    have hT : residue insp = (fun _ => True) := congrArg (fun d => bT d) he
    have hF : insp h₀ = (fun h => h ≠ h₁) := congrArg (fun d => bF d) he
    have hlink : residue insp h₀ = ¬ (insp h₀) h₀ := rfl                    -- diag insp h₀ = ¬ insp h₀ h₀
    rw [hT, hF] at hlink
    simp [hne] at hlink                                                     -- True = ¬ (h₀ ≠ h₁) = ¬ True = False
```
The witness is `¬ Recoverable` (the two labels differ at `h₁`, so the residue- and reference-positions are label-separated) and out-of-image (the diagonal link `residue insp h₀ = ¬ insp h₀ h₀` forces any minted `bT h₀ = ¬ bF h₀`, which `outWit` violates: `bT h₀ = bF h₀ = True`).

- **Ambient:** `Recoverable`, `IsBisim`, `IsBisimL`, `plainOf`, `mintL`, the diagonal link `residue = diag` (README §2.3).
- **Success condition (Dual, the defect):** `outWit` fails `Recoverable` and is outside the mint's image; the theorem states only "outside the image", never a classification.
- **Failure mode (two, both foreclosed):** *the fork closed (discipline 1, SERIOUS)* if the theorem sorted `outWit` into given/chosen; foreclosed, it only locates. *The defect artifactual (discipline 4)* if the exclusion were by size/typing; foreclosed, the excluder is the diagonal link `residue insp h₀ = ¬ insp h₀ h₀`. **Winner.**

**Paper triage (the WS4-specific questions).** (i) *Is the exclusion structural (label) or artifactual (size/typing)?* STRUCTURAL: `outWit` has the SAME carrier and label type as every `mintL insp` (both `Lab dest`, label `HoldPred dest`), so no typing artifact; the exclusion is `bT h₀ = bF h₀`, violating the mint-forced diagonal link `bT h₀ = ¬ bF h₀`, i.e. the label's own content at `h₀` does the excluding. (ii) *Is the witness a genuine import?* YES, `¬ Recoverable` because `bT ≠ bF` (differ at `h₁`). **Winner.**

### D-C2, the structural-exclusion certificate (the discipline-4 guard, first-class)

```lean
/-- **THE EXCLUSION IS STRUCTURAL.** The out-of-image obstruction is the diagonal link, not the bookkeeping:
    for EVERY inspection, the minted coalgebra satisfies `bT h₀ = ¬ bF h₀` at the distinguished hold, and
    `outWit` violates it (`bT h₀ = bF h₀`). Same carrier, same label type as every mint; the label excludes. -/
theorem ws4_exclusion_structural {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    (∀ insp : Insp dest, bT (mintL dest h₀ insp) h₀ = ¬ bF (mintL dest h₀ insp) h₀)   -- the mint-forced diagonal link
  ∧ (bT (outWit dest h₀ h₁ hinf) h₀ = bF (outWit dest h₀ h₁ hinf) h₀) := by            -- outWit violates it
  refine ⟨fun insp => ?_, ?_⟩
  · show residue insp h₀ = ¬ (insp h₀) h₀; rfl                      -- diag insp h₀ = ¬ insp h₀ h₀ (definitional)
  · simp [outWit, hne]                                             -- ⊤ h₀ = True = (h₀ ≠ h₁) = bF h₀
```
The certificate the review demands (discipline 4): the exclusion is by the diagonal link (a structural fact about EVERY mint), not by a size or typing accident. The witness lives in the same type as the mint's outputs; only its label's value at `h₀` excludes it.

- **Ambient:** `mintL`, `residue`/`diag`, `outWit`.
- **Success condition (Dual):** the mint-forced link and its violation by `outWit`, as a theorem. **Winner (the structural-exclusion certificate).**

### D-C3, `labelLoop`, the charter's first candidate (rejected as artifactual)

```lean
theorem ws4_labelLoop_out_of_image (hinf) :
    ¬ ∃ insp, mintL dest h₀ insp = labelLoop hinf   -- FALSE TYPE: labelLoop : Lab over ULift Bool labels
```
The transcribed `labelLoop` (label type `ULift Bool`, carrier `ULift Bool`) is `¬ Recoverable` (`ws4_labelLoop_not_recoverable`) and the charter names it "the first candidate."

- **Failure mode:** *the degenerate defect, a TYPING artifact (discipline 4), the honestly-reported alternative.* `labelLoop`'s label type (`ULift Bool`) differs from the mint's (`HoldPred dest`), so it is not even in `Lab dest`; excluding it from the image would be excluding it by a typing mismatch, exactly the artifact the charter forbids. **Reject as the witness.** Recorded because the charter names it: the honest reading is that `labelLoop` is the shape-touchstone, but a STRUCTURAL defect needs a witness in the mint's own codomain, excluded by its content, which is `outWit` (D-C1). The intensional resemblance (a Bool self-loop) is not enough; the witness must be in `Lab dest` and excluded by the diagonal, not the type.

### D-C4, the mint essentially surjective (TOTAL, pre-registered, first-class)

```lean
theorem ws4_mint_surjective (hinf) :                                        -- the TOTAL alternative
    ∀ b : Lab dest, (¬ Recoverable b) → ∃ insp, mintL dest h₀ insp = b
```
The honest alternative: if EVERY `¬ Recoverable` labelled coalgebra of the shape were mintable, the mint is essentially surjective, every import diagonal-born, and the fork presses toward the generated.

- **Status:** *the TOTAL outcome, pre-registered.* **Refuted here by D-C1** (`outWit` is `¬ Recoverable` yet not minted). Were D-C1 to fail (the diagonal link always satisfiable, e.g. if `|Hold| = 1` so no `h₁` exists and every two-label import lies on the link), WS4 reports TOTAL and states `ws4_mint_surjective` as the theorem, reported in its direction, the positioning rewritten honestly. **The design says so: TOTAL is honorable, not a failure.**

### D-C5, a theorem sorting the out-of-image imports (the central sin, stated to be rejected)

```lean
def genealogy (b : Lab dest) : Origin := if (∃ insp, mintL … insp = b) then .chosen else .given  -- SORTING
```
Classify each out-of-image import as *given* rather than *chosen* (or vice versa).

- **Failure mode:** *the fork closed from the order side (discipline 1), the CENTRAL SIN, SERIOUS.* Deciding an out-of-image import to be given rather than chosen does what Series 07 proves cannot be done and what Series 12 closed by leaving open. **Reject.** `ws4_mint_not_surjective` LOCATES (`¬ ∃ insp, mintL insp = outWit`); it never sorts. The words *given* and *chosen* appear in this design's prose only, never as terms; no `Origin` type, no `genealogy` function, exists in the core.

## Paper-decidable triage

| Cand | What it claims | Structural (label) not artifact? | Genuine import? | Verdict |
|---|---|---|---|---|
| D-C1 | `outWit` out-of-image | **yes** (diagonal link `bT h₀ = ¬ bF h₀`, same type) | **yes** (`bT ≠ bF` at `h₁`) | **win (the defect)** |
| D-C2 | structural-exclusion certificate | **yes** (mint-forced link, violation) | n/a | **win (discipline-4 guard)** |
| D-C3 | `labelLoop` out-of-image | **no** (typing artifact, `ULift Bool ≠ HoldPred`) | yes | reject (artifactual) |
| D-C4 | mint essentially surjective | n/a | n/a | TOTAL (pre-registered; refuted by D-C1) |
| D-C5 | sort out-of-image into given/chosen | — | — | **reject (central sin, SERIOUS)** |

## Winning candidates: D-C1 (the defect) + D-C2 (structural-exclusion certificate)

### Definitions and obligations (cite `spec/README.md` §2.2–§2.3, §2.6–§2.7; consume WS2)

```lean
namespace Series13.WS4
-- Recoverable, IsBisim, IsBisimL, plainOf, labelLoop, ws1_no_self_total_hold, residue, diag — transcribed.
-- mintL, mintL_true, mintL_false (WS2); instLELab (WS1) — consumed.  bT, bF : Lab dest → HoldPred dest (label projections)
-- outWit (fixed above)
-- ws4_mint_not_surjective (D-C1), ws4_exclusion_structural (D-C2)
```

**Proof architecture.** `outWit = (⊤, (≠ h₁))` lives in `Lab dest` (same type as every mint). It is `¬ Recoverable` because its two labels differ at `h₁` (the `⊤`-plain-bisim is not a label-bisim). It is out-of-image because minting forces the diagonal link `bT h₀ = ¬ bF h₀` (from `residue = diag`, `residue insp h₀ = ¬ insp h₀ h₀`), and `outWit` violates it (`bT h₀ = bF h₀ = True`, since `h₀ ≠ h₁`). D-C2 isolates the link as the structural excluder: for every mint the link holds, and `outWit` breaks it. **Dependencies:** the mint `mintL` (WS2), the diagonal `residue = diag` / `ws1_no_self_total_hold` (README §2.3, the structural excluder), the labelled order `instLELab` (WS1, `outWit`'s type). **The witness is excluded by the diagonal link (its own label at `h₀`), not by a size, universe, or typing artifact; and it is a genuine import.** The `h₁ ≠ h₀` hypothesis makes `outWit` a genuine import (`¬ Recoverable`), a richness requirement, not the excluder; the exclusion (out-of-image) holds structurally for any `|Hold|`, and on `|Hold| = 1` the honest alternative is TOTAL (no import lies off the link), pre-registered.

## Outcome classes (per charter §5)

- **Dual (the WS4 payoff, the series' deepest theorem):** `ws4_mint_not_surjective` (`outWit` an import outside the mint's image) with `ws4_exclusion_structural` (the exclusion by the diagonal link). The class of imports properly contains the diagonal-born ones; the remainder is where the prose places the given, LOCATED never SORTED.
- **Total (pre-registered, first-class, honorable):** if every import proves mintable (D-C4), the mint is essentially surjective, every import diagonal-born; WS4 states `ws4_mint_surjective` and WS5 records TOTAL, the fork pressed toward the generated, the positioning rewritten honestly.
- **Partial (pre-registered):** if `outWit` were excluded only by an artifact (a reviewer judging the diagonal link a bookkeeping accident), the defect is degenerate and WS4 reports Partial. Foreclosed by D-C2 (same type, the label excludes).
- **Circular / SERIOUS (pre-registered, discipline 1):** if any theorem sorted the out-of-image imports into given/chosen (D-C5), the fork is closed, the central sin. Foreclosed: the core locates, never sorts; *given*/*chosen* are prose only.
- **Strip test.** Delete "defect / fork / given / chosen / genealogy" from `ws4_mint_not_surjective` and it is the bare fact *"the labelled coalgebra `(⊤, ≠h₁)` fails `Recoverable` and equals no `mintL insp`, because every `mintL insp` has `bT h₀ = ¬ bF h₀` (`residue = diag`) and this one has `bT h₀ = bF h₀`"*, an out-of-image `¬ Recoverable` fact with structural exclusion, exactly protocol §0.3's target. No name is a term (no `Origin`, no `genealogy`; *given*/*chosen* in prose only).

## Deliverable

`series-13/formal/Series13/ws4.lean`: the transcribed import test + diagonal (README §6); the WS2 mint and WS1 order consumed; `outWit`, the label projections `bT`, `bF`; `ws4_mint_not_surjective` (D-C1), `ws4_exclusion_structural` (D-C2). **WS4 depends on WS2 (the defect is about the WS2 mint); the fork stays open (the theorem locates, never sorts); TOTAL is pre-registered.** Axiom check: `#print axioms ws4_mint_not_surjective` reduces through `residue`/`diag`/`ws1_no_self_total_hold` and the finite witness to the standard three. **An import provably outside the mint's image, the exclusion structural (the diagonal link, `ws1_no_self_total_hold`, in order-theoretic clothes), the witness a genuine import, the fork left open: Series 07's undecidable fork located, never sorted.**
