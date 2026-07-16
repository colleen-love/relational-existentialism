# WS4, The defect (the fork in order-theoretic clothes)

**Design doc. Series 13, GENUINELY UNCERTAIN IN DIRECTION. Owns the mintability question AT THE RIGHT RESOLUTION (up to equivalence `≈`, not literal equality), and reports whichever way it falls. DUAL: some import `b` fails `∃ insp, mintL insp ≈ b`, the exclusion STRUCTURAL (the diagonal link survives `≈`, a proof obligation). TOTAL: every `¬ Recoverable` coalgebra of the shape is `≈` some mint, stated first-class on carriers with `|Hold| ≥ 2` (not the degenerate single-hold case). The verdict is COMPUTED from which holds; `outWit` is the TEST ARTICLE, not the answer. The theorem LOCATES, never SORTS (discipline 1); the exclusion is structural, never artifactual (discipline 4).**

*Series 13 is standalone; the diagonal (`ws1_no_self_total_hold`, `residue`, `diag`), the import test (`Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `labelLoop`), the labelled order (`instLELab`, WS1), and the mint (`mintL`, WS2) are transcribed/consumed from `spec/README.md` and WS1/WS2. WS4 DEFINES `≈` (order-equivalence in `instLELab`) and the test article `outWit`, and computes the mintability question at that resolution. The two signature risks: the fork closed by a sorting theorem (discipline 1, foreclosed, the core only asks membership-up-to-`≈`, never *given*/*chosen*), and DUAL-by-construction (foreclosed by moving to `≈`, so the defect survives only if the diagonal genuinely blocks it, not a bookkeeping artifact of literal equality).*

## The object at stake, and why literal equality is the wrong test

The charter's WS4 (§2): exhibit an import provably outside the mint's image, non-degenerately, the exclusion structural. The naive reading tests LITERAL non-surjectivity, `¬ ∃ insp, mintL insp = b`. **This is too fine, and DUAL-by-construction.** Two coalgebras that are label-bisimilar (or order-equivalent) do the same import work; a `b` that merely tweaks a mint's reference-label AWAY from the distinguished hold `h₀` (invisible to both the labelled order and label-bisimilarity) fails literal equality against every mint while doing nothing new. So literal non-surjectivity is cheap, and a DUAL read off it is an artifact of the resolution, not a finding.

The honest test is mintability **up to equivalence**. Fix

```lean
/-- **The equivalence.** Order-equivalence in `instLELab`: `b ≈ b'` iff each is `≤` the other. Justified over
    label-bisimilarity because it is the equivalence the CONNECTION already uses (the Galois connection,
    WS3, is between `instLEInsp` and `instLELab`, so "the mint's image" is naturally taken up to `instLELab`
    equivalence), it is coarser than literal equality exactly where the order is blind (the reference-label
    away from `h₀`), and it is the SAME boundary as label-bisimilarity for this shape (both make `b` mintable
    iff `b` sits on the diagonal link, verified below), so the choice does not tilt the outcome. -/
def labEquiv {X} (dest) (h₀ : Hold dest) (b b' : Lab dest) : Prop := b ≤ b' ∧ b' ≤ b     -- `b ≈ b'`
```

**What `≈` sees (paper-computed, the crux).** On the singleton-edge shape `b = (bT, bF)` (residue-label `bT`, reference-label `bF`), `instLELab` gives `d₁ ≤ d₂ ↔ bT₁ ⊑c bT₂ ∧ (bF₂ h₀ → bF₁ h₀)`, so `b ≈ b' ↔ bT = bT' ∧ bF h₀ = bF' h₀`: **`≈` sees the residue-label FULLY and the reference-label ONLY at `h₀`.** Every mint satisfies the DIAGONAL LINK `bT h₀ = ¬ bF h₀` (because `bT = residue insp`, `bF = insp h₀`, and `residue insp h₀ = ¬ insp h₀ h₀ = ¬ bF h₀`). Therefore:

> **`b` is mintable up to `≈` ⟺ `b` sits on the diagonal link `bT h₀ = ¬ bF h₀`.**
> (`mintL insp ≈ b` forces `residue insp = bT` and `insp h₀ h₀ = bF h₀`; the link then reads `bT h₀ = ¬ bF h₀`. Conversely, on the link, `insp h h' := if h = h₀ then bF h' else ¬ bT h` mints a coalgebra `≈ b`.)

This boundary is the whole content of WS4, and it is `ws1_no_self_total_hold` in order-theoretic clothes: what the mint can manufacture is exactly the coalgebras on the diagonal link; what lies off it must simply arrive. The direction of the verdict is then a COUNTING question, computed, not assumed:

- **`|Hold| ≥ 2`:** off-link `¬ Recoverable` coalgebras EXIST (differ from the link only at a second hold `h₁ ≠ h₀`), so the mint is NOT essentially surjective: **DUAL**, the defect structural.
- **`|Hold| = 1`:** every `¬ Recoverable b` differs from `bF` only at `h₀`, so `bT h₀ ≠ bF h₀`, i.e. `bT h₀ = ¬ bF h₀` (on the link), so every import is mintable: **TOTAL** (degenerate).

**We attempted TOTAL on `|Hold| ≥ 2` (every `¬ Recoverable` `≈` some mint) as a first-class target; it is FALSE, refuted by `outWit` below. That refutation IS the DUAL finding, computed, not a construction.**

**Ambient theory.** `spec/README.md` §2.2 (import test), §2.3 (diagonal), §2.6–§2.7 (labelled order, mint); `spec/ws3-design.md` (the interior drops these off-link coalgebras). Notation: `bT b`, `bF b` the two self-loop labels of `b`; holds `h₀ h₁ : Hold dest`.

## The single-layer scope (the tower bound), stated not silenced

Series 13 deliberately does NOT transcribe the reification tower (`IsReify`, `reifyStep`, `towerN`, `prec`); its carrier is FLAT. Every labelled coalgebra in `Lab dest` (the mint's codomain and `outWit`) is a flat two-region self-loop; no coalgebra here carries tower structure. So the mintability question WS4 answers is the FLAT-LAYER question, and both outcomes are bounded by that:

- **DUAL** here is DUAL AT THE FLAT LAYER: `outWit` is a flat import order-equivalent to no mint. Whether some tower-carrying import (a coalgebra whose labels track reification rank) also survives outside the mint's image up to `≈` is UNTESTABLE in this carrier and is a **named open** (WS5, `the layer-stability open`), not a silent omission.
- **TOTAL** here would be TOTAL AT THE FLAT LAYER: the mint essentially surjective over FLAT imports. It would NOT license "every import diagonal-born" outright, because tower-laden imports are unexamined. The honest report is "TOTAL at the flat layer, tower open," a BOUNDED finding whose bound is the tower.

The layer-stability question, named for the close: **does the mint commute with reification, and does any tower-carrying import survive outside the mint's image up to `≈`?** Series 13 is a single-layer result and says so; it does not extend to the tower, and this open is recorded as a theorem-shaped question Series 13 leaves for a successor, exactly as Series 12's permanent opens were left.

## The test article, fixed

```lean
/-- **The test article** (NOT the answer). Residue-label `⊤`; reference-label `bFwit := fun h => h ≠ h₁`.
    On `|Hold| ≥ 2` (`h₁ ≠ h₀`) it is OFF the diagonal link: `bT h₀ = ⊤ h₀ = True` and `bF h₀ = (h₀ ≠ h₁) =
    True`, so `bT h₀ = bF h₀` (link demands `bT h₀ = ¬ bF h₀`). And `bT ≠ bF` (differ at `h₁`), so it is
    `¬ Recoverable`, a genuine import. It witnesses DUAL. On `|Hold| = 1` no such `h₁` exists and the article
    degenerates onto the link; the honest report there is TOTAL. -/
noncomputable def outWit {X} (dest) (h₀ h₁ : Hold dest) (hinf : ℵ₀ ≤ κ) : Lab dest :=
  fun i => match i with
    | ⟨true⟩  => toPk hinf {((fun _ => True),   ⟨true⟩)}    -- bT = ⊤
    | ⟨false⟩ => toPk hinf {((fun h => h ≠ h₁), ⟨false⟩)}   -- bF = (≠ h₁)
```

## Candidates

### D-C1, DUAL: `outWit` not mintable up to `≈`, the diagonal link surviving `≈` (the lead when `|Hold| ≥ 2`)

```lean
/-- **THE DEFECT (up to `≈`).** `outWit` fails `Recoverable` (an import) and is `≈` NO mint. The theorem
    LOCATES it outside the mint's image at the honest resolution; it does not classify it. -/
theorem ws4_mint_not_surjective {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (outWit dest h₀ h₁ hinf)                                              -- an IMPORT …
  ∧ ¬ ∃ insp : Insp dest, labEquiv dest h₀ (mintL dest h₀ insp) (outWit dest h₀ h₁ hinf) := by  -- … ≈ no mint
  refine ⟨?_, ?_⟩
  · -- ¬ Recoverable: ⊤ is a plain-bisim (i ↦ {i}) but not a label-bisim, since bT ≠ bF (differ at h₁)
    intro hrec
    have hlab : IsBisimL (outWit dest h₀ h₁ hinf) (fun _ _ => True) := hrec _ (by …)   -- ⊤ plain-bisim
    obtain ⟨hf, _⟩ := hlab ⟨true⟩ ⟨false⟩ trivial
    obtain ⟨q, hq, hfst, _⟩ := hf ((fun _ => True), ⟨true⟩) (by simp [outWit])
    simp [outWit, Set.mem_singleton_iff] at hq; subst hq
    exact absurd (congrFun hfst h₁) (by simp [hne.symm])          -- ⊤ h₁ = True ≠ (h₁ ≠ h₁) = False
  · -- ≈ no mint: mintL insp ≈ outWit ⟹ (from outWit ≤ mintL insp) residue insp h₀ = True, and
    -- (from mintL insp ≤ outWit) insp h₀ h₀ = True; but residue insp h₀ = ¬ insp h₀ h₀, contradiction.
    rintro ⟨insp, hle₁, hle₂⟩
    have hresT : residue insp h₀ = True := by
      have := (hle₂.1) ((fun _ => True), ⟨true⟩) (by simp [outWit])     -- outWit ≤ mintL: bT(outWit)=⊤ ⊑c residue insp
      …                                                                 -- ⊤ h₀ → residue insp h₀
    have hself : (insp h₀) h₀ = True := by
      have := (hle₁.2) ((fun h => h ≠ h₁), ⟨false⟩) (by simp [outWit])  -- mintL ≤ outWit ref-part: bF(outWit) h₀ → insp h₀ h₀
      simpa [hne] using this                                           -- (h₀ ≠ h₁ = True) → insp h₀ h₀
    have hlink : residue insp h₀ = ¬ (insp h₀) h₀ := rfl               -- diag insp h₀ = ¬ insp h₀ h₀
    rw [hresT, hself] at hlink; simp at hlink                          -- True = ¬ True = False
```
`outWit` is `¬ Recoverable` (labels differ at `h₁`) and `≈` no mint: order-equivalence forces `residue insp = bT = ⊤` (so `residue insp h₀ = True`, from `outWit ≤ mintL insp`) AND `insp h₀ h₀ = bF h₀ = True` (from `mintL insp ≤ outWit`), but the diagonal link `residue insp h₀ = ¬ insp h₀ h₀` makes these inconsistent. The exclusion is the diagonal, surviving `≈`.

- **Ambient:** `Recoverable`, `IsBisim`, `IsBisimL`, `instLELab` (both directions of `≈`), `mintL`, `residue = diag`.
- **Success condition (Dual):** `outWit` fails `Recoverable` and is `≈` no mint; the theorem states only membership-up-to-`≈`, never a classification.
- **Failure mode (three, all handled):** *the fork closed (discipline 1, SERIOUS)* if it sorted `outWit`; foreclosed. *DUAL-by-construction* if literal equality were the test; foreclosed by moving to `≈`. *the defect artifactual (discipline 4)* if the exclusion were by size/typing; foreclosed, the diagonal link excludes. **Winner when `|Hold| ≥ 2`.**

**Paper triage (the WS4-specific questions).** (i) *Structural (label) or artifactual (size/typing)?* STRUCTURAL: `outWit` has the SAME carrier and label type as every mint (`Lab dest`), and the exclusion is the diagonal link `bT h₀ = ¬ bF h₀`, an equation in the label's own content at `h₀` that `≈` preserves. Not a typing or universe accident. (ii) *A genuine import?* YES, `¬ Recoverable` because `bT ≠ bF` at `h₁`. (iii) *Does the exclusion survive `≈`?* YES, and its survival is the proof obligation `ws4_exclusion_structural` (D-C2), not an assumption. **Winner (|Hold| ≥ 2).**

### D-C2, the diagonal link survives `≈` (the structural-exclusion certificate, the discipline-4 guard)

```lean
/-- **THE LINK SURVIVES `≈`.** `≈` preserves exactly the diagonal-link data: if `b ≈ b'` then `bT b = bT b'`
    and `bF b h₀ = bF b' h₀`. Every mint is ON the link (`bT h₀ = ¬ bF h₀`); `outWit` is OFF it
    (`bT h₀ = bF h₀`). So being on/off the link is `≈`-invariant, and the exclusion is structural, not a
    literal-equality accident. -/
theorem ws4_exclusion_structural {X} (dest) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) :
    (∀ b b' : Lab dest, labEquiv dest h₀ b b' →                                   -- ≈ preserves the link data:
        (bT b = bT b') ∧ (bF b h₀ ↔ bF b' h₀))
  ∧ (∀ insp : Insp dest, bT (mintL dest h₀ insp) h₀ = ¬ bF (mintL dest h₀ insp) h₀)   -- every mint ON the link
  ∧ (bT (outWit dest h₀ h₁ hinf) h₀ = bF (outWit dest h₀ h₁ hinf) h₀) := by            -- outWit OFF the link
  refine ⟨fun b b' hbb => ?_, fun insp => rfl, ?_⟩
  · exact ⟨…, …⟩                                                    -- extract bT-equality and bF-h₀ from mutual ≤
  · simp [outWit, hne]                                             -- ⊤ h₀ = True = (h₀ ≠ h₁) = bF h₀
```
The certificate discipline 4 demands, upgraded to `≈`: the exclusion is by the diagonal link, `≈` preserves the link data (so the exclusion is not a literal-equality artifact), every mint is on the link, `outWit` is off it. The label excludes; `≈` cannot rescue it.

- **Ambient:** `instLELab`, `mintL`, `residue`/`diag`, `outWit`.
- **Success condition (Dual):** the three conjuncts, as a theorem: `≈` preserves the link data, mints are on the link, `outWit` is off it. **Winner (the structural-exclusion certificate at resolution `≈`).**

### D-C3, TOTAL: essential surjectivity on `|Hold| ≥ 2` (the first-class target we ATTEMPTED, and refuted)

```lean
/-- **THE TOTAL TARGET (attempted, on |Hold| ≥ 2).** Every `¬ Recoverable` coalgebra of the shape is `≈` some
    mint. If provable, the mint is essentially surjective, every import diagonal-born, and the verdict is
    TOTAL. THIS IS FALSE on |Hold| ≥ 2, refuted by `outWit` (D-C1): the off-link imports are not mintable up
    to `≈`. The refutation is the DUAL finding. -/
theorem ws4_mint_essentially_surjective_ATTEMPT {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∀ b : Lab dest, (¬ Recoverable b) → ∃ insp, labEquiv dest h₀ (mintL dest h₀ insp) b
  -- REFUTED on |Hold| ≥ 2 by D-C1 (outWit is a ¬Recoverable b with no ≈-mint); NOT a theorem there.
```
The honest attempt at TOTAL on the non-degenerate carrier, stated so its refutation is visible. On `|Hold| ≥ 2` it is FALSE (D-C1 is the counterexample), so the verdict is DUAL. On `|Hold| = 1` it is TRUE (D-C4).

- **Status:** *the TOTAL alternative, attempted and refuted on `|Hold| ≥ 2`.* **Not a theorem on `|Hold| ≥ 2`; its negation (D-C1) is.** Recorded first-class so the verdict is genuinely computed: we did not assume DUAL, we tried TOTAL and it failed on the carriers of interest.

### D-C4, TOTAL on `|Hold| = 1` (the degenerate case, honestly labelled)

```lean
/-- **TOTAL, degenerate.** If the carrier has a single hold (`∀ h, h = h₀`), every `¬ Recoverable` coalgebra
    sits on the diagonal link (its labels differ only at `h₀`, so `bT h₀ ≠ bF h₀`, i.e. `bT h₀ = ¬ bF h₀`),
    hence is `≈` some mint. The mint is essentially surjective and the verdict is TOTAL, on the degenerate
    single-hold carrier. Reported HONESTLY as degenerate, not as the finding. -/
theorem ws4_mint_essentially_surjective_degenerate {X} (dest) (h₀ : Hold dest)
    (hone : ∀ h : Hold dest, h = h₀) (hinf : ℵ₀ ≤ κ) :
    ∀ b : Lab dest, (¬ Recoverable b) → ∃ insp, labEquiv dest h₀ (mintL dest h₀ insp) b := by
  intro b hb
  -- ¬ Recoverable ⟹ bT ≠ bF ⟹ (single hold) bT h₀ ≠ bF h₀ ⟹ bT h₀ = ¬ bF h₀ (on the link) ⟹ mintable up to ≈
  refine ⟨fun h h' => if h = h₀ then bF b h' else ¬ bT b h, ?_⟩
  …
```
The degenerate TOTAL, proved but labelled degenerate. On a single-hold carrier there is no room for an off-link import, so the mint manufactures the whole rescue; the finding is real but the carrier is not of interest.

- **Status:** *TOTAL on `|Hold| = 1`, a theorem, degenerate.* Feeds the verdict (WS5): if the carrier is single-hold, the verdict is TOTAL; else DUAL. **Winner as the honest degenerate boundary.**

### D-C5, `labelLoop`, the charter's named candidate (rejected as artifactual)

```lean
theorem ws4_labelLoop_out_of_image (hinf) : ¬ ∃ insp, mintL dest h₀ insp = labelLoop hinf  -- FALSE TYPE
```
`labelLoop` (label type `ULift Bool ≠ HoldPred dest`) is `¬ Recoverable` and the charter names it "the first candidate."

- **Failure mode:** *the degenerate defect, a TYPING artifact (discipline 4), the honestly-reported alternative.* `labelLoop` is not in `Lab dest` (wrong label type), so excluding it is a typing accident, exactly the artifact the charter forbids. **Reject as the witness.** Recorded: `labelLoop` is the shape-touchstone; a STRUCTURAL defect needs a witness in the mint's own codomain, excluded by the diagonal link up to `≈`, which is `outWit` (D-C1).

### D-C6, a theorem sorting the out-of-image imports (the central sin, stated to be rejected)

```lean
def genealogy (b : Lab dest) : Origin := if (∃ insp, mintL … insp ≈ b) then .chosen else .given  -- SORTING
```
Classify each `≈`-out-of-image import as *given* rather than *chosen*.

- **Failure mode:** *the fork closed from the order side (discipline 1), the CENTRAL SIN, SERIOUS.* Deciding an out-of-image import to be given rather than chosen does what Series 07 proves cannot be done. **Reject.** `ws4_mint_not_surjective` asks only membership up to `≈` (`¬ ∃ insp, mintL insp ≈ outWit`); it never sorts. No `Origin` type, no `genealogy` function; *given*/*chosen* in prose only.

## Paper-decidable triage

| Cand | Claim | Resolution | Structural (label), not artifact? | Genuine import? | Verdict |
|---|---|---|---|---|---|
| D-C1 | `outWit` `≈`-out-of-image | up to `≈` | **yes** (diagonal link survives `≈`, same type) | **yes** (`bT ≠ bF` at `h₁`) | **win (DUAL, |Hold| ≥ 2)** |
| D-C2 | link survives `≈` | up to `≈` | **yes** (`≈` preserves link data) | n/a | **win (discipline-4 guard)** |
| D-C3 | ess. surjective on |Hold| ≥ 2 | up to `≈` | n/a | n/a | **REFUTED by D-C1 (⟹ DUAL)** |
| D-C4 | ess. surjective on |Hold| = 1 | up to `≈` | n/a | n/a | TOTAL (degenerate), a theorem |
| D-C5 | `labelLoop` out-of-image | literal (wrong type) | **no** (typing artifact) | yes | reject (artifactual) |
| D-C6 | sort into given/chosen | — | — | — | **reject (central sin, SERIOUS)** |

**The computed direction.** `outWit` is the test article. On `|Hold| ≥ 2` (carriers of interest), D-C3 (TOTAL) is refuted by D-C1, so the verdict is **DUAL** with the structural defect (D-C1, D-C2). On `|Hold| = 1` (degenerate), D-C4 gives **TOTAL**. WS5 computes which, from the carrier's hold count; neither is the lead, the math decides.

## Winning candidates: D-C1 + D-C2 (DUAL, |Hold| ≥ 2) / D-C4 (TOTAL, |Hold| = 1), computed by WS5

### Definitions and obligations (cite `spec/README.md` §2.2–§2.3, §2.6–§2.7; consume WS1, WS2)

```lean
namespace Series13.WS4
-- Recoverable, IsBisim, IsBisimL, plainOf, labelLoop, ws1_no_self_total_hold, residue, diag — transcribed.
-- mintL, mintL_true, mintL_false (WS2); instLELab (WS1); bT, bF : Lab dest → HoldPred dest — consumed.
-- labEquiv (≈), outWit (fixed above)
-- ws4_mint_not_surjective (D-C1, DUAL), ws4_exclusion_structural (D-C2),
-- ws4_mint_essentially_surjective_degenerate (D-C4, TOTAL on |Hold| = 1)
```

**Proof architecture.** The equivalence `labEquiv` (order-equivalence in `instLELab`) sees `bT` fully and `bF` only at `h₀`. Mintability up to `≈` reduces to the diagonal link `bT h₀ = ¬ bF h₀` (from `residue = diag`). D-C1 (DUAL, `|Hold| ≥ 2`): `outWit = (⊤, ≠h₁)` is `¬ Recoverable` (labels differ at `h₁`) and off the link (`bT h₀ = bF h₀ = True`), so `≈` no mint (mutual `≤` forces `residue insp h₀ = True` and `insp h₀ h₀ = True`, contradicting the link). D-C2 certifies the link survives `≈`. D-C4 (TOTAL, `|Hold| = 1`): every import is on the link, hence `≈` a mint. **Dependencies:** the mint `mintL` (WS2), the diagonal `residue = diag` / `ws1_no_self_total_hold` (the structural excluder), the labelled order `instLELab` (WS1, both directions for `≈`). **The exclusion is the diagonal link surviving `≈`, not a literal-equality artifact; the direction is computed from the hold count, not assumed.**

## Outcome classes (per charter §5), COMPUTED

- **Dual (`|Hold| ≥ 2`, carriers of interest):** `ws4_mint_not_surjective` (`outWit` an import, `≈` no mint) with `ws4_exclusion_structural` (the link survives `≈`). Essential surjectivity was ATTEMPTED (D-C3) and REFUTED. The class of imports properly contains the diagonal-born ones; the remainder is where the prose places the given, LOCATED never SORTED.
- **Total (`|Hold| = 1`, degenerate), AT THE FLAT LAYER:** `ws4_mint_essentially_surjective_degenerate`. Every FLAT import mintable up to `≈`; the mint manufactures the whole FLAT rescue. Reported honestly as (a) degenerate (single-hold carrier) AND (b) bounded (flat layer only, tower-laden imports untestable, the layer-stability open, WS5). Even were a carrier of interest to fall surjective, the finding would be "TOTAL at the flat layer, tower open," not TOTAL outright: a flat mint essentially surjective over flat imports, with the tower unexamined, is a bounded finding whose bound is the tower.
- **Partial (pre-registered):** if `outWit` were excluded only by literal equality (a reviewer judging `≈` too fine) or the link failed to survive `≈`, the defect is degenerate and WS4 reports Partial. Foreclosed by D-C2 (the link is `≈`-invariant).
- **Circular / SERIOUS (discipline 1):** if any theorem sorted the out-of-image imports into given/chosen (D-C6), the central sin. Foreclosed: the core asks membership up to `≈`, never sorts; *given*/*chosen* prose only.
- **Strip test.** Delete "defect / fork / given / chosen / genealogy" from `ws4_mint_not_surjective` and it is the bare fact *"the labelled coalgebra `(⊤, ≠h₁)` fails `Recoverable` and is order-equivalent to no `mintL insp`, because every mint has `bT h₀ = ¬ bF h₀` (`residue = diag`), `≈` preserves that data, and this one has `bT h₀ = bF h₀`"*, an out-of-image-up-to-`≈` `¬ Recoverable` fact with structural exclusion. No name is a term (no `Origin`, no `genealogy`).

## Deliverable

`series-13/formal/Series13/ws4.lean`: the transcribed import test + diagonal (README §6); the WS2 mint and WS1 order consumed; `labEquiv`, `outWit`, `bT`, `bF`; `ws4_mint_not_surjective` (D-C1), `ws4_exclusion_structural` (D-C2), `ws4_mint_essentially_surjective_degenerate` (D-C4). **WS4 depends on WS2; the fork stays open (membership up to `≈`, never a classification); the direction (DUAL vs TOTAL) is computed by WS5 from the hold count.** Axiom check: `#print axioms ws4_mint_not_surjective` and `ws4_mint_essentially_surjective_degenerate` reduce through `residue`/`diag`/`ws1_no_self_total_hold`, `instLELab`, and the finite witness to the standard three. **Mintability tested at the right resolution (up to `≈`, not literal equality): the diagonal link is the boundary, it survives `≈`, and whether an off-link import exists (DUAL) or not (TOTAL) is computed from the carrier, `outWit` the test article, the fork left open.**
