# WS4-witness, The inhabitability witness (`dir := rank`)

**Design sub-artifact. Series 12, WS2's concrete model, consumed by WS4 and WS5. Owns: the ONE closed carrier `(destW, reifyW, rankW)` on which two existentials are discharged. (a) The opening is INHABITABLE and the many is real (`Many destWL`), separating a reified relatum that itself carries a reified constituent from a base relatum, plain-bisimilar by the collapse engine yet separated at the labelled level by their tower RANK, on a carrier where `rank` is NON-INJECTIVE (distinct states share a rank, so rank is provably coarser than identity and is not a point-indicator), with the separation reinstated as a GENERAL theorem (any reified relatum carrying a reified constituent separates from any base relatum, `reify`/`rank`/base-closure load-bearing in the general statement). (b) The convergence relation is UNDERDETERMINED (`ws4_underdetermined`), two compasses on this same carrier over a genuine constituency edge, one cohering and one not, both non-degenerate. Registered in `spec/README.md` §2.7 to §2.10; the disclosed structural deviation (total `IsReify` unsatisfiable on a concrete atomless carrier, pointwise reification facts supplied) is owned here.**

*Series 12 is standalone; the collapse engine (`ws1_atomless_bisim`, `hneRel_isBisim`), the labelled/import test (`plainOf`, `IsBisimL`, `Recoverable`), the reification section and tower (`IsReify`, `reifyStep`, `reify_mem_reifyStep`, `towerN`, `ws3_reify_preserves_SHNE`), and the `Compass`/`Converges`/`ConstituentOf` objects (README §2.9 to §2.10) are cited from `spec/README.md`; this sub-artifact adds only the concrete carrier and the two existential witnesses. It is the guard against the program's gravest inherited failure. Series 10's `ws2_reify_bisim_embeds` and Series 11's `ws1_attention_makes_real` both drew their distinction on `labelLoop`, two fixed Booleans where `reify`/`reifyStep`/`towerN` never occur, and were honestly re-graded Bookkeeping re-hit. The Phase B revision (`spec/design-review-1.md` Finding 1) further required that the witness not merely INTEND the tower but be extensionally more than a point-tag: the carrier carries a non-injective rank and a general separation theorem, so a blind strip test finds the general rank-separation fact on a coarse-rank carrier, not a two-Boolean labelled-separation fact.*

## The object at stake

Two existentials, on ONE carrier (README §4, WS2 owns it, WS4 reuses it so the model pair is on the same structure):

1. **Inhabitability with plurality (WS2).** `Many destWL` (README §2.8), a pair `x, y` plain-bisimilar (the collapse engine merges them, the quotient is blind) yet not label-bisimilar (the labelled level keeps them apart). Discipline 4 demands this be a GENUINE tower-distinction: `x` a reified relatum carrying a reified constituent, `y` a base relatum, `reify`/`reifyStep`/rank load-bearing, on a carrier where rank is coarser than identity, generalized across the tower, not a bare point-tag.
2. **Underdetermination (WS4).** `ws4_underdetermined` (README §2.10), two compasses `c₁, c₂` on this carrier with `Converges c₁ aW bW` and `¬ Converges c₂ aW bW`, both non-degenerate, over a GENUINE constituency edge (`ConstituentOf destW reifyW aW bW`).

The Series 10/11 answer, the relatum's own two-valued identity on a fixed field (`labelLoop`), is the point-tag that failed. Series 12's answer is **`dir := rank`**: the label a relatum broadcasts is its position in the reification tower, so the distinction is drawn on `towerN`/`reifyStep`, the reified relatum is separated from the base relatum BY its rank, and (Finding 1) rank is non-injective and the separation is general.

**Ambient theory.** `spec/README.md` §2.1 (collapse engine), §2.4 (import test), §2.5 (tower plus disclosed deviation), §2.9 (`Compass`), §2.10 (`Converges`, `ConstituentOf`).

## The closed carrier (four states, non-injective rank)

```lean
namespace Series12.Witness
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, ws1_atomless_bisim, LkObj, IsBisimL, plainOf,
-- IsReify, reifyStep, reify_mem_reifyStep, towerN, ws3_reify_preserves_SHNE, Compass, Converges,
-- ConstituentOf, NonDegenerate, cited (README §6).

inductive WCar : Type u
  | base | base' | mid | top          -- aW, aW' (rank 0); bW (rank 1); cW (rank 2)
  deriving DecidableEq

abbrev X : Type u := WCar
def aW  : X := .base                  -- a BASE relatum (rank 0)
def aW' : X := .base'                 -- a SECOND base relatum (rank 0), makes rank NON-INJECTIVE
def bW  : X := .mid                   -- a reified relatum (rank 1), = reifyW {aW}, dest bW = {aW}
def cW  : X := .top                   -- a reified relatum (rank 2) CARRYING the reified constituent bW, = reifyW {bW}

/-- The plain relating. `aW`, `aW'` self-loop (rank 0); `bW → aW`; `cW → bW`. All four are `SHNE`. -/
def destW (hinf : ℵ₀ ≤ κ) : X → PkObj κ X
  | .base  => toPk hinf {aW}
  | .base' => toPk hinf {aW'}
  | .mid   => toPk hinf {aW}          -- dest bW = {aW} = dest (reifyW {aW}) : pointwise reify at {aW}
  | .top   => toPk hinf {bW}          -- dest cW = {bW} = dest (reifyW {bW}) : pointwise reify at {bW}

/-- The patterns reified into `bW` and `cW`. -/
def sW  (hinf : ℵ₀ ≤ κ) : PkObj κ X := toPk hinf {aW}       -- the model-pair edge pattern (aW ∈ sW.1, bW = reifyW sW)
def sW₂ (hinf : ℵ₀ ≤ κ) : PkObj κ X := toPk hinf {bW}       -- the plurality pattern (bW ∈ sW₂.1, cW = reifyW sW₂)

/-- A section, defined pointwise at `{aW}` and `{bW}` (total `IsReify` is unsatisfiable here, disclosed below). -/
def reifyW (hinf : ℵ₀ ≤ κ) : PkObj κ X → X :=
  fun s => if s.1 = {aW} then bW else if s.1 = {bW} then cW else aW

/-- The RANK direction: position in the tower over `Ω₀ = {aW, aW'}`. NON-INJECTIVE: `rank aW = rank aW' = 0`. -/
def rankW : X → ℕ
  | .base | .base' => 0
  | .mid           => 1
  | .top           => 2

/-- **The general rank-labelled lift.** Every relatum broadcasts its rank on its outgoing edges; the plain
    quotient forgets it. Parametric in `(dest, rank)`, so the general separation theorem is stated over it. -/
def rankLift {X : Type u} (dest : X → PkObj κ X) (rank : X → ℕ) : X → LkObj κ (ULift.{u} ℕ) X :=
  fun x => PkMap κ (fun z => (⟨rank x⟩, z)) (dest x)

def destWL (hinf : ℵ₀ ≤ κ) : X → LkObj κ (ULift.{u} ℕ) X := rankLift (destW hinf) rankW
end Series12.Witness
```

**The carrier facts (paper-checked, each a small lemma):**

- **SHNE.** `aW`, `aW'` self-loop; `bW → aW → aW → …`; `cW → bW → aW → …`; so all four are `SHNE (destW hinf)` (`ws_witness_SHNE`).
- **Pointwise reification.** `destW (reifyW {aW}) = destW bW = {aW} = (sW).1` and `destW (reifyW {bW}) = destW cW = {bW} = (sW₂).1` (`ws_witness_reify_pointwise`). `aW ∈ (sW).1` and `bW ∈ (sW₂).1` (`ws_witness_constituent`).
- **Rank is NON-INJECTIVE (the anti-point-indicator certificate, Finding 1).** `rankW aW = rankW aW' = 0` and `aW ≠ aW'`, so rank is strictly coarser than identity and is provably not the point-indicator on any single state (`ws_witness_rank_noninjective`). Moreover `aW`, `aW'` are label-bisimilar under `destWL` (identical rank-0 self-loops up to the relation), so the rank labelling MERGES them, confirming the label is the rank, not a tag.
- **Rank is the tower position (the anti-point-tag certificate).** `bW = reifyW {aW}` and `bW ∈ reifyStep (destW) (reifyW) {aW, aW'}` via `reify_mem_reifyStep`, so `bW ∈ towerN … 1`, `rankW bW = 1`; `cW = reifyW {bW}` and `cW ∈ reifyStep (destW) (reifyW) (towerN … 1)`, so `cW ∈ towerN … 2`, `rankW cW = 2` (`ws_witness_rank_is_tower`). The rank monotone step `∀ w ∈ (sW₂).1, rankW w < rankW cW` holds (`rankW bW = 1 < 2`). `reify`, `reifyStep`, `towerN` all OCCUR and are load-bearing.
- **`plainOf destWL = destW`.** `plainOf (destWL hinf) x = PkMap snd (PkMap (fun z => (⟨rankW x⟩, z)) (destW hinf x)) = PkMap id (destW hinf x) = destW hinf x` (via `Set.image_id`) (`ws_witness_plainOf`).

## Candidates for the direction

### C1, `dir := rank`, non-injective, with the general separation theorem (the lead)

The label a relatum broadcasts is its tower rank; rank is non-injective (`aW`, `aW'` at 0); and the separation is a GENERAL theorem instantiated at the concrete pair.

```lean
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) :=
  ⟨cW, aW,
   ws1_atomless_bisim (plainOf (destWL hinf)) cW aW (ws_witness_SHNE hinf).top (ws_witness_SHNE hinf).base,
   (ws2_many_general (destW hinf) (reifyW hinf) rankW (sW₂ hinf) … bW … aW … ).2⟩          -- an INSTANCE of the general theorem
```

- **Ambient:** `ws1_atomless_bisim` (plain merge), `ws2_many_general` (the general rank-separation), `reify_mem_reifyStep`/`towerN` (rank IS the tower position), `ws_witness_rank_noninjective` (rank coarser than identity).
- **Success condition (Shape-drawn on the witness):** `cW` (a reified relatum carrying the reified constituent `bW`) and the base relatum `aW` are plain-bisimilar (collapse engine) but rank-separated, as an instance of the general theorem, on a carrier where rank is non-injective.
- **Failure mode:** *degenerate inhabitation (discipline 4).* Foreclosed on three fronts (Finding 1): the separated relatum carries a reified constituent (`cW = reifyW {bW}`, `rankW bW = 1`), rank is non-injective (`aW`, `aW'` share rank 0), and the separation is general (`ws2_many_general`), not one hand-picked pair. **Winner.**

### C2, `dir := self-identity` (the transcribed `labelLoop`, the point-tag)

The label is the relatum's own two-valued identity on a fixed field, exactly `labelLoop` (README §2.4).

```lean
theorem ws2_many_labelLoop (hinf : ℵ₀ ≤ κ) : Many (labelLoop hinf) :=
  ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1, (ws4_free_label_is_import hinf).2⟩
```

- **Failure mode:** *degenerate inhabitation, the Bookkeeping re-hit (discipline 4).* `reify`/`reifyStep`/`towerN` never occur; the distinction is on two fixed Booleans; rank (there is none) is trivially injective; there is no generalization. This is precisely Series 10/11's re-graded failure. **Reject as the witness; retain `labelLoop` only as the shape-touchstone (README §2.4).**

### C3, Two-state `dir := rank` (the silhouette, the Phase B v1 defect, rejected)

The earlier v1: `X = ULift Bool`, `aW = ⟨false⟩`, `bW = ⟨true⟩`, `dirOf x = if x = bW then ⟨1⟩ else ⟨0⟩`.

- **Failure mode:** *the point-tag SILHOUETTE (discipline 4, Finding 1).* On a two-element carrier `dirOf` is extensionally the point-indicator on `bW`, so even though `reify`/`rank` are intensionally present, a blind strip finds the two-Boolean labelled-separation fact, the exact silhouette of `ws4_label_survives_quotient`. **Reject:** the intensional justification is necessary but not sufficient; the carrier must ALSO be extensionally more than a point-tag, which C1 secures via non-injective rank and the general theorem.

### C4, `dir := rank` with a TOTAL section (the naive form, unsatisfiable)

Same as C1 but demanding `IsReify destW reifyW` (total, `∀ s, destW (reifyW s) = s`).

- **Failure mode:** *the honestly-reported alternative, the disclosed deviation.* A total section is `destW` surjective onto `PkObj κ X`, i.e. `|PkObj κ X| ≤ |X|`, false by Cantor for any `κ ≥ 2` on a concrete carrier. So `IsReify destW reifyW` is UNSATISFIABLE. **Reject the total form; C1 supplies the POINTWISE facts (`destW (reifyW {aW}) = {aW}`, `destW (reifyW {bW}) = {bW}`, the constituents nonempty and `SHNE`) that `ws3_reify_preserves_SHNE`/`reify_mem_reifyStep`/the convergence edge actually consume.** Faithful narrowing, disclosed (README §2.5), not hidden.

## Paper-decidable triage

| Cand | Direction | Reification load-bearing? | Rank coarser than identity? | `Many` non-degenerate + general? | Convergence non-vacuously definable? | Non-degenerate model pair? | Verdict |
|---|---|---|---|---|---|---|---|
| C1 | rank, non-injective, general | **yes** (`cW = reifyW {bW}`, `bW ∈ reifyStep {aW,aW'}`, label = rank) | **yes** (`rankW aW = rankW aW' = 0`, `aW ≠ aW'`) | **yes** (general theorem, `cW` carries reified `bW`) | **yes** (`Converges` a real `Or` equation over `ConstituentOf aW bW`) | **yes** (below) | **win** |
| C2 | self-identity (`labelLoop`) | no | no rank | no, point-tag | n/a | n/a | reject (point-tag) |
| C3 | rank, two-state | intensional only | injective (silhouette) | no, one pair | yes | yes | reject (silhouette) |
| C4 | rank + total `IsReify` | yes but UNSATISFIABLE |, |, |, |, | reject; C1 pointwise |

**The WS4-specific triage (protocol §2, the two questions).** (i) *Is `Converges` non-vacuously definable on this carrier?* YES, over the genuine constituency edge `ConstituentOf destW reifyW aW bW` (`aW ∈ (sW).1`, `bW = reifyW sW`, `destW bW = (sW).1`), `Converges c aW bW := c.raise aW bW (c.orient aW) = c.orient bW` is a real equation in `Or` whose truth depends on `c`. (ii) *Is there a non-degenerate model pair?* YES, the two compasses below.

## Winning construction, C1 (`dir := rank`, non-injective, general), pointwise section (C4 disclosed)

### The general separation theorem (Finding 1, reinstated)

```lean
/-- **THE GENERAL RANK-SEPARATION (reified relatum vs base relatum, tower load-bearing in the statement).**
    For any `dest`, `reify`, `rank` with the reified relatum ranking strictly above its constituents, any
    pattern `s` whose reified relatum `reify s` carries a constituent `w₀` of rank at least 1 (a REIFIED
    constituent), and any base relatum `y` of rank 0, the reified relatum and the base relatum are
    plain-bisimilar (the collapse engine) yet NOT label-bisimilar over the rank-labelled lift. `reify`,
    `rank`, and the base-rank-0 closure are load-bearing in the general statement. -/
theorem ws2_many_general {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (rank : X → ℕ)
    (s : PkObj κ X) (hs : s.1 ≠ ∅) (hpt : dest (reify s) = s)
    (w₀ : X) (hw₀ : w₀ ∈ s.1) (hw₀rank : 1 ≤ rank w₀)                 -- a REIFIED constituent
    (hstep : ∀ w ∈ s.1, rank w < rank (reify s))                     -- reify s ranks strictly above its constituents
    (y : X) (hyrank : rank y = 0)                                    -- a base relatum
    (hshne_r : SHNE dest (reify s)) (hshne_y : SHNE dest y) :
    (∃ R, IsBisim dest R ∧ R (reify s) y)                            -- plain-bisimilar (collapse engine, blind)
  ∧ (¬ ∃ R, IsBisimL (rankLift dest rank) R ∧ R (reify s) y) := by   -- rank-separated (reader distinguishes, FREE)
  refine ⟨ws1_atomless_bisim dest (reify s) y hshne_r hshne_y, ?_⟩
  -- rank (reify s) > rank w₀ ≥ 1 > 0 = rank y, so the source-rank labels mismatch; hpt gives an edge to mismatch on
  …
```
The separation is now GENERAL: `reify`, `rank`, and the strict-rank-step (`hstep`, so `rank (reify s) > rank w₀ ≥ 1 > 0 = rank y`, giving the label mismatch) are load-bearing in the statement, and the reified relatum genuinely carries a reified constituent. The concrete `Many` pair `(cW, aW)` is the instance `s := sW₂` (`= {bW}`), `w₀ := bW` (`rank 1`), `y := aW` (`rank 0`).

### The plurality witness and its certificates (WS2)

```lean
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) := …    -- (cW, aW), the general theorem instanced

theorem ws_witness_rank_noninjective : rankW aW = rankW aW' ∧ aW ≠ aW' := ⟨rfl, by decide⟩

theorem ws2_reification_loadbearing (hinf : ℵ₀ ≤ κ) :
    cW = reifyW hinf (sW₂ hinf)                                       -- reified relatum …
  ∧ cW ∈ reifyStep (destW hinf) (reifyW hinf) (towerN (destW hinf) (reifyW hinf) {aW, aW'} 1)  -- … reifyStep-adjoined at rank 2
  ∧ bW ∈ (sW₂ hinf).1 ∧ 1 ≤ rankW bW                                 -- … carrying a REIFIED constituent
  ∧ destW hinf (reifyW hinf (sW₂ hinf)) = (sW₂ hinf).1 := …           -- … pointwise reify
```

### The convergence model pair (WS4), same carrier, on a genuine constituency edge

```lean
/-- Non-degeneracy: `Or` non-trivial, `orient` not a collapsed constant, `raise` not a collapsed constant. -/
structure NonDegenerate {X} (dest) (reify) {Or} (c : Compass dest reify Or) (x W : X) : Prop where
  or_nontrivial   : ∃ o₁ o₂ : Or, o₁ ≠ o₂
  orient_nonconst : ∃ p q : X, c.orient p ≠ c.orient q
  raise_nonconst  : ∃ o₁ o₂ : Or, c.raise x W o₁ ≠ c.raise x W o₂

/-- Both compasses share the SAME non-constant orientation (`orient aW = ⟨true⟩`, `orient bW = ⟨false⟩`); they
    differ ONLY in the raising at the edge `(aW, bW)`. Convergence turns on the free RAISING, how "my
    orientation, followed up its layer" presents at the whole, which the structure does not decide. -/
noncomputable def cHold (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => ⟨!o.down⟩                                   -- the `not` raising: raise (orient aW) = ⟨false⟩ = orient bW

noncomputable def cFail (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => o                                           -- the `id` raising: raise (orient aW) = ⟨true⟩ ≠ orient bW

/-- **THE UNDERDETERMINATION (the wall).** Over the genuine constituency edge `(aW, bW)` (`ConstituentOf`),
    convergence holds under `cHold` and fails under `cFail`, on the SAME structure, both non-degenerate, so
    the structure does not decide it. -/
theorem ws4_underdetermined (hinf : ℵ₀ ≤ κ) :
    ConstituentOf (destW hinf) (reifyW hinf) aW bW
  ∧ ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨⟨sW hinf, ws_witness_reify_pointwise hinf, ws_witness_constituent hinf, rfl⟩,
   cHold hinf, cFail hinf, by simp [Converges, cHold], by simp [Converges, cFail],
   ⟨⟨⟨true⟩, ⟨false⟩, by decide⟩, ⟨aW, bW, by simp⟩, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩,
   ⟨⟨⟨true⟩, ⟨false⟩, by decide⟩, ⟨aW, bW, by simp⟩, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩⟩
```

**Why this is not deciding-by-definition (discipline 3), stated once and never hidden.** `Converges c aW bW` unfolds to `c.raise aW bW (c.orient aW) = c.orient bW`, a genuine equation in `ULift Bool`. It is not `True`, not `False`, not `orient aW = orient aW`. The two compasses share the exact same non-constant orientation and differ ONLY in the raising, so what is undetermined is isolated to the free layering, and both truth values are realized on ONE structure over ONE genuine constituency edge. Neither compass is a collapsed constant (`NonDegenerate`), the relation is non-vacuous (`cHold` satisfies it, `cFail` refutes it). This is the earned model pair, not a definitional tilt.

## Self-classification (the honest label)

- **Genuine tower-distinction, NOT a point-tag, on THREE certificates (discipline 4, Finding 1).** (i) *Reification load-bearing*: `cW = reifyW {bW}` is a `reifyStep`-produced reified relatum at `towerN` rank 2, carrying the REIFIED constituent `bW` (rank 1); `reify`/`reifyStep`/`towerN` are load-bearing (`ws2_reification_loadbearing`). (ii) *Rank non-injective*: `rankW aW = rankW aW' = 0` with `aW ≠ aW'`, and `aW`, `aW'` are label-bisimilar under `destWL`, so rank is provably coarser than identity and merges distinct states, hence is not a point-indicator (`ws_witness_rank_noninjective`). (iii) *General separation*: `ws2_many_general` separates ANY reified relatum carrying a reified constituent from ANY rank-0 base relatum, `reify`/`rank`/base-closure load-bearing in the general statement, so the concrete pair is an instance, not one hand-picked pair. The without-import side (the One) is genuine `ws2_import_theorem_static`, not a rigged collapse.
- **The disclosed structural deviation (owned here, routed to `charter-status.md`).** Total `IsReify destW reifyW` is UNSATISFIABLE on this concrete atomless carrier (Cantor). The witness supplies the POINTWISE reification facts the lemmas consume (`destW (reifyW {aW}) = {aW}`, `destW (reifyW {bW}) = {bW}`, constituents nonempty and `SHNE`), never the total section. Faithful narrowing, disclosed, not hidden. A reviewer who wants the total `IsReify` is entitled to note this; the design's position is that the pointwise facts are exactly what `ws3_reify_preserves_SHNE` and the convergence edge consume, so the narrowing changes no consumed hypothesis.
- **One inhabitant among all, for an existential.** Both `ws2_many_witness` and `ws4_underdetermined` discharge EXISTENTIALS ("the opening CAN be inhabited", "there EXIST two compasses …"). They witness inhabitability and underdetermination; they never assert "THIS is what inhabits it" or "THIS is the compass." The compasses `cHold`/`cFail` are constructed solely to witness `∃ c₁ c₂`; the audit (WS7) confirms no GENERAL compass-theorem uses them, and no theorem outside these existentials selects a distinguished compass.

## Outcome classes (per charter §5)

- **Shape-drawn on the witness (the payoff):** `ws2_many_witness` (`Many` on a reified relatum carrying a reified constituent, rank non-injective, general theorem instanced) and `ws4_underdetermined` (the non-degenerate model pair on a genuine constituency edge). The two existentials the expected terminus rests on, discharged on one closed carrier.
- **Partial (pre-registered, discipline 4):** if a reviewer still judged the rank label external to the tower, the inhabitation would be a point-tag and the finding Partial, reported as such. Foreclosed on three certificates: reification load-bearing, rank non-injective, and the general theorem.
- **Convergence-decided (pre-registered, discipline 3):** if the model pair proved vacuous, WS4 reports convergence-decided or Partial in its direction. Foreclosed by `NonDegenerate` on both compasses and both truth values realized.
- **Strip test.** Delete **"opening / inhabited / compass / convergence / orientation / layered"** from `ws2_many_witness` and it is the bare fact **"a reifyStep-produced relatum carrying a reified constituent and a base relatum are plain-bisimilar (`ws1_atomless_bisim`) yet not label-bisimilar under the rank labelling, on a carrier where rank is coarser than identity, GENERALLY (`ws2_many_general`)"**, a general rank-separation-and-reification fact on a coarse-rank carrier, which is NOT the two-Boolean labelled-separation fact of `ws4_label_survives_quotient` (Finding 1 satisfied). Delete the same words from `ws4_underdetermined` and it is **"two compasses on one structure, a defined equation over a constituency edge holding for one and failing for the other, both non-degenerate"**, the model-pair fact. Both survive the strip AS their named facts; the interpretive layer is earned, flagged, and the mathematical content is general-separation/reification/model-pair, not a rigged definition.

## Deliverable

`series-12/formal/Series12/ws2.lean` hosts the carrier (`WCar`, `aW`, `aW'`, `bW`, `cW`, `destW`, `sW`, `sW₂`, `reifyW`, `rankW`, `rankLift`, `destWL`), the carrier lemmas (`ws_witness_SHNE`, `ws_witness_reify_pointwise`, `ws_witness_plainOf`, `ws_witness_rank_is_tower`, `ws_witness_rank_noninjective`), `ws2_many_general`, `ws2_many_witness`, `ws2_reification_loadbearing`; `series-12/formal/Series12/ws4.lean` hosts `NonDegenerate`, `cHold`, `cFail`, `ws4_underdetermined` over the SAME carrier. Axiom check: `#print axioms ws2_many_witness` and `#print axioms ws4_underdetermined` on the standard three (`ws1_atomless_bisim` is axiom-clean; the finite carrier facts reduce via `decide`/`simp`). **The witness discharges inhabitability-with-plurality (a reified relatum carrying a reified constituent, rank non-injective, generalized) and underdetermination (a non-degenerate model pair over a genuine constituency edge) on one closed carrier, reification load-bearing, the total-`IsReify` deviation disclosed, every construction confined to an existential: the guard against the point-tag and the deciding-by-definition escapes, together.**
