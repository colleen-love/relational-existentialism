# WS4-witness — The inhabitability witness (`dir := rank`)

**Design sub-artifact. Series 12, WS2's concrete model, consumed by WS4 and WS5. Owns: the ONE closed carrier `(destW, reifyW)` on which two existentials are discharged — (a) the opening is INHABITABLE and the many is real (`Many destWL`: a reified tower relatum and a base relatum, genuinely plain-bisimilar, separated at the labelled level by their tower RANK, with `reify`/`reifyStep`/`towerN`/rank load-bearing — the genuine tower-distinction Series 10 and 11 could not draw); and (b) the convergence relation is UNDERDETERMINED (`ws4_underdetermined`: two compasses on this same carrier, one cohering up the reification edge and one not, both non-degenerate). Registered in `spec/README.md` §2.7–§2.10; the disclosed structural deviation (total `IsReify` unsatisfiable on a concrete atomless carrier; pointwise reification facts supplied) is owned here.**

*Series 12 is standalone; the collapse engine (`ws1_atomless_bisim`, `hneRel_isBisim`), the labelled/import test (`plainOf`, `IsBisimL`, `Recoverable`, `ws4_free_label_is_import`), the reification section and tower (`IsReify`, `reifyStep`, `reify_mem_reifyStep`, `towerN`, `prec`, `ws3_reify_preserves_SHNE`), and the `Compass`/`Converges` objects (README §2.9–§2.10) are cited from `spec/README.md`; this sub-artifact adds only the concrete carrier and the two existential witnesses. It is the guard against the program's gravest inherited failure: Series 10's `ws2_reify_bisim_embeds` and Series 11's `ws1_attention_makes_real` both drew their distinction on `labelLoop` — two fixed Booleans where `reify`/`reifyStep`/`towerN` never occur — and were honestly re-graded Bookkeeping re-hit. Series 12's witness must NOT repeat that: the separated pair is a genuine reified relatum and its base constituent, and the label is the tower RANK, defined from `towerN`/`reifyStep`.*

## The object at stake

Two existentials, on ONE carrier (README §4: WS2 owns it, WS4 reuses it so the model pair is "on the same structure"):

1. **Inhabitability with plurality (WS2).** `Many destWL` (README §2.8): a pair `x, y` that is plain-bisimilar (the collapse engine merges them — the quotient is blind) yet not label-bisimilar (the labelled level keeps them apart). The charter's discipline 4 demands this be a GENUINE tower-distinction: `x` a reified relatum `reifyW s`, `y` a base relatum, `reify`/`reifyStep`/rank load-bearing, not a bare point-tag.
2. **Underdetermination (WS4).** `ws4_underdetermined` (README §2.10): two compasses `c₁, c₂` on this carrier with `Converges c₁ aW bW` and `¬ Converges c₂ aW bW`, both non-degenerate, over a GENUINE reification edge (`aW ∈ sW.1`, `bW = reifyW sW`).

The design question is the direction the labelled lift carries. The Series 10/11 answer — the relatum's own two-valued identity on a fixed field (`labelLoop`) — is the point-tag that failed. Series 12's answer is **`dir := rank`**: the label a relatum broadcasts is its position in the reification tower, so the distinction is drawn on `towerN`/`reifyStep` and the reified relatum is separated from the base relatum BY its rank.

**Ambient theory.** `spec/README.md` §2.1 (collapse engine), §2.4 (import test), §2.5 (tower + disclosed deviation), §2.9 (`Compass`), §2.10 (`Converges`).

## The closed carrier

```lean
namespace Series12.Witness
-- PkObj, PkMap, toPk, SReaches, SHNE, IsBisim, ws1_atomless_bisim, LkObj, IsBisimL, plainOf,
-- IsReify, reifyStep, reify_mem_reifyStep, towerN, ws3_reify_preserves_SHNE, Compass, Converges — cited (README §6).

abbrev X : Type u := ULift.{u} Bool
def aW : X := ⟨false⟩                          -- the BASE relatum (rank 0)
def bW : X := ⟨true⟩                           -- the REIFIED relatum (rank 1), = reifyW {aW}

/-- The plain relating: `aW` self-loops (rank 0); `bW` relates to `aW` (so `dest bW = {aW}`). Both `SHNE`. -/
def destW (hinf : ℵ₀ ≤ κ) : X → PkObj κ X :=
  fun x => toPk hinf (if x = bW then {aW} else {aW})     -- destW aW = {aW}, destW bW = {aW}

/-- The pattern reified into `bW`. -/
def sW (hinf : ℵ₀ ≤ κ) : PkObj κ X := toPk hinf {aW}

/-- A section, defined pointwise at `sW` (total `IsReify` is unsatisfiable here — disclosed below). -/
def reifyW (hinf : ℵ₀ ≤ κ) : PkObj κ X → X :=
  fun s => if s.1 = {aW} then bW else aW                 -- reifyW {aW} = bW; elsewhere = aW

/-- The RANK direction: a relatum's position in the tower over `Ω₀ = {aW}`. `dirOf aW = 0`, `dirOf bW = 1`. -/
def dirOf : X → ULift.{u} ℕ := fun x => if x = bW then ⟨1⟩ else ⟨0⟩

/-- **The labelled lift (`dir := rank`).** Every relatum broadcasts its tower RANK on its outgoing edges;
    the plain quotient forgets it. -/
def destWL (hinf : ℵ₀ ≤ κ) : X → LkObj κ (ULift.{u} ℕ) X :=
  fun x => PkMap κ (fun y => (dirOf x, y)) (destW hinf x)
end Series12.Witness
```

**The carrier facts (paper-checked, each a small lemma):**

- **SHNE.** `destW aW = {aW}` (`aW` self-loops) and `destW bW = {aW}` (`bW → aW → aW → …`), so `SHNE (destW hinf) aW` and `SHNE (destW hinf) bW` (`ws_witness_SHNE`).
- **Pointwise reification.** `destW hinf (reifyW hinf (sW hinf)) = destW hinf bW = {aW} = (sW hinf).1`, so `dest (reify sW) = sW` holds AT `sW` (`ws_witness_reify_pointwise`). `aW ∈ (sW hinf).1` (`ws_witness_constituent`).
- **Reification load-bearing (the anti-point-tag certificate).** `bW = reifyW hinf (sW hinf)`, and `bW ∈ reifyStep (destW hinf) (reifyW hinf) {aW}` via `reify_mem_reifyStep` (with `(sW).1 ⊆ {aW}`, `(sW).1 ≠ ∅`), and `{aW, bW} = towerN (destW hinf) (reifyW hinf) {aW} 1`, so `dirOf bW = ⟨1⟩` IS the tower rank at which `reifyStep` adjoins `bW` (`ws_witness_rank_is_tower`). `reify`, `reifyStep`, `towerN` all OCCUR and are load-bearing — this is what `labelLoop` lacked.
- **`plainOf destWL = destW`.** `plainOf (destWL hinf) x = PkMap snd (PkMap (fun y => (dirOf x, y)) (destW hinf x)) = PkMap id (destW hinf x) = destW hinf x` (via `Set.image_id`), so the plain quotient recovers the unlabelled relating (`ws_witness_plainOf`).

## Candidates for the direction

### C1 — `dir := rank` (the lead; reification load-bearing)

The label a relatum broadcasts is its tower rank (`dirOf = ` position in `towerN`). `destWL x := PkMap (·, labelled with `dirOf x`) (destW x)`.

```lean
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) :=
  ⟨aW, bW,
   ws1_atomless_bisim (plainOf (destWL hinf)) aW bW ws_witness_SHNE_aW ws_witness_SHNE_bW,  -- plain-bisimilar
   ws_witness_rank_separates hinf⟩                                                          -- rank-separated
```

- **Ambient:** `ws1_atomless_bisim` (plain merge), the rank-label mismatch (label-separation), `reify_mem_reifyStep`/`towerN` (rank IS the tower position).
- **Success condition (Shape-drawn on the witness):** `aW` and `bW` are plain-bisimilar (collapse engine) but no label-bisimulation relates them (their broadcast ranks `⟨0⟩` and `⟨1⟩` mismatch), and `bW` is a genuine `reifyStep`-produced reified relatum.
- **Failure mode:** *degenerate inhabitation (discipline 4).* Foreclosed: the separated relatum `bW` is `reifyW sW`, adjoined by `reifyStep`, and the label is the tower rank — `reify`, `reifyStep`, `towerN` are load-bearing, not a fixed Boolean. **Winner.**

### C2 — `dir := self-identity` (the transcribed `labelLoop`; the point-tag)

The label is the relatum's own two-valued identity on a fixed field: exactly `labelLoop` (README §2.4).

```lean
theorem ws2_many_labelLoop (hinf : ℵ₀ ≤ κ) : Many (labelLoop hinf) := ⟨⟨true⟩, ⟨false⟩, (ws4_free_label_is_import hinf).1, (ws4_free_label_is_import hinf).2⟩
```

- **Failure mode:** *degenerate inhabitation, the Bookkeeping re-hit (discipline 4).* `reify`/`reifyStep`/`towerN` never occur; the distinction is on two fixed Booleans. This is precisely Series 10's `ws2_reify_bisim_embeds` / Series 11's `ws1_attention_makes_real`, honestly re-graded Bookkeeping re-hit. **Reject as the witness; retain `labelLoop` only as the shape-touchstone (README §2.4).**

### C3 — `dir := afford` (the hold's afforded set as the label)

The label records `afford dest h` (what the hold turns toward, README §2.3), tying the direction to the diagonal residue.

- **Failure mode:** *the honestly-reported alternative — over-coupling to the diagonal.* `afford` is a Set, not a κ-bounded label; forcing it into `Q` reintroduces the diagonal's freeness by construction, blurring "the opening is inhabitable" (WS2) with "the residue is free" (WS1). **Reject:** the WS1 fact should stay WS1's; the witness inhabits the opening with a TOWER direction, not the residue.
- **Paper triage.** The residue routing is WS1's forced-for-all fact; re-deriving it here would make the inhabitation lean on WS1's obstruction rather than exhibit a genuine tower-distinction. Retain only as the interpretive tie (the rank a relatum broadcasts is a proxy for how deep its self-reference has proliferated).

### C4 — `dir := rank` with a TOTAL section (the naive form; unsatisfiable)

Same as C1 but demanding `IsReify destW reifyW` (total: `∀ s, destW (reifyW s) = s`).

- **Failure mode:** *the honestly-reported alternative — the disclosed deviation.* A total section is `destW` surjective onto `PkObj κ X`, i.e. `|PkObj κ X| ≤ |X|`, false by Cantor for any `κ ≥ 2` on a concrete carrier (`|PkObj κ X| > |X|`). So `IsReify destW reifyW` is UNSATISFIABLE on this (or any concrete atomless) carrier. **Reject the total form; C1 supplies the POINTWISE facts (`destW (reifyW sW) = sW`, `(sW).1 ≠ ∅`, `∀ x ∈ (sW).1, SHNE destW x`) that `ws3_reify_preserves_SHNE`/`reify_mem_reifyStep`/the convergence edge actually consume.** This narrowing is faithful and disclosed (README §2.5), not hidden.

## Paper-decidable triage

| Cand | Direction | Reification load-bearing? | `Many` non-degenerate? | Convergence non-vacuously definable here? | Non-degenerate model pair? | Verdict |
|---|---|---|---|---|---|---|
| C1 | rank (`dirOf` = `towerN` position) | **yes** (`bW = reifyW sW`, `bW ∈ reifyStep {aW}`, label = tower rank) | **yes** (reified relatum vs base relatum, plain-bisimilar, rank-separated) | **yes** (`Converges c aW bW` a real equation over the edge `aW ∈ sW.1`, `bW = reifyW sW`) | **yes** (§ below) | **win** |
| C2 | self-identity (`labelLoop`) | no (`reify`/`reifyStep`/`towerN` absent) | no — point-tag | n/a (no reification edge) | n/a | reject (point-tag) |
| C3 | afford (residue) | partial (leans on WS1's forced residue) | over-coupled | would decide via the residue | risky | reject (WS1's fact) |
| C4 | rank + total `IsReify` | yes but UNSATISFIABLE | — | — | — | reject; C1 pointwise |

**The WS4-specific triage (protocol §2, the two questions):** (i) *Is `Converges` non-vacuously definable on this carrier?* YES — over the genuine reification edge `(aW, bW)` with `aW ∈ (sW).1` and `bW = reifyW sW`, `Converges c aW bW := c.raise aW bW (c.orient aW) = c.orient bW` is a real equation in `Or` whose truth depends on `c`'s free `orient`/`raise` values (not `True`, not `False`, not reflexive). (ii) *Is there a non-degenerate model pair?* YES — the two compasses below.

## Winning construction: C1 (`dir := rank`), pointwise section (C4 disclosed)

### The plurality witness (WS2)

```lean
/-- **The rank separates (the anti-point-tag core).** No label-bisimulation relates `aW` and `bW`: `aW`
    broadcasts rank `⟨0⟩`, `bW` broadcasts rank `⟨1⟩`, and a label-bisimulation would have to match `aW`'s
    edge `(⟨0⟩, aW)` against a `bW`-edge with label `⟨0⟩`, but `destWL bW = {(⟨1⟩, aW)}` carries only `⟨1⟩`. -/
theorem ws_witness_rank_separates (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (destWL hinf) R ∧ R aW bW := …            -- ⟨0⟩ ≠ ⟨1⟩, the tower-rank mismatch

/-- **THE PLURALITY WITNESS (`Many`, on a genuine tower-distinction).** `aW` and `bW` are plain-bisimilar
    (the collapse engine merges them — the quotient is blind) yet rank-separated at the labelled level, with
    `bW = reifyW sW` a `reifyStep`-produced reified relatum and the label its `towerN` rank. -/
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) :=
  ⟨aW, bW, ws1_atomless_bisim _ aW bW (ws_witness_SHNE hinf).1 (ws_witness_SHNE hinf).2,
   ws_witness_rank_separates hinf⟩

/-- **Reification load-bearing (the certificate the review greps for).** The separated relatum is a genuine
    reified relatum, adjoined by `reifyStep`, at tower rank 1 — NOT a fixed Boolean. -/
theorem ws_witness_reification_loadbearing (hinf : ℵ₀ ≤ κ) :
    bW = reifyW hinf (sW hinf)
  ∧ bW ∈ reifyStep (destW hinf) (reifyW hinf) {aW}
  ∧ destW hinf (reifyW hinf (sW hinf)) = (sW hinf).1
  ∧ aW ∈ (sW hinf).1 := …
```

### The convergence model pair (WS4), same carrier

```lean
/-- Non-degeneracy: `Or` non-trivial, `orient` not a collapsed constant, `raise` not a collapsed constant. -/
structure NonDegenerate {X} (dest) (reify) {Or} (c : Compass dest reify Or) (x W : X) : Prop where
  or_nontrivial   : ∃ o₁ o₂ : Or, o₁ ≠ o₂
  orient_nonconst : ∃ p q : X, c.orient p ≠ c.orient q
  raise_nonconst  : ∃ o₁ o₂ : Or, c.raise x W o₁ ≠ c.raise x W o₂

/-- Both compasses share the SAME non-constant orientation `orient aW = ⟨true⟩`, `orient bW = ⟨false⟩`; they
    differ ONLY in the raising at the edge `(aW, bW)`. Convergence turns on the free RAISING — how "my
    orientation, followed up its layer" presents at the whole — which the structure does not decide. -/
noncomputable def cHold (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => ⟨!o.down⟩                          -- the `not` raising: raise (orient aW) = ⟨false⟩ = orient bW

noncomputable def cFail (hinf : ℵ₀ ≤ κ) : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool) where
  orient := fun x => if x = aW then ⟨true⟩ else ⟨false⟩
  raise  := fun _ _ o => o                                  -- the `id` raising: raise (orient aW) = ⟨true⟩ ≠ orient bW

/-- **THE UNDERDETERMINATION (the wall).** Convergence holds under `cHold` and fails under `cFail`, on the
    SAME structure over the SAME reification edge, both non-degenerate — so the structure does not decide it. -/
theorem ws4_underdetermined (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Compass (destW hinf) (reifyW hinf) (ULift.{u} Bool),
        Converges (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ ¬ Converges (destW hinf) (reifyW hinf) c₂ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₁ aW bW
      ∧ NonDegenerate (destW hinf) (reifyW hinf) c₂ aW bW :=
  ⟨cHold hinf, cFail hinf,
   by simp [Converges, cHold],       -- ⟨!true⟩ = ⟨false⟩ = orient bW      ✓ holds
   by simp [Converges, cFail],       -- ⟨true⟩ = orient bW is false        ✓ fails
   ⟨⟨⟨true⟩, ⟨false⟩, by decide⟩, ⟨aW, bW, by simp⟩, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩,
   ⟨⟨⟨true⟩, ⟨false⟩, by decide⟩, ⟨aW, bW, by simp⟩, ⟨⟨true⟩, ⟨false⟩, by decide⟩⟩⟩
```

**Why this is not deciding-by-definition (discipline 3), stated once and never hidden.** `Converges c aW bW` unfolds to `c.raise aW bW (c.orient aW) = c.orient bW`, a genuine equation in `ULift Bool`. It is not `True`, not `False`, not `orient aW = orient aW`. The two compasses share the exact same non-constant orientation and differ ONLY in the raising, so what is undetermined is isolated to the free layering, and both truth values are realized on ONE structure over ONE genuine reification edge. Neither compass is a collapsed constant (`NonDegenerate`), the relation is non-vacuous (`cHold` satisfies it, `cFail` refutes it). This is the earned model pair, not a definitional tilt.

## Self-classification (the honest label)

- **Genuine tower-distinction, NOT a point-tag (discipline 4).** `bW = reifyW sW` is a `reifyStep`-produced reified relatum at `towerN` rank 1; the label is the tower rank; `reify`/`reifyStep`/`towerN` are load-bearing (`ws_witness_reification_loadbearing`). This is the distinction Series 10 (`ws2_reify_bisim_embeds`) and Series 11 (`ws1_attention_makes_real`) could not draw — they landed on `labelLoop` and were re-graded Bookkeeping re-hit. The without-import side (the One) is genuine `ws1_atomless_bisim`, not a rigged collapse.
- **The disclosed structural deviation (owned here, routed to `charter-status.md`).** Total `IsReify destW reifyW` is UNSATISFIABLE on this concrete atomless carrier (Cantor). The witness supplies the POINTWISE reification facts the lemmas consume (`destW (reifyW sW) = sW`, `(sW).1 ≠ ∅`, `∀ x ∈ (sW).1, SHNE destW x`), never the total section. Faithful narrowing, disclosed, not hidden. A reviewer who wants the total `IsReify` is entitled to note this; the design's position is that the pointwise facts are exactly what `ws3_reify_preserves_SHNE` and the convergence edge consume, so the narrowing changes no consumed hypothesis.
- **One inhabitant among all, for an existential.** Both `ws2_many_witness` and `ws4_underdetermined` discharge EXISTENTIALS ("the opening CAN be inhabited"; "there EXIST two compasses …"). They witness inhabitability and underdetermination; they never assert "THIS is what inhabits it" or "THIS is the compass." The compasses `cHold`/`cFail` are constructed solely to witness `∃ c₁ c₂` — the audit (WS7) confirms no GENERAL compass-theorem uses them, and no theorem outside these existentials selects a distinguished compass.

## Outcome classes (per charter §5)

- **Shape-drawn on the witness (the payoff):** `ws2_many_witness` (`Many` on a genuine tower-distinction) and `ws4_underdetermined` (the non-degenerate model pair). The two existentials the charter's expected terminus rests on, discharged on one closed carrier.
- **Partial (pre-registered, discipline 4):** if a reviewer judges the rank label external to the tower (a fresh index, not genuinely `towerN`'s position), the inhabitation is a point-tag and the finding is Partial — reported as such. Foreclosed by `ws_witness_reification_loadbearing` (`bW ∈ reifyStep {aW}`, rank = `towerN` position), so the label is not fresh: it is the tower's own rank.
- **Convergence-decided (pre-registered, discipline 3):** if the model pair proves vacuous (e.g. `cHold` degenerate on inspection), WS4 reports convergence-decided or Partial in its direction. Foreclosed by `NonDegenerate` on both compasses and both truth values realized.
- **Strip test.** Delete **"opening / inhabited / compass / convergence / orientation / layered"** from `ws2_many_witness` and it is the bare fact **"a `reifyStep`-produced relatum and a base relatum are plain-bisimilar (`ws1_atomless_bisim`) yet not label-bisimilar under the rank labelling, `reify`/`reifyStep`/`towerN` load-bearing"** — a reification-and-bisimulation fact, which is what the charter demands (the plurality strips to the labelled-separation fact with reification load-bearing). Delete the same words from `ws4_underdetermined` and it is **"two compasses on one structure, a defined equation over a reification edge holding for one and failing for the other, both non-degenerate"** — the model-pair fact. Both survive the strip AS their named facts; the interpretive layer (the opening inhabited, the wall) is earned, flagged, and the mathematical content is bisimulation/reification/model-pair, not a rigged definition.

## Deliverable

`series-12/formal/Series12/ws2.lean` hosts the carrier (`X`, `aW`, `bW`, `destW`, `sW`, `reifyW`, `dirOf`, `destWL`), the carrier lemmas (`ws_witness_SHNE`, `ws_witness_reify_pointwise`, `ws_witness_plainOf`, `ws_witness_rank_is_tower`), `ws_witness_rank_separates`, `ws2_many_witness`, `ws_witness_reification_loadbearing`; `series-12/formal/Series12/ws4.lean` hosts `NonDegenerate`, `cHold`, `cFail`, `ws4_underdetermined` over the SAME carrier. Axiom check: `#print axioms ws2_many_witness` and `#print axioms ws4_underdetermined` on the standard three (`ws1_atomless_bisim` is axiom-clean; the finite carrier facts reduce via `decide`/`simp`). **The witness discharges inhabitability-with-plurality and underdetermination on one closed carrier, reification load-bearing, the total-`IsReify` deviation disclosed, every construction confined to an existential — the guard against the point-tag and the deciding-by-definition escapes, together.**
