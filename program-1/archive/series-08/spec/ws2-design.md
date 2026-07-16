# WS2 — Perspective breaks the collapse

**Design doc. Series 08, the payoff. Owns: two finite holds of a shared relation, taken from opposite sides, fail "relate alike" so the Series 07 merge does not apply — plurality with no import (vs. weight, §4.1) and no leaf (vs. limit-atomlessness, §4.3), provided the asymmetry is free, which WS1 secures.**

*Series 08 is standalone; names transcribed into `series-08/formal/Series08/ws2.lean`, re-namespaced `Series08.WS2` (see `spec/README.md` §6). The witnesses — `labelLoop` (a free directed hold), `ws4_free_label_is_import`, `ws4_labelLoop_not_recoverable` — are **already built** in Series 07 `ws4.lean`; WS2 re-reads them as "distinct perspectives do not merge." WS2's plurality is stated with **freeness as a hypothesis discharged by WS1** (charter §6, protocol §4): perspective breaks the collapse only if the restriction is free, not recoverable.*

## The object at stake

The charter's Consequence 1 (§2, §5.2): the Series 07 engine merges nodes that relate alike (`ws1_atomless_bisim` + behavioral identity ⇒ equality). Perspective supplies two holds of the *same* relation — `x↾(x,y)` and `y↾(y,x)` — that do **not** relate alike, so the label-respecting bisimulation that would merge them fails. The teeth (§4.1): this counts as plurality-by-perspective, not plurality-by-import, **only if the directed hold is free** (not recoverable from the plain relating). WS1's spine secures freeness globally (no god's-eye node recovers all faces); WS2 exhibits the surviving pair and certifies which of three outcomes the code delivers: **monism-broken** (free perspective, distinct holds survive), **monism-reasserts** (the holds are recoverable, so they collapse — Series 07 wins), or **recoverable-hence-collapsed** (the honest failure). The whole payoff is the freeness verdict tied to the Series 04/WS4 semantic import test.

The design must be scrupulous about the strip test here, because this is the payoff most at risk of being the Series 07 free-label import wearing the word "perspective" (charter §4.1: "not a weight, not a coordinate riding alongside"). The honest position, pre-registered: **stripped of "perspective," the surviving pair is exactly `ws4_free_label_is_import`** — a plain-bisimilar-yet-label-distinct pair. What makes it *perspective* rather than a generic free-label import is that the label is the *source-direction of an edge already in the carrier* (not arbitrary external data), and that its freeness is the *global* no-god's-eye fact (WS1), not a local stipulation. WS2 states this distinction and does not oversell it; WS7 adjudicates whether it holds.

**Ambient theory.** `spec/README.md` §2.1–§2.3 (carrier, hold, the labelled face, `Recoverable`, `plainOf`, `IsBisimL`, `labelLoop`), and WS1's `ws1_no_gods_eye` / `ws1_directed_hold_free`. All transcribed.

## Candidates

### C1 — Distinct perspectives survive the merge = the free label survives (the lead)

```lean
theorem ws2_perspective_breaks_merge (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)      -- plain relating cannot tell them apart
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=          -- the directed holds do NOT relate alike
  ws4_free_label_is_import hinf
```
Two loops carrying their own direction as the hold: plain-bisimilar (the relating merges them, Series 07), yet no label-bisimulation relates them (the directed holds do not relate alike). So perspective distinguishes what relating cannot.

- **Ambient `F`:** the labelled functor; the hold is the direction-label; "relate alike" = `IsBisimL`.
- **Success condition:** the term typechecks (`ws4_free_label_is_import`). The merge that Series 07 forces on the plain relating **fails** once the directed hold is added.
- **Failure mode:** *recoverable-hence-collapsed.* If the directed hold were `Recoverable`, `ws4_recoverable_not_import` would turn the plain bisimulation into a label bisimulation and the pair would merge (monism reasserts). Ruled out by C2.

**Paper triage.** Decidable and built. **Winner (the payoff).**

### C2 — Freeness: the directed hold is not recoverable (the non-circularity core)

```lean
theorem ws2_free_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf
```
The plain relating cannot recover the direction (`ws4_label_survives_quotient`), so `Recoverable` fails — the hold is free, not a function of the relating. This is what separates perspective from Series 04's recoverable face (which collapsed).

- **Failure mode:** *freeness defined-in.* If `labelLoop` were free by a definitional gerrymander, this would be circular. It is not: freeness is a *theorem* (a plain-bisimulation with no label-bisimulation counterpart), the same shape Series 07 used for its non-circularity. **Winner (secures C1).**

### C3 — The asymmetry witness: `x↾(x,y) ≠ y↾(y,x)` at the level of afford

```lean
theorem ws2_perspective_asymmetry {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hxy : y ∈ (dest x).1) (hne : ¬ SReaches dest y x) :
    afford dest ⟨(x, y), hxy⟩ ≠ afford dest ⟨(y, x), _⟩   -- the two directed holds afford different fields
```
The literal charter statement: the hold from `x` toward `y` affords a different sub-field than the hold from `y` toward `x`, whenever the relating is genuinely directed (`y` reaches into `x`'s field but not conversely).

- **Failure mode:** *the ill-typed reverse hold.* `⟨(y,x), _⟩` requires `x ∈ (dest y).1`; on a genuinely asymmetric edge the reverse hold **does not exist**, so the inequality is vacuously mis-stated. Fix: state it as "either the reverse hold does not exist, or the affords differ" — i.e. asymmetry is *absence of the reverse hold or divergence of affords*. Constructible on `twoLoop`-with-a-sink but fiddly; the clean content is C1.

**Paper triage.** Faithful to the charter's `x↾(x,y) ≠ y↾(y,x)` wording and a genuine `afford`-level fact, but the typing of the reverse hold makes it the awkward statement. **Retain as the concrete illustration (with the existence-guard), C1 carries the payoff.**

### C4 — Plurality corollary: perspective yields distinct nodes with no import, no leaf

```lean
theorem ws2_plurality_by_perspective (hinf : ℵ₀ ≤ κ) :
    ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)                        -- (4) plural
  ∧ (∀ i, SHNE (plainOf (labelLoop hinf)) i)                     -- (3) atomless, no leaf
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)      -- distinct perspectives don't merge
  ∧ ¬ Recoverable (labelLoop hinf) := by                          -- free, not an import
  exact ⟨by decide, labelLoop_atomless hinf, ws4_label_survives_quotient hinf,
         ws4_labelLoop_not_recoverable hinf⟩
```
The full payoff bundled: plural, atomless (no leaf, §4.3), non-merging, and free (no import, §4.1). This is "distributed finite perspective" as a theorem — plurality that the collapse cannot dissolve.

- **Failure mode:** none beyond C1+C2 (it is their conjunction with `labelLoop_atomless`). **Winner (the bundled headline).**

### C5 — The abstract form: any free directed hold breaks any behaviorally-identified merge

```lean
theorem ws2_free_hold_survives {Q X : Type u} (dest : X → LkObj κ Q X)
    (hfree : ¬ Recoverable dest) : ∃ R, IsBisim (plainOf dest) R ∧ ¬ IsBisimL dest R
```
State it generally: freeness *is* the existence of a plain bisimulation that is not a label bisimulation — a directed hold the relating cannot recover.

- **Failure mode:** *unfolds to the definition of `Recoverable`.* `¬ Recoverable dest` is `∃ R, IsBisim (plainOf dest) R ∧ ¬ IsBisimL dest R` by `push_neg`, so C5 is `Recoverable`'s negation restated — true but definitional (the coincidence-rule trap). **Reject as a payoff; it is the *definition* of freeness, not a consequence.** Keep only as the bridge lemma naming what freeness means.

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | distinct perspectives don't merge | `ws4_free_label_is_import` | yes — built | **win (payoff)** |
| C2 | the directed hold is free | `ws4_labelLoop_not_recoverable` | yes — built | **win (non-circularity)** |
| C3 | `afford(x,y) ≠ afford(y,x)` | `afford`, existence-guard | yes; reverse-hold typing fiddly | illustration |
| C4 | plural ∧ atomless ∧ non-merging ∧ free | C1+C2+`labelLoop_atomless` | yes | **win (headline)** |
| C5 | free = plain-bisim-not-label-bisim | `push_neg` on `Recoverable` | yes but definitional | reject (bridge only) |

## Winning candidates: C1+C2+C4 (the payoff and its freeness), C3 as illustration

### Definitions and obligations (cite `spec/README.md` §2; consume WS1)

```lean
namespace Series08.WS2
-- carrier + labelled/face machinery, labelLoop, labelLoop_atomless, ws4_free_label_is_import,
-- ws4_labelLoop_not_recoverable, ws4_label_survives_quotient, ws4_recoverable_not_import,
-- Recoverable, plainOf, IsBisim, IsBisimL — transcribed (README §6); ws1_directed_hold_free from WS1.

/-- **D1 — perspective breaks the merge (C1).** Plain-bisimilar (Series 07 would merge them) yet the
    directed holds do not relate alike: the merge fails. -/
theorem ws2_perspective_breaks_merge (hinf : ℵ₀ ≤ κ) :
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ws4_free_label_is_import hinf

/-- **D2 — freeness (C2).** The directed hold is not recoverable — the relating does not carry it. -/
theorem ws2_free_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (labelLoop hinf) :=
  ws4_labelLoop_not_recoverable hinf

/-- **D4 — plurality by distributed perspective (C4).** Plural, atomless (no leaf), non-merging, free. -/
theorem ws2_plurality_by_perspective (hinf : ℵ₀ ≤ κ) :
    ((⟨true⟩ : ULift.{u} Bool) ≠ ⟨false⟩)
  ∧ (∀ i, SHNE (plainOf (labelLoop hinf)) i)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ ¬ Recoverable (labelLoop hinf) :=
  ⟨by decide, labelLoop_atomless hinf, ws4_label_survives_quotient hinf,
   ws4_labelLoop_not_recoverable hinf⟩

/-- **D3 — the freeness verdict (the three outcomes, tied to the import test).** The code delivers
    MONISM-BROKEN: the perspective is free (D2), so it survives (D1); it is NOT the recoverable face
    that collapses (`ws4_recoverable_not_import` is the OTHER horn, which Series 04's face fell under). -/
theorem ws2_monism_broken (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (labelLoop hinf)
  ∧ (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩) :=
  ⟨ws4_labelLoop_not_recoverable hinf, ws4_free_label_is_import hinf⟩
```

**D1/D2/D4** are transcriptions re-read; the mathematical work is Series 07's. **D3** is the freeness verdict the charter demands (§5.2): the code delivers **monism-broken** because the perspective is *free* (D2), landing on the `ws4_free_label_is_import` horn, not the `ws4_recoverable_not_import` horn where Series 04's recoverable face collapsed. The dependency on WS1 is explicit: freeness is sound only because no god's-eye node recovers all faces (`ws1_no_gods_eye`) — WS2 consumes that, and the cross-workstream review (protocol §D) must confirm the edge.

## Outcome classes (per charter §7)

- **Discharged (monism-broken):** D1, D2, D4, D3 — all transcribe built Series 07 lemmas; the plurality survives the merge and is free.
- **Partial (routed to WS7):** C3, the literal `afford(x,y) ≠ afford(y,x)`, if the reverse-hold existence-guard is not built; C1's non-merging pair carries the payoff regardless.
- **Refuted hypothesis / Failed (pre-registered honest alternative):** if the review finds the directed hold is *recoverable* after all (freeness defined-in, or the label is a function of the relating), then `ws4_recoverable_not_import` applies, the pair merges, and **monism reasserts** — reported as Failed for the payoff, routed to WS7 → `monismStands`. Not expected: freeness is a built theorem (D2), the same non-circularity shape Series 07 certified.
- **Strip test.** Delete **"perspective"** from `ws2_perspective_breaks_merge` and the statement is the bare **`ws4_free_label_is_import`**: *a plain-bisimilar pair with no label-bisimulation relating them.* The payoff **survives the strip** as a free-label fact — so the honest report is that the *mathematical* content is Series 07's free-label import, and "perspective / directed hold" is the earned reading (the label is an edge-direction intrinsic to the carrier, its freeness the global no-god's-eye fact of WS1). WS2 does **not** claim the strip leaves nothing; it claims the residue is a genuine plurality fact and names the interpretive surplus. This is the sharpest strip in the series and WS7 weighs it directly.

## Deliverable

`series-08/formal/Series08/ws2.lean`: transcribed labelled machinery (README §6); `ws2_perspective_breaks_merge` (D1), `ws2_free_not_recoverable` (D2), `ws2_plurality_by_perspective` (D4), `ws2_monism_broken` (D3), and (if built) `ws2_perspective_asymmetry` (C3, with existence-guard). Axiom check: `#print axioms ws2_perspective_breaks_merge` reduces through `ws4_free_label_is_import` to the standard three. **Depends on WS1** (`ws1_no_gods_eye` secures the global freeness D3 leans on); the ledger records the edge.
