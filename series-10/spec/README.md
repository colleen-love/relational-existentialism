# Series 10 — Design Index

**The anchor for the seven design docs. Fixes, once, every decision the workstreams share: the reifying κ-bounded carrier (the carrier home, settled in WS1 and ambient for all), the coalgebra `dest : Ω → PkObj κ Ω` and its section `reify : PkObj κ Ω → Ω` (the forward map of `Ω ≅ F(Ω)`, `dest ∘ reify = id`), the transcribed Series 09 diagonal layer (`insp`, `diag`, `SelfTotal`, `ws1_no_self_total_hold`, `residue`, `ws2_residue_free`), the reification tower and its single endogenous order `≺` (WS3, from reification sequences), the close-or-fold dichotomy with CLOSE-forbidden, the distributed-reflexivity (fold) predicate, and the two Series-10 discipline rules (growth must be strict-and-internal not a `List`; the bound must be reflexivity not cardinality).**

*Series 10 is standalone. It carries its own copy of every Series 09/08/07/04 lemma it needs; nothing is imported across series (the closure gate confirms it). The upstream names reproduced (transcribed verbatim into `series-10/formal/Series10/`, re-namespaced `Series10.WSn`) are listed in §6. Series 10's engine is genuinely new Lean: the reification map `reify : PkObj κ Ω → Ω` (§2.4), productive blindness (`ws1_free_reification`, WS1), strict internal growth (`ws2_growth_strict`, WS2), the reification tower and its endogenous order (WS3), close-or-fold with CLOSE-forbidden (WS4), and the fold kill condition (WS5) are Series 10 content. What is transcribed is the diagonal that makes reification genuine (`ws1_no_self_total_hold`, `ws2_residue_free`), the collapse it must break (`ws1_atomless_bisim`, `ws2_import_theorem_static`), the semantic import test that certifies freeness (`ws4_free_label_is_import`, `Recoverable`, `plainOf`), and — as the thing growth must NOT reduce to — the moving-hole shape Series 09 could only reach. Designs must be honest about which is which, and above all whether "growth" is a bigger carrier or a longer record.*

---

## 1. The one-paragraph design

Series 09 proved (`ws1_no_self_total_hold`) that on a hold-reflexive carrier no hold contains its own complete content — a Cantor/Lawvere diagonal independent of relational identity — and that the diagonal residue is FREE (`ws2_residue_free`), so plurality followed from one position. But the carrier was FIXED: the residue was a content no *existing* relatum realised, and re-diagonalization only relocated it (`ws4_residue_moves`), so a moving hole was still one hole, still collapsible by the engine (`ws1_atomless_bisim`). Series 10 keeps the diagonal and adds the one ingredient Series 09 lacked: **reification**, a map `reify : PkObj κ Ω → Ω` sending a pattern-of-relating `s` to the object `reify s` whose relating IS that pattern (`dest (reify s) = s`), the forward map of the founding equation `Ω ≅ F(Ω)`. Where Series 09 held `Ω` fixed and let a hole move, Series 10 lets each free residue REIFY into a new relatum, so the carrier grows. The spine (WS1, productive blindness) is a single positive: the reified self-relation is FREE — not recoverable from the plain relating — and this routes THROUGH the diagonal, because recoverability of the reified self-relation would reconstruct a self-total hold, which `ws1_no_self_total_hold` forbids (the exact shape of `ws2_residue_is_import`, transcribed and strengthened from residue-freeness to relatum-freshness). So blindness is productive: relating mints a genuinely new relatum precisely BECAUSE the relating cannot fully hold itself. From this one fact three consequences follow. **Genuine growth** (WS2): the reified relatum is a free label (`ws4_free_label_is_import`-shaped), so the extended carrier does not label-bisimulation-embed into the prior one — growth is strict and internal, a bigger world, not a longer `List` (the repair of Series 09's moving hole, the exorcism of the `accResidue` ghost). **Breaks the Series 07 collapse** (WS2): two objects with distinct reification histories differ in which relata exist for them, and existence-of-a-free-relatum is not bisimulation-invariant, so `BehaviorallyIdentified` does not merge them where the moving hole (bisimulation-invariant) was still merged. **The close-or-fold dichotomy** (WS4): under iterated reification exactly one of CLOSE (a totality-relatum, an object that is the totality of relata below it) or its negation holds, and CLOSE is FORBIDDEN by the diagonal (a totality-relatum is a self-total hold, `ws1_no_self_total_hold`), an Impossibility. The engine of all three is the reification tower (WS3), on which two obligations are discharged first — **(NL)** no leaf (a reified relatum has its own relating, `SHNE` preserved) and the **endogenous order** `≺` (from reification sequences, not an imported clock) — and one is the series' open law, the **fold** (distributed reflexivity, the crown), which WS5 *tests* against a pre-committed kill condition and never bakes into `reify` or the tower.

---

## 2. Ambient theory (shared by all workstreams) — fixed here once

### 2.1 The carrier home beneath the reification (transcribed from Series 09/08/07; ambient for all)

The underlying relating is Series 09's **plain `P_κ`-coalgebra**, transcribed verbatim. It supplies κ-boundedness (hence consistency: the reifying carrier has models) and the reaching/atomlessness/bisimulation vocabulary the escapes are argued in — above all the **collapse engine** growth must break.

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}          -- the κ-bounded powerset, F(Ω)
-- a plain coalgebra is  dest : X → PkObj κ X   (the relating)
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅   -- strong hereditary non-emptiness (no leaf)
def IsBisim (dest) (R) : Prop := …                                       -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
def hneRel (dest) : X → X → Prop := fun x y => SHNE dest x ∧ SHNE dest y
lemma hneRel_isBisim (dest) : IsBisim dest (hneRel dest)                  -- THE COLLAPSE ENGINE (Series 07/08)
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                          -- any two atomless states bisimilar
theorem ws2_import_theorem_static (dest) (hbehav : BehaviorallyIdentified dest)
    (hatom : ∀ x, SHNE dest x) : Subsingleton X                          -- THE COLLAPSE (Series 08): monism
```

**This is the home beneath the reification. No workstream may pick a different one.** The κ-bound on `PkObj` is load-bearing three times over: it is why the carrier is a *consistent object* (not Russell, charter §5.5), why `reify : PkObj κ Ω → Ω` can be a genuine injection (a `PkObj κ Ω ↪ Ω` exists for suitable κ where `Ω ↠ PkObj κ Ω` fails by Cantor, §2.4), and why each tower stage is a legitimate set (well-foundedness, WS3). It is **scaffolding** (charter §1): every Series 10 theorem must hold for all sufficiently large κ (the large-κ discipline, §5), and no result may rely on κ being small. `ws1_atomless_bisim` / `ws2_import_theorem_static` are the collapse Series 10 must break at the LABELLED level — growth is genuine only if the reified relatum escapes this engine.

### 2.2 The hold, the labelled functor, and the semantic import test (transcribed from Series 09/08/04; ambient for all)

```lean
/-- A hold `x↾(x,y)`: `x` restricting toward its successor `y`. Holding is primitive; reaching is derived. -/
def Hold (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }

/-- The LABELLED functor and the recoverable/free import test — the certificate that a distinction is a
    genuine import (free) rather than recoverable from the plain relating. The heart of WS2's growth check. -/
def LkObj (κ) (Q X) : Type u := PkObj κ (Q × X)
def IsBisimL (dest : X → LkObj κ Q X) (R) : Prop := …                     -- label-respecting bisimulation
def plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X := fun x => PkMap κ Prod.snd (dest x)  -- forget the label
def Recoverable (dest : X → LkObj κ Q X) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
theorem ws4_free_label_is_import (hinf) :                                 -- THE IMPORT TEST (positive horn)
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)        --   plain-bisimilar …
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)              --   … but NOT label-bisimilar: FREE
theorem ws4_recoverable_not_import (dest) (hrec : Recoverable dest) … :   -- THE IMPORT TEST (negative horn)
    (recoverable ⇒ the label collapses with the plain relating)
```

`ws4_free_label_is_import` is the shape Series 10's growth must take: a distinction (the reified relatum's identity) that is plain-bisimulation-invisible but label-bisimulation-visible — FREE, an import, not recovered. `ws4_recoverable_not_import` is its negative: a recoverable distinction collapses into the plain relating (bisimulation-invariant), which is exactly Series 09's moving-hole failure. **The bookkeeping check (protocol §0.4) is: does the reified relatum land on the `ws4_free_label_is_import` horn (genuine growth) or the `ws4_recoverable_not_import` horn (Bookkeeping)?**

### 2.3 The diagonal layer and residue-freeness (transcribed from Series 09 WS1/WS2; the guarantor of productive blindness)

```lean
def HoldPred (dest) : Type u := Hold dest → Prop                          -- a content: which holds a face contains
def diag (insp : Hold dest → HoldPred dest) : HoldPred dest := fun h => ¬ insp h h
def SelfTotal (insp) (t : Hold dest) : Prop := ∀ h, insp t h ↔ diag insp h    -- "contains its own complete content"
theorem ws1_no_self_total_hold (dest) (insp) : ¬ ∃ t, SelfTotal insp t    -- THE DIAGONAL (Series 09 spine)
theorem ws1_diagonal_not_bisim (dest) (insp) :                            -- and it is INDEPENDENT of relational identity
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ {Y} (d) (i), ¬ ∃ t, SelfTotal i t)
def residue (insp) : HoldPred dest := diag insp
def ResidueRecoverable (insp) : Prop := ∃ h, insp h = residue insp
theorem ws2_residue_free (dest) (insp) : ¬ ResidueRecoverable insp        -- THE FREE RESIDUE (Series 09 payoff)
theorem ws2_residue_is_import (dest) (insp) :                             -- freeness ⇒ recovery reconstructs self-total
    (¬ ∃ h, insp h = residue insp) ∧ (ResidueRecoverable insp → ∃ t, SelfTotal insp t)
```

This is the diagonal that makes reification productive rather than illusory. **`ws2_residue_is_import` is the exact template Series 10 strengthens:** Series 09 proved the residue's *content* free; Series 10 proves the *reified relatum* fresh, by the same route — recoverability would reconstruct a self-total hold. Productive blindness (WS1) is `ws2_residue_free` lifted from "content not realised by any hold" to "relatum not recoverable from any prior carrier."

### 2.4 The reification `reify : F(Ω) → Ω` (WS1 fixes it; ambient for all) — THE SERIES 10 CARRIER DECISION

Series 09's carrier could express a hole *moving* over a fixed field but not a relation *becoming a new object*, which is why its residue could only relocate (a moving hole is one hole). Series 10's one new structural ingredient repairs exactly this. A **reifying carrier** is a Series 09 coalgebra equipped with a **reification**, the forward map of `Ω ≅ F(Ω)`:

```lean
/-- **Reification.** A section of `dest`: a map from patterns-of-relating to the relatum that IS that
    pattern. `reify s` is the object relating exactly to `s`. The forward map of `Ω ≅ F(Ω)`, κ-bounded so
    the adjoined relatum stays in `PkObj κ`. It is NOT assumed an isomorphism (the diagonal forbids that,
    §4.5): only a section, hence injective, `dest` its retraction. -/
def IsReify (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Prop :=
  ∀ s : PkObj κ X, dest (reify s) = s

/-- `reify` is injective from `dest ∘ reify = id`: distinct patterns mint distinct relata. -/
theorem reify_injective (dest) (reify) (h : IsReify dest reify) : Function.Injective reify := …
```

**The carrier decision, stated once and consumed by WS2–WS6 (protocol §2, first design duty):** the ambient home is the triple `(dest, insp, reify)` — a κ-bounded coalgebra `dest : Ω → PkObj κ Ω`, the Series 09 inspection `insp : Hold dest → HoldPred dest`, and a reification `reify : PkObj κ Ω → Ω` with `IsReify dest reify`. WS1 fixes it; **no two workstreams may assume different reifications.** Four properties are load-bearing and each is a WS1/WS3 obligation, none assumed:

- **`reify` is a section, not an iso (§4.5, the razor).** `dest ∘ reify = id` (every pattern is reifiable, so reification genuinely grows the carrier — §4.5's not-too-weak horn). But `reify ∘ dest ≠ id` in general and `reify` is NOT surjective: a surjective `reify` would make `dest` injective, and combined with a totality-relatum would give a self-total hold (§4.5's not-too-strong horn, CLOSE-forbidden, WS4). The κ-bound is what makes a section *exist* (a `PkObj κ Ω ↪ Ω` for suitable κ) while forbidding the iso (Cantor blocks `Ω ↠ PkObj κ Ω` for the closing top). **This is the whole razor: strong enough to grow (section), weak enough not to close (not surjective).**
- **Free reification routes through the diagonal (§2, the spine).** The reified self-relation is not recoverable, and recoverability reconstructs a self-total hold (`ws2_residue_is_import`-shaped). WS1's `ws1_free_reification` proves it FROM `ws1_no_self_total_hold`, not a fresh assumption. This is what makes growth genuine (§4.3) and CLOSE forbidden (§4.5).
- **Reification preserves `SHNE` (§4.2, NL).** `dest (reify s) = s`, so if `s ≠ ∅` the reified relatum has successors; reifying non-empty patterns preserves hereditary non-emptiness. The reified relation is a full relatum, never a leaf. WS3's obligation.
- **The tower order is endogenous (§4.1).** `α ≺ β` iff `Ω_β` is reached by reifications from `Ω_α` — the reflexive-transitive closure of the reification step, from `reify` alone, no external ordinal clock. WS3 fixes it once; WS4 and WS5 consume the same `≺`.

### 2.5 The reification tower, its endogenous order, and the fold (WS3 fixes the tower/order; WS5 tests the fold) — THE SERIES 10 ORDER DECISION

The carrier grows by adjoining, at each stage, the relata reifiable from the relata present. Modelled as an ordinal-indexed family of **subcarriers** of a fixed ambient universe `Ω` (so growth is the SAME carrier extending, not an external record — the §4.3 discipline), each `Ω_α : Set Ω` closed under `dest`:

```lean
/-- One reification step: adjoin every relatum reifiable from a κ-bounded pattern drawn from `Ω_α`. The
    carrier EXTENDS; nothing is recorded on the side. -/
def reifyStep (dest) (reify) (Ωα : Set Ω) : Set Ω :=
  Ωα ∪ { x | ∃ s : PkObj κ Ω, (s.1 ⊆ Ωα) ∧ x = reify s }
/-- The tower: an ordinal-indexed family, `Ω_{α+1} = reifyStep Ω_α`, unions at limits. -/
def tower (dest) (reify) (Ω₀ : Set Ω) : Ordinal → Set Ω := …               -- transfinite recursion, WS3
/-- **THE TOWER ORDER, derived once.** `Ωα ≺ Ωβ` iff `Ωβ` is reached by reification steps from `Ωα`.
    Endogenous: the reflexive-transitive closure of `reifyStep`, from `reify` alone — no external index. -/
def prec (dest) (reify) : Set Ω → Set Ω → Prop :=
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)
```

**This is the tower order (protocol §2, second design duty). WS3 (the tower) and WS4 (close-or-fold) both consume `prec`; neither may redefine it, and neither may substitute an external `Ordinal`-index.** The imported-ordinal branch (`≺` := a stamped stage counter, the Series 03/05 trap) is designed in as a **refuted** failure mode (`ws3_imported_order_refuted`), never a fallback. The **fold** (crown) is measured SEPARATELY from the tower, as distributed reflexivity, so it stays testable:

```lean
/-- CLOSE: some reachable stage contains a TOTALITY-RELATUM — an object that is the totality of relata
    below it (its relating enumerates the stage). Forbidden by the diagonal (WS4). -/
def Closes (dest) (reify) (Ω₀) : Prop := ∃ α, ∃ t ∈ tower dest reify Ω₀ α, IsTotalityRelatum … t
/-- FOLD (the crown, distributed reflexivity): every free residue opened at a stage is REIFIED into the
    carrier at a LATER stage — each stage's incompletability folds back into range of the prior structure,
    a bound that is everywhere rather than at a summit. Measured as reflexivity, NOT as "stayed under κ". -/
def Folds (dest) (reify) (Ω₀) : Prop := ∀ α, ∀ (free residue r at stage α), ∃ β, α ≺ β ∧ r reified in Ω_β
```

`Folds` is a fact about the reification step (each residue is later reified), an **endogenous reflexivity**, not a cardinality bound. **The cardinal sin (charter §4.4, protocol §0.5): a fold that unfolds to "the tower stayed under the imposed κ."** Series 10 forbids this: `Folds` says "every residue is reified at a later stage," which is refutable by exhibiting a proliferating tower with an un-reified residue (κ removed). WS5 runs the kill condition and reports `discharged_on_scaffold` / `fatal` / `partialV`.

---

## 3. The verdict type (WS7)

```lean
inductive Series10Verdict
  | reificationEstablished  -- productive blindness routes through the diagonal, growth strict-and-internal
                            --   (not a List), CLOSE forbidden, fold settled (D-on-scaffold / FATAL / Partial),
                            --   no result relies on small κ
  | bookkeeping             -- "growth" is a lengthening List / index while the carrier is bisimulation-constant
                            --   (Series 09's moving hole re-hit at the carrier level) — the payoff failed
  | selfTotalSmuggled       -- `reify` closes the tower: a totality-relatum exists, i.e. a self-total hold was
                            --   smuggled past the diagonal — a `reify` DESIGN DEFECT, not monism re-derived
  | kappaByFiat             -- "self-bounding" unfolds to "bounded by the imposed κ" (Series 08's conservation
                            --   sin relocated) — a SERIOUS finding
  | Circular                -- freeness free-by-fiat, growth defined-in, or the fold baked into `reify` — a WS7 finding
  deriving DecidableEq
```

`reificationEstablished`: WS1 productive blindness discharged AND certified to route through the diagonal (`ws1_no_self_total_hold` / `ws2_residue_is_import`), WS2 growth strict-and-internal (label-bisimulation-non-embedding, not a `List`), WS4 CLOSE forbidden as an Impossibility and the dichotomy exhaustive, WS5 fold settled to one of {`discharged_on_scaffold`, `fatal`, `partialV`} by the kill condition, and every theorem holding for all large κ. `bookkeeping`: the Series-10-specific honest failure — growth reduces to a lengthening record while the carrier is bisimulation-constant (Series 09's moving hole re-hit; charter §5.5, naming it is first-class). `selfTotalSmuggled`: `reify` mis-defined so the tower closes (a totality-relatum, a self-total hold past the diagonal) — a design defect, reported as such, NOT as monism. `kappaByFiat`: the fold rests on small κ. `Circular`: a WS7 finding (freeness/growth/fold defined-in). The verdict is a function of a mechanized `Audit` certificate whose every field is a theorem (transcribing Series 07/08/09's `Audit`/`verdict` pattern), so it cannot be hand-set — and its spine field carries the *routes-through-the-diagonal* certificate, its growth field the *label-bisimulation-non-embedding* certificate.

---

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk |
|---|---|---|---|---|
| WS1 | reifying carrier + `reify` + productive blindness | `ws1_no_self_total_hold`, `ws2_residue_is_import`, `Recoverable`/`plainOf` | `ws1_free_reification`, `ws1_close_forbidden_local`, `ws1_reify_section_not_iso` | freeness a fresh assumption (not through the diagonal); `reify` too weak (bookkeeping) or too strong (closes) |
| WS2 | genuine growth, not bookkeeping | WS1 freeness, `ws4_free_label_is_import`, `ws1_atomless_bisim` | `ws2_growth_strict`, `ws2_history_not_merged`, `ws2_growth_is_free_label` | growth is a `List` / bisim-embeds (Bookkeeping); merges at the plain level |
| WS3 | the reification tower + endogenous order + (NL) | WS1 `reify`, `SHNE`, `IsReify` | `ws3_reify_preserves_SHNE` (NL), `ws3_order_endogenous`, `ws3_imported_order_refuted`, `ws3_tower_well_founded` | order an imported ordinal; a reified leaf; tower ill-defined (proper class) |
| WS4 | close-or-fold dichotomy + CLOSE-forbidden | WS3 tower + `prec`, `ws1_no_self_total_hold` | `ws4_dichotomy`, `ws4_close_forbidden`, `Folds` (predicate only) | CLOSE asserted / built into `reify`; fold defined as staying-under-κ |
| WS5 | the fold-or-fatal fork | WS3 tower, WS4 `Folds` | `ws5_kill_condition`, `ws5_fold_verdict` (D-on-scaffold/FATAL/Partial) | fold assumed (crown baked in); κ-by-fiat; small-κ reliance |
| WS6 | the heuristic ceiling + Series 11 handoff | WS1, WS5 scope | `ws6_provable_core`, `ws6_universal_theses`, `ws6_series11_handoff` | universal blindness / universal fold not rangeable |
| WS7 | bookkeeping + κ-by-fiat + import + verdict | all | `Series10Verdict`, `ws7_verdict`, the `Audit`, `ws7_bookkeeping_check`, `ws7_kappa_discipline` | verdict rests on a bookkeeping growth, a κ-by-fiat fold, or a smuggled self-total hold |

---

## 5. Predicted headline

WS1's productive blindness is genuinely new Lean and its target is the whole engine: **`ws1_free_reification` Discharged — the reified self-relation is FREE, routing through the diagonal (`ws2_residue_is_import`-shaped: recoverability reconstructs a self-total hold, forbidden by `ws1_no_self_total_hold`)** — so the reification is irreducible, a genuinely new relatum, and the carrier genuinely grows. Its *strip test* will show the mathematical content is the bare Series 09 freeness fact ("the residue / the reified content is not in the range of the prior relating") lifted to relatum-freshness, with "reification / productive blindness / the growing self" as the earned interpretive layer; the design says so, and — as in Series 09 — surviving the strip *as a freeness fact routed through the diagonal* is what the charter demands. WS2's strict-growth is the payoff most at risk: it is Discharged **at the labelled level** (`ws2_growth_is_free_label`, the reified relatum is a free label, so the extended carrier does not label-bisimulation-embed into the prior), with the honest disclosure that at the PLAIN level the collapse engine (`ws1_atomless_bisim`) still merges — so genuine growth lives exactly where the free label lives, and the strip test flags that "growth," deleted, leaves `ws4_free_label_is_import`. **Bookkeeping is the pre-registered honest alternative** if a reviewer judges the label external (Series 09's moving hole re-hit one level up); the design pre-registers it and WS7 adjudicates. WS4's **CLOSE-forbidden is Discharged as an Impossibility** (a totality-relatum is a self-total hold, `ws1_no_self_total_hold`), the cleanest result of the series. The genuinely open workstream is WS5's fold. **Predicted verdict: `reificationEstablished`** with the fold **Discharged-on-scaffold at the step-reflexivity level, Partial in the universal** (distributed reflexivity — every free residue is reified at a later stage — holds per-step on the bounded carrier, measured as reflexivity not cardinality; whether the whole tower folds at every limit and survives κ-removal is Series 11's, a defended thesis, WS6). This mirrors Series 09's WS5 outcome (Refuted-universal, Discharged-on-a-class → Partial) with the honest fork left open. `bookkeeping` only if WS2's growth is found to bisim-embed (the SERIOUS finding the series exists to test, not expected but genuinely live); `selfTotalSmuggled` only if `reify` turns out to close the tower (a design defect, guarded by the section-not-iso razor); `kappaByFiat` only if the fold rests on small κ (the reflexivity-not-cardinality definition guards it); `Circular` only if the audit finds freeness/growth/fold defined-in (the designed guards make it not expected). The one genuine scope hazard (charter §5.3): productive blindness may be Discharged only for a specific `reify` witness on a specific carrier, with the universal "every κ-bounded reifying carrier grows freely" left a defended thesis (WS6) — which still advances the program, since ONE genuinely growing free tower is what Series 09's fixed field could not produce.

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-10/formal/Series10/`)

Re-namespaced `Series10.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation (Series 09 `ws1` / Series 08 `ws1` / Series 07 `ws1`):** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `SHNE.ne_empty`, `SHNE.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim` (**the collapse engine**), `ws1_atomless_bisim` (any two atomless states bisimilar), `twoLoop` (+ `twoLoop_HNE`).
- **The collapse (Series 09 `ws1` / Series 08 `ws1`):** `ws1_recovers_static`, `ws2_import_theorem_static` (**the collapse**, monism from behavioral identity + atomlessness).
- **The labelled / face machinery and the semantic import test (Series 09 `ws1` / Series 08 `ws1` / Series 04 `ws4`):** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `labelLoop`, `ws4_free_label_is_import` (**the import test**, positive horn — the shape of genuine growth), `ws4_recoverable_not_import` (negative horn — the shape of Bookkeeping), `ws4_label_survives_quotient`, `ws4_labelLoop_not_recoverable`.
- **The diagonal spine and the free residue (Series 09 `ws1`/`ws2`) — the guarantor of productive blindness:** `Hold`, `afford`, `ws1_hold_forced`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold` (**the diagonal**), `ws1_diagonal_not_bisim` (**its independence**), `ws1_insp_not_surjective`, `ws1_unrestricted_carrier_inconsistent`, `inspLoop`, `ws1_holdreflexive_not_selfloop`, `residue`, `ResidueRecoverable`, `ws2_residue_distinct`, `ws2_residue_free` (**the free residue**), `ws2_residue_is_import` (**the template**: recovery reconstructs a self-total hold).
- **The coincidence witness — transcribed as a negative touchstone:** `Symmetric`, `ws1_symmetric_states_bisimilar` (kept so WS7 can certify Series 10's payoffs do not launder through it).
- **Verdict (Series 07/08/09 `ws7`):** the `Audit`/`verdict` certificate pattern, re-pointed to `Series10Verdict` (§3).

Nothing is `import`ed across series; each is copied into the relevant `series-10/formal/Series10/wsN.lean` and re-namespaced, and the closure gate confirms it. The **genuinely new Series 10 Lean** is the reification `reify`/`IsReify` (§2.4), productive blindness (WS1), strict internal growth (WS2), the reification tower and endogenous order (WS3), close-or-fold with CLOSE-forbidden (WS4), and the fold kill condition (WS5).

---

*Design index for Series 10. Read this before any `wsN-design.md`; the shared objects (the reifying carrier `(dest, insp, reify)`, the diagonal layer, the reification tower, the ONE order `≺`, the fold predicate, the verdict) are defined here once and cited. The two discipline rules — growth is strict-and-internal (a bigger carrier, not a `List`: the bookkeeping check, PROMOTED to first-class) and the bound is reflexivity (not the imposed κ: the κ-by-fiat check, PROMOTED to first-class) — are the spine of the review. `reify` is a section not an iso (strong enough to grow, weak enough not to close), and the fold is refuted-or-proved never assumed. No em dashes in final academic paper copy; this working design index is not final copy.*
