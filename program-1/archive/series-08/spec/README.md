# Series 08 — Design Index

**The anchor for the seven design docs. Fixes, once, every decision the workstreams share: the carrier home, the hold/restriction primitive (`x↾(x,y)`, holding-first, charter §3), the re-restriction map, the single endogenous order `≺`, the transcribed Series 07/04 machinery, and the two Series-08 discipline rules (no conservation-by-fiat, freeness-refuted-or-proved). `ws1…ws7-design.md` are written against this file; a shared object is defined here and cited, never redefined.**

*Series 08 is standalone. It carries its own copy of every Series 07/04 lemma it needs; nothing is imported across series (the closure gate confirms it). The upstream names reproduced (and transcribed verbatim into `series-08/formal/Series08/`, re-namespaced `Series08.WSn`) are listed in §6. Much of WS1–WS2 is a **reframing** of already-built Series 07 machinery (the recoverable-vs-free label test); the genuinely new Lean is WS3 (the re-restriction map and the endogenous order), WS5 (the conservation kill condition), and WS7 (the freeness/conservation audit). Designs must be honest about which is which.*

---

## 1. The one-paragraph design

Series 07 proved (`ws2_import_theorem`) that on a plain `P_κ`-coalgebra, behavioral identity plus every-moment atomlessness forces subsingleton-ness: the atomless, groundless, plain world is the One. Series 08 keeps that carrier and adds one primitive it did not consider: the **hold** `x↾(x,y)`, a *directed* restriction of the relating (Series 04's face, now read as perspectival). The spine (WS1) is a single negative: the node that holds **all** faces **symmetrically** — the god's-eye node — is exactly a *recoverable*-face coalgebra, so by the transcribed engine (`ws4_recoverable_atomless_collapses`) it is a subsingleton; it collapses to the One and loses the faces it was meant to contain. Hence **no relationally-identified god's-eye node exists** (Impossibility proved), and this is what makes a *directed* hold **free** (not recoverable): freeness is global, secured by the non-existence of the totality that would recover every face at once. From this one fact three consequences follow. **Plurality** (WS2): two holds of a shared relation taken from opposite sides need not relate alike (`x↾(x,y)` vs `y↾(y,x)`), so the Series 07 merge does not apply — *provided* the asymmetry is free, which WS1 secures and WS2 witnesses (`ws4_free_label_is_import`, re-read). **Forced dynamics** (WS3): a single finite hold affords only a `< κ`-bounded slice, but the atomless field beneath it never bottoms out (`SHNE`), so no hold is `SReaches`-closed; resolving deeper requires *moving to a new hold* — re-restriction — and the re-restriction relation never terminates. **Depth/layering** (WS4): each re-restriction step resolves a deeper node by discarding the sibling alternatives at the current focus; depth is the length of the re-restriction chain, and reachability (`SReaches`) is exactly its trace. The engine of all three is the **re-restriction map** (WS3), on which two obligations are cheap and discharged first — **(NL)** no leaf (`SHNE` preserved) and **(NF)** not-a-function — and one is the series' open law, **(CB)** conservation of breadth, which WS5 *tests* against a pre-committed kill condition and never bakes into the map.

---

## 2. Ambient theory (shared by all workstreams) — fixed here once

### 2.1 The carrier home (WS1 fixes it; ambient for WS2–WS6)

The underlying relating is Series 07's **plain `P_κ`-coalgebra**, transcribed verbatim:

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}          -- the κ-bounded powerset
-- a plain coalgebra is  dest : X → PkObj κ X
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅   -- strong hereditary non-emptiness
def IsBisim (dest) (R) : Prop := …                                       -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
def hneRel (dest) := fun x y => SHNE dest x ∧ SHNE dest y
lemma hneRel_isBisim (dest) : IsBisim dest (hneRel dest)                  -- the engine's core
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                          -- THE ENGINE
```

**This is the home. No workstream may pick a different one.** The terminal/QPF `νPk` is *not* transcribed (Series 07 already showed the abstract `BehaviorallyIdentified` form subsumes it); Series 08 works over an arbitrary `dest : X → PkObj κ X`.

### 2.2 The hold / restriction primitive (WS1 fixes it; holding-first, charter §3)

A **hold** is a directed edge, read as *the source restricting the relation toward the target*. Following Series 04's `face` (`x↾(x,y)` = the part of `x` routed through its edge to `y`):

```lean
/-- A hold `x↾(x,y)`: `x` restricting toward its successor `y`. Holding is primitive; reaching is derived. -/
def Hold (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }
/-- What the hold affords: the sub-field it turns toward (Series 04's `face`, forced by `dest` alone). -/
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }
```

`afford` is a *function of `dest`* (forced, not annotated): `ws1_hold_forced` re-proves Series 04's `ws1_face_forced` on this carrier. Reaching is derived from holds (§2.4), never axiomatic (charter §3).

**Perspective** is the *directedness*: the hold `(x,y)` (x's face toward y) is a different object from `(y,x)` (y's face toward x). The two are carried by the Series 07 **labelled functor** `LkObj κ Q X = PkObj κ (Q × X)`, with `Q` recording the source-direction; `plainOf` forgets it. A face is **recoverable** (`Recoverable dest`) iff the direction adds no constraint the plain relating does not already impose — the god's-eye/symmetric case — and **free** otherwise. This is the Series 04/WS4 semantic import test, transcribed, and it is the hinge of the whole series (§2.3).

### 2.3 The god's-eye node and freeness (WS1 spine; ambient for WS2, WS5, WS7)

```lean
def LkObj (κ) (Q X) : Type u := PkObj κ (Q × X)
def plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X := fun x => PkMap κ Prod.snd (dest x)
def IsBisimL (dest) (R) : Prop := …                     -- label-respecting bisimulation
def BehaviorallyIdentifiedL (dest) : Prop := ∀ R, IsBisimL dest R → ∀ x y, R x y → x = y
def Recoverable (dest) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
theorem ws4_recoverable_atomless_collapses (dest) (hrec : Recoverable dest)
    (hbehav : BehaviorallyIdentifiedL dest) (hatom : ∀ x, SHNE (plainOf dest) x) : Subsingleton X
theorem ws4_free_label_is_import (hinf) :                                   -- the free directed hold survives
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)
```

**A god's-eye node = a symmetric hold = a recoverable face.** Holding *all* faces *symmetrically* means the direction-label distinguishes nothing the relating does not — precisely `Recoverable`. Then `ws4_recoverable_atomless_collapses` makes it a subsingleton: the totality annihilates its faces (charter §2 spine). **Freeness of distributed perspective** is the contrapositive at the level of the whole system: a *directed* hold whose asymmetry is not recoverable (`labelLoop`, `¬ Recoverable`) survives the merge — and no single node recovers all such holds, because the node that would is the god's-eye node, which does not exist. Freeness is thus **global (no-totality), not local**: each face is locally recoverable (Series 04), but the family of all faces is not recoverable by any one node. This distinction is load-bearing and is stated honestly in WS1/WS2, never hidden.

### 2.4 The re-restriction map and the ONE endogenous order (WS3 fixes it; ambient for WS4, WS5)

Re-restriction narrows a hold toward a deeper node by *following its edge*:

```lean
/-- Re-restriction step: `x↾(x,y)  ↝  y↾(y,z)`. Narrow from x's hold toward y to y's hold toward z (deeper). -/
def ReReStep (dest) : Hold dest → Hold dest → Prop :=
  fun h h' => h'.1.1 = h.1.2 ∧ (h'.1.2 ∈ (dest h'.1.1).1)     -- the new source is the old target
/-- THE ORDER, derived once. `m ≺ m'` iff `m'` is reached by a re-restriction sequence from `m`. Endogenous:
    the reflexive-transitive closure of `ReReStep`, defined from `dest` alone — no external stage index. -/
def prec (dest) : Hold dest → Hold dest → Prop := Relation.ReflTransGen (ReReStep dest)
```

**This is the order. WS3 and WS4 both consume `prec`; neither may redefine it, and neither may substitute an external `ℕ`-index.** The imported-index branch (`≺` := a stamped stage counter, the Series 05 trap) is designed in as a *refuted* failure mode (`ws3_imported_index_refuted`), never a fallback. **Breadth** is measured *separately* from the map, so conservation stays testable (§2.5).

### 2.5 The breadth measure and the conservation discipline (WS5 owns; charter §5.4)

```lean
/-- Breadth AT a hold: the alternatives available for the next re-restriction — the successors of the target. -/
def breadth (dest) (h : Hold dest) : Cardinal := Cardinal.mk (↥(dest h.1.2).1)
```

`breadth` is defined from `dest`, **outside** `ReReStep`. Conservation (CB) is then the *fact* "`breadth` does not increase along `prec`" — a statement **about** the map, provable or refutable, never a clause **inside** it. **The cardinal sin (protocol §0.4): a re-restriction definition that deletes the chosen successor from the sibling set, so foreclosure holds by unfolding the definition.** Series 08 forbids this: `ReReStep` follows the edge and touches no sibling set. WS5 runs the kill condition — exhibit a re-restriction that opens depth without foreclosing breadth — and reports `Refuted` / `Discharged` / `Partial`.

---

## 3. The verdict type (WS7)

```lean
inductive Series08Verdict
  | perspectiveEstablished   -- spine lands, plurality free, dynamics forced, conservation SETTLED (any of D/R/P)
  | monismStands             -- the god's-eye node was constructible OR perspective proved recoverable
  | Circular                 -- freeness or conservation holds only by a definitional exclusion — sharp negative
  deriving DecidableEq
```

`perspectiveEstablished`: WS1 spine discharged, WS2 freeness non-circular, WS3 order endogenous and (NL)+(NF) discharged, WS5 conservation settled to one of {Discharged, Refuted, Partial} by the kill condition. `monismStands`: the honest-failure outcome (charter §8.1). `Circular`: freeness defined-in or conservation baked-in (a WS7 finding). The verdict is a function of a mechanized `Audit` certificate whose every field is a theorem (transcribing Series 07's `Audit`/`verdict` pattern), so it cannot be hand-set.

---

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk |
|---|---|---|---|---|
| WS1 | carrier + hold + the no-god's-eye spine | `ws4_recoverable_atomless_collapses`, `ws1_atomless_bisim` | `ws1_no_gods_eye`, `ws1_hold_forced`, `ws1_perspective_asymmetry` | Spinozist retreat (god's-eye excluded by fiat, not collapsed) |
| WS2 | plurality by free perspective | WS1 freeness, `ws4_free_label_is_import`, `ws4_labelLoop_not_recoverable` | `ws2_perspective_breaks_merge`, `ws2_free_not_recoverable` | perspective recoverable-hence-collapsing (monism reasserts) |
| WS3 | re-restriction map + endogenous order | carrier, `SHNE.succ`, `SReaches` | `ws3_rerestriction_no_leaf`, `ws3_rerestriction_not_function`, `ws3_dynamics_forced`, `ws3_order_endogenous` | order is a painted-on / imported index |
| WS4 | narrowing = depth; reach as trace | WS3 map + order | `ws4_depth_is_narrowing`, `ws4_reaches_is_trace`; universal Partial | depth-as-narrowing is a bare reachability fact |
| WS5 | the conservation fork | WS3 map, `breadth` | `ws5_kill_condition`, `ws5_conservation_verdict` (D/R/P) | conservation assumed-in-a-definition |
| WS6 | the heuristic ceiling | WS4, WS5 | `ws6_provable_core`, `ws6_universal` (heuristic) | universal not rangeable |
| WS7 | freeness/conservation audit + verdict | all | `Series08Verdict`, `ws7_verdict`, the `Audit` | verdict rests on a fiat exclusion |

---

## 5. Predicted headline

WS1's spine and WS2's plurality are near-reframings of built Series 07 machinery (`ws4_recoverable_atomless_collapses`, `ws4_free_label_is_import`), so they discharge cleanly *as theorems* — but their *strip tests* will show the mathematical content is the recoverable/free-label collapse, with the "perspective/god's-eye/face" reading as the earned interpretive layer; the designs say so. The genuinely new Lean is WS3's endogenous order and forced-dynamics non-termination, and WS5's conservation kill condition. **Predicted verdict: `perspectiveEstablished`** with conservation **Refuted-in-general, Discharged-on-a-finite-breadth-subclass (Partial)** — the honest expectation is that a free atomless field does *not* conserve breadth (a constant-branching witness opens depth foreclosing nothing), so the "self-limiting universe" is retracted and the bound downgraded to mere boundedness, exactly the kind of first-class refutation the charter pre-registers. `monismStands` only if the god's-eye node turns out constructible (not expected); `Circular` only if the audit finds freeness or conservation defined-in (the two designed guards make it not expected).

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-08/formal/Series08/`)

Re-namespaced `Series08.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation (Series 07 `ws1`):** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `SHNE.ne_empty`, `SHNE.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim`, `ws1_atomless_bisim`, `ws1_recovers_static`, `twoLoop` (+ `twoLoop_HNE`, `twoLoop_true_bisim`).
- **The labelled/face machinery (Series 07 `ws4`):** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `labelLoop`, `facedLoop`, `ws4_free_label_is_import`, `ws4_recoverable_not_import`, `ws4_recoverable_atomless_collapses`, `ws4_labelLoop_not_recoverable`, `ws4_facedLoop_recoverable`.
- **The collapse (Series 07 `ws2`):** `ws2_import_theorem`, `ws2_import_theorem_static`.
- **The face primitive (Series 04 `ws1`):** `face` / `RoutedThrough` / `ws1_face_forced` — re-expressed as `Hold` / `afford` / `ws1_hold_forced` on this carrier (§2.2).
- **Verdict (Series 07 `ws7`):** `ProgramVerdict` and the `Audit`/`verdict` certificate pattern, re-pointed to `Series08Verdict` (§3).

Nothing is `import`ed across series; each is copied into the relevant `series-08/formal/Series08/wsN.lean` and re-namespaced, and the closure gate confirms it.

---

*Design index for Series 08. Read this before any `wsN-design.md`; the shared objects (the carrier, the hold `x↾(x,y)`, the re-restriction map, the ONE order `≺`, the breadth measure, the verdict) are defined here once and cited. The two discipline rules — freeness refuted-or-proved (never defined-in), conservation tested-or-refuted (never baked-in) — are the spine of the review. No em dashes in final academic paper copy; this working design index is not final copy.*
