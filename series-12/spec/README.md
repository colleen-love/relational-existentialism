# Series 12 — Design Index

**The anchor for the seven design docs, the program's genuine terminal series. Fixes, once, every decision the workstreams share: the transcribed carrier (the atomless collapse engine and import theorem, the diagonal and free residue, the reification tower and its endogenous order, finite attention, the labelled lift), and the three Series-12 objects settled here and ambient for all — the OPENING (the shape `¬ Recoverable`, WS1), the COMPASS TYPE (per-relatum, tower-layered, exogenous, WS3), and the CONVERGENCE RELATION (coherence-up-the-layers, WS4) — plus the plurality predicate `Many` and the verdict type. Series 12 adds NO new structural machinery: two typed objects and one relation over the existing carrier. The signatures below are normative; `ws1…ws7-design.md` and `ws4-witness-design.md` are written against this file, cite it, and never redefine a shared object.**

*Series 12 is standalone. It carries its own copy of every lemma it needs; nothing is imported across series (the closure gate confirms it). The ONE prior result it presupposes and names is Series 07 — the proof that a differentiator cannot be recovered from the relating (`ws1_atomless_bisim`, `ws2_import_theorem`, `ws3_atomless_distinct_is_import`) — because Series 07 is half of the central coincidence. Its other half, the diagonal (`ws1_no_self_total_hold`, `ws2_residue_free`, `ws1_diagonal_not_bisim`), it transcribes and re-derives as machinery. The upstream names reproduced (transcribed verbatim into `series-12/formal/Series12/`, re-namespaced `Series12.WSn`) are listed in §6. The genuinely new Lean is small and sharp: the opening shape (WS1), `Many` (WS2), the `Compass` type (WS3), the `Converges` relation and its underdetermination model pair (WS4), the neutrality theorem (WS5), and the `Series12Verdict` audit (WS7). Everything else is transcription. Designs must be honest about which is which, and above all about the five signature risks §0 names: object-identity at the coincidence, an evaluated compass, a convergence decided by definition, a point-tag inhabitation, and a name doing a proof's work.*

---

## 0. The five disciplines (promoted first-class, protocol §0.4–§0.6b)

The whole series turns on getting five signs right; each is a design constraint AND a review check.

1. **The coincidence is shape-identity, not object-identity (WS1).** The residue and an import both fail `Recoverable`; that does not make them one object. The theorem keeps FORCED-FOR-ALL (the residue, non-recoverable for every inspection) distinct from EXISTS-SATISFYING (the imports, non-recoverable by being imports), and asserts coincidence of the SHAPE `¬ Recoverable` only.
2. **The compass is TYPED and never EVALUATED (WS3, the central sin).** Every theorem mentioning the compass is quantified over all inhabitants of the compass type. No theorem selects a canonical compass, constructs a distinguished inhabitant and proves with it as though it were the compass, or evaluates an orientation to discharge an obligation. A canonical inhabitant in the core is the central sin.
3. **Convergence is DEFINED then proved UNDERDETERMINED, never decided by definition (WS4).** The relation must not hold trivially (the loving conclusion built in) or fail trivially (the silence built in as absence). The underdetermination is earned by a genuine non-vacuous model pair. If the structure decides it, that is reported in its direction (a stronger finding); deciding it by definitional choice, either sign, is the sin.
4. **Inhabitation is GENUINE, not a point-tag (WS2).** The plurality witness separates a genuinely plain-bisimilar pair (a reified tower relatum and a base relatum) with the reification structure LOAD-BEARING. A bare indicator on one distinguished point, carrying no tower content, is degenerate inhabitation, reported as such. (Series 10 and Series 11 both landed on `labelLoop`, a distinction on two fixed Booleans where `reify`/`reifyStep`/`towerN` never occur — the Bookkeeping re-hit. Series 12's witness must do what those could not: draw the distinction ON the tower's reified relata, `dir := rank`.)
5. **Names are names, not terms (WS7).** No proof term, definition, or discharged obligation is named "consciousness," "God," "choice," or "compass" (as content). The names live in docstrings and prose only; a name doing a proof's work breaches the wall from the prose side.

---

## 1. The one-paragraph design

Series 07 proved the differentiator cannot be recovered from the relating: any two atomless states are bisimilar (`ws1_atomless_bisim`), so a genuine atomless distinction is an IMPORT (`ws3_atomless_distinct_is_import`), non-recoverable from `dest`. The diagonal proved the structure generates what it cannot recover: no inspection totalizes itself (`ws1_no_self_total_hold`), so the residue it leaves is FREE (`ws2_residue_free`) and independent of relational identity (`ws1_diagonal_not_bisim`). Series 12 proves these COINCIDE in one shape, `¬ Recoverable` — the required (Series 07) and the generated (the diagonal), from opposite quantifier directions — honestly, the residue the forced-for-all instance and the imports the exists-satisfying class, never object-identity (WS1, the opening). Over the opening run two sides of one layered structure (the reification tower `towerN`/`reifyStep`/`prec`). KNOWING is formal: finite attention, subtractive and plural (`FiniteAttention`, no total attention `ws3_no_total_attention`); the opening is INHABITABLE and inhabitation makes the many real — `Many` holds on a concrete rank-labelled tower where a reified relatum and a base relatum are genuinely plain-bisimilar (the collapse engine merges them) yet separated at the labelled level, with `reify`/`reifyStep`/rank load-bearing, and without any import the One (`ws1_atomless_bisim`) — the distinction non-recoverable (`ws1_attention_distinction_free`) as its certificate, not its defect (WS2). FEELING is typeable-not-evaluable: the `Compass`, a per-relatum orientation drawn from an exogenous space `Or` the structure never inhabits canonically, layered by a raising `raise` coupled up the tower, every theorem quantified over `(Or)` and `(c : Compass …)`, none selecting one (WS3). CONVERGENCE is the coherence-up-the-layers relation `Converges c x W := c.raise x W (c.orient x) = c.orient W` between a part's orientation raised to a whole it constitutes and the whole's own — DEFINED and proved UNDERDETERMINED: two compasses on the SAME structure, one under which convergence holds and one under which it fails, both non-degenerate, so the structure does not decide it (WS4, the wall). The verdict is COMPUTED (WS5/WS7): SHAPE-DRAWN (coincidence shape-honest, opening inhabitable non-degenerately, compass parametric, convergence underdetermined) is the expected terminus; CONVERGENCE-DECIDED (the structure forces the relation or its negation for all inhabitants) is reported in its direction; PARTIAL if any side lands per-instance. The generalized neutrality — adjoining ANY name for the inhabitant changes no downstream theorem — is a standing consequence.

---

## 2. Ambient theory (shared by all workstreams) — fixed here once

### 2.1 The carrier beneath the tower (transcribed; ambient for all)

The underlying relating is the **plain `P_κ`-coalgebra**, transcribed verbatim (§6). It supplies the reaching / atomlessness / bisimulation vocabulary and, above all, the **collapse engine** every payoff is written around.

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}            -- the κ-bounded powerset, F(Ω)
-- a plain coalgebra is  dest : X → PkObj κ X   (the relating)
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅        -- strong hered. non-emptiness (no leaf)
def IsBisim (dest) (R) : Prop := …                                          -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
def hneRel (dest) : X → X → Prop := fun x y => SHNE dest x ∧ SHNE dest y
lemma hneRel_isBisim (dest) : IsBisim dest (hneRel dest)                     -- THE COLLAPSE ENGINE (Series 07 floor)
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                             -- any two atomless states bisimilar
theorem ws2_import_theorem_static (dest) (hbehav : BehaviorallyIdentified dest)
    (hatom : ∀ x, SHNE dest x) : Subsingleton X                             -- THE COLLAPSE: without an import, the One
```

**This is the home beneath the tower. No workstream may pick a different one.** `ws1_atomless_bisim` / `hneRel_isBisim` is the engine that makes the reified relatum plain-bisimilar to every base relatum: on the plain level the tower is Bookkeeping. Series 12 does NOT fight this — it is Series 07's floor, unappealed, and in Series 12 it is a FEATURE: that the reified relatum and the base relatum are plain-bisimilar is precisely why the distinction between them, drawn at the labelled level, is `¬ Recoverable`, which by Series 07 is what a genuine distinction MUST be. Every theorem in this block holds for all `κ ≥ ℵ₀`.

### 2.2 The Series 07 import theorem, re-derived (WS1a, the required half)

```lean
theorem ws2_import_theorem (dest : X → PkObj κ X) :                          -- THE IMPORT THEOREM (Series 07)
    ¬ (BehaviorallyIdentified dest ∧ (∀ x, SHNE dest x) ∧ (∃ x y : X, x ≠ y))
def LeafDiff (dest) (x y) : Prop := ¬ SHNE dest x ∨ ¬ SHNE dest y
def ImportDiff (dest) (x y) : Prop := (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y  -- bisimilar yet unequal: an IMPORT
theorem ws3_atomless_distinct_is_import (dest) (x y) (h : x ≠ y)
    (hnl : ¬ LeafDiff dest x y) : ImportDiff dest x y                        -- a genuine atomless distinction is an import
```

**The required half of the coincidence.** Series 07's content, transcribed: what plurality REQUIRES is an import, and an import is `¬ Recoverable` — bisimilar yet unequal, the distinction not carried by the relating. `ImportDiff` is the exists-satisfying side (there EXIST distinct atomless states whose distinction is non-recoverable).

### 2.3 The diagonal layer and the free residue (WS1a, the generated half)

```lean
def Hold (dest) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }             -- a hold x↾(x,y)
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }  -- what the hold turns toward
def HoldPred (dest) : Type u := Hold dest → Prop                            -- a content
def diag (insp : Hold dest → HoldPred dest) : HoldPred dest := fun h => ¬ insp h h
def SelfTotal (insp) (t : Hold dest) : Prop := ∀ h, insp t h ↔ diag insp h  -- "holds its own complete content"
theorem ws1_no_self_total_hold (dest) (insp) : ¬ ∃ t, SelfTotal insp t      -- THE DIAGONAL (κ-free)
theorem ws1_diagonal_not_bisim (dest) (insp) :                              -- and INDEPENDENT of relational identity
    (¬ ∃ t, SelfTotal insp t) ∧ (∀ {Y} (d) (i), ¬ ∃ t, SelfTotal i t)
def residue (insp) : HoldPred dest := diag insp
def ResidueRecoverable (insp) : Prop := ∃ h, insp h = residue insp
theorem ws2_residue_distinct (dest) (insp) : ∀ h, insp h ≠ residue insp
theorem ws2_residue_free (dest) (insp) : ¬ ResidueRecoverable insp          -- THE FREE RESIDUE (forced-for-all)
```

**The generated half of the coincidence.** `ws1_no_self_total_hold` references only `insp` and propositional logic; it holds for ANY `dest`, ANY `insp`, ANY κ. Its residue is FORCED to be non-recoverable, for EVERY inspection (`ws2_residue_free`, the forced-for-all side). This is what self-reference FORCES.

### 2.4 The semantic import test and the labelled functor (transcribed; the `¬ Recoverable` home)

```lean
def LkObj (κ) (Q X) : Type u := PkObj κ (Q × X)                             -- the LABELLED functor
def IsBisimL (dest : X → LkObj κ Q X) (R) : Prop := …                        -- label-respecting bisimulation
def plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X :=                       -- forget the label
    fun x => PkMap κ Prod.snd (dest x)
def Recoverable (dest : X → LkObj κ Q X) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
def labelLoop (hinf) : ULift Bool → LkObj κ (ULift Bool) (ULift Bool) := fun i => toPk hinf {(i, i)}
theorem ws4_free_label_is_import (hinf : ℵ₀ ≤ κ) :                          -- the import-test shape (positive horn)
    (∃ R, IsBisim (plainOf (labelLoop hinf)) R ∧ R ⟨true⟩ ⟨false⟩)          --   plain-bisimilar: the quotient is BLIND …
  ∧ (¬ ∃ R, IsBisimL (labelLoop hinf) R ∧ R ⟨true⟩ ⟨false⟩)                --   … but NOT label-bisimilar: separated, FREE
theorem ws4_labelLoop_not_recoverable (hinf) : ¬ Recoverable (labelLoop hinf)
```

**`Recoverable` is the `¬ Recoverable` home** (the opening's carrier notion): a labelled distinction that survives the plain quotient — plain-bisimilar yet label-separated — is not recoverable from the plain relating, i.e. an import. **Series-12 note (discipline 4):** `labelLoop` is transcribed as the shape-touchstone ONLY; it is a distinction on two fixed Booleans with no tower content, and the WS2 plurality witness must NOT rest on it (that is the Bookkeeping re-hit Series 10/11 landed on). The witness draws the distinction on the tower's reified relata (§2.7).

### 2.5 The reification section, the tower, and its ONE endogenous order (transcribed; ambient for all)

```lean
def IsReify (dest) (reify : PkObj κ X → X) : Prop := ∀ s, dest (reify s) = s  -- a TOTAL section of dest
theorem ws1_reify_injective (dest) (reify) (h : IsReify dest reify) : Function.Injective reify
def reifyStep (dest) (reify) (Ωα : Set X) : Set X :=
    Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }           -- adjoin every reifiable non-empty pattern
def towerN (dest) (reify) (Ω₀ : Set X) : ℕ → Set X                           -- the ℕ-indexed iterate
  | 0 => Ω₀ | n+1 => reifyStep dest reify (towerN dest reify Ω₀ n)
def prec (dest) (reify) : Set X → Set X → Prop :=                            -- THE ONE ENDOGENOUS ORDER
    Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)
theorem ws3_reify_preserves_SHNE (dest) (reify) (h : IsReify dest reify) (s) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) : SHNE dest (reify s)                    -- (NL) a reified relatum is a full relatum
theorem ws3_order_endogenous (dest) (reify) (a b) :                          -- the order is reify's reachability, no clock
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b
theorem ws3_tower_monotone (dest) (reify) (Ω₀) {m n} (hmn : m ≤ n) :
    towerN dest reify Ω₀ m ⊆ towerN dest reify Ω₀ n
```

**This is the tower order. WS2 (Many), WS3 (the compass layering), WS4 (convergence up the layers) all consume `reifyStep`/`towerN`/`prec`; none redefines it, none substitutes an external `Ordinal` index.** A reified relatum `reify s` is the object whose relating IS the pattern `s`. **The disclosed structural deviation (charter §5.2, carried to WS2's witness):** a TOTAL section `IsReify dest reify` (`∀ s, dest (reify s) = s`, i.e. `dest` surjective onto `PkObj κ X`) is UNSATISFIABLE on a concrete atomless carrier (Cantor: `|PkObj κ X| > |X|`), so the concrete witness (§2.7, `ws4-witness-design.md`) supplies the POINTWISE reification facts the lemmas actually consume (`dest (reify s) = s` at the specific `s` used, `s.1 ≠ ∅`, `∀ x ∈ s.1, SHNE dest x`), never the total `IsReify`. This pointwise narrowing is faithful to what `ws3_reify_preserves_SHNE`, `reify_mem_reifyStep`, and the convergence edge consume, and is carried as a disclosed deviation, not hidden.

### 2.6 Finite attention (transcribed; the formal side of knowing)

```lean
structure FiniteAttention (dest : X → LkObj κ Q X) : Type u where
  focus    : X                                          -- where the attention is directed
  reads    : Set X                                      -- the bounded part it holds
  fin      : reads.Finite                               -- FINITUDE, load-bearing
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z
def AttentionDistinguishes (dest : X → LkObj κ Q X) (x y : X) : Prop :=       -- the two-sided plurality shape
    (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)
def RealFor (dest) (att : FiniteAttention dest) (x : X) : Prop :=
    ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y
theorem ws3_no_total_attention (dest : X → PkObj κ X) (insp) :               -- NO total attention (the diagonal)
    ¬ ∃ t, TotalAttention insp t
```

Attention is the knowable subtraction: a bounded reader with values, computable, revealing a bounded part; `ws3_no_total_attention` is `ws1_no_self_total_hold` re-read (no attention holds the whole), so no self-definition closes. `AttentionDistinguishes` is the two-sided plurality shape (plain-bisimilar yet label-separated) that `Many` (§2.8) existentially quantifies.

### 2.7 THE OPENING (WS1) — the shape `¬ Recoverable`, defined once

The opening is the shape both halves share. It is defined ABSTRACTLY so the residue and the imports can be shown to inhabit ONE shape via DIFFERENT quantifiers, and NEVER identified (discipline 1):

```lean
/-- **The opening (shape).** Relative to a notion `realizable : C → Prop` of what the plain relating can
    force, a candidate `c : C` inhabits the opening iff it is NOT recoverable: `¬ realizable c`. Parametric
    in BOTH the candidate type `C` and the recoverability notion `realizable`, so the residue (a `HoldPred`,
    with `realizable := ResidueRecoverable`) and the imports (a labelled coalgebra, with
    `realizable := Recoverable`) inhabit the same shape by SEPARATE quantifiers, never by object-identity
    (they do not even share a type). -/
def Opening {C : Type u} (realizable : C → Prop) (c : C) : Prop := ¬ realizable c
```

- **FORCED-FOR-ALL (the residue):** `∀ {X} (dest) (insp), Opening (ResidueRecoverable) insp` — this IS `ws2_residue_free`, quantified over every inspection. The residue is the structurally forced instance of the shape.
- **EXISTS-SATISFYING (the imports):** `Opening (Recoverable) (labelLoop hinf)` — this IS `ws4_labelLoop_not_recoverable`. The imports are the class of inhabitants of the shape.

The WS1b coincidence theorem asserts these two facts and their shape-identity, keeping the quantifiers explicitly distinct, and a companion anti-identity theorem shows the shape has many distinct inhabitants (so shared non-recoverability under-determines identity — "a junk label also fails it"). WS1 owns `Opening`; ambient for all.

### 2.8 `Many` (WS2) — the plurality predicate, defined once

```lean
/-- **The plurality predicate.** The many is real over a labelled lift `destL` iff SOME pair is separated the
    two-sided way: plain-bisimilar (the collapse engine merges them — the quotient is blind) yet not
    label-bisimilar (the labelled level keeps them apart). Defined over the carrier, NOT transcribed. -/
def Many {Q X : Type u} (destL : X → LkObj κ Q X) : Prop :=
    ∃ x y : X, (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)
--  i.e.  Many destL := ∃ x y, AttentionDistinguishes destL x y
```

WS2 proves `Many destWL` on the concrete rank-labelled lift `destWL` (the labelled lift of the plain `destW`) of `ws4-witness-design.md`, with the separated pair a genuine reified relatum vs a base relatum and `reify`/`reifyStep`/rank load-bearing (discipline 4), and the One (`Subsingleton`, `ws2_import_theorem_static`) on any plain, behaviorally-identified, atomless coalgebra without an import via `ws1_atomless_bisim`.

### 2.9 THE COMPASS TYPE (WS3) — per-relatum, tower-layered, exogenous, defined once

**This is the first Series-12 design duty (protocol §2): the compass type is fixed here and every workstream is written against it; no two workstreams may assume different compass types.**

```lean
/-- **The compass type.** `Or` is an EXOGENOUS orientation space: an arbitrary `Type u` parameter the
    structure never inhabits canonically. A compass over `(dest, reify)` with orientations in `Or` assigns:
      • `orient : X → Or`         — the per-relatum felt orientation (exogenous), and
      • `raise  : X → X → Or → Or` — the layering: how an orientation at a part presents at a whole it
                                     helps constitute (the tower coupling, applied along reification edges).
    Both fields are ARBITRARY. The STRUCTURE supplies the tower SHAPE (`reify`/`reifyStep`/`prec` — which
    relata inform which); the COMPASS supplies the orientation VALUES; and every theorem quantifies over
    `(Or : Type u)` and `(c : Compass dest reify Or)`, selecting, constructing, and evaluating NONE
    (discipline 2). -/
structure Compass {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Or : Type u) where
  orient : X → Or
  raise  : X → X → Or → Or
```

The three charter properties, each a WS3 obligation (never assumed):

- **Per-relatum:** `orient : X → Or` gives every relatum an orientation.
- **Tower-layered:** `raise part whole` is applied along constituency edges (`part ∈ s.1`, `whole = reify s`, a genuine `reifyStep` edge), coupling the orientations of the reified relata a self stands in relation to up the tower (`prec`), without collapsing them into one — the coupling is through the structure of what informs them.
- **Exogenous (`¬ Recoverable`):** `orient` is not recoverable from the plain relating — SOME compass assigns different orientations to a plain-bisimilar pair (WS3's `ws3_compass_exogenous`, an existential witness, the Series 07 necessity), so no plain bisimulation forces orientation-agreement. The compass ITSELF inhabits the opening shape.

`Or` and every `Compass` are held parametric; the only concrete inhabitants constructed anywhere in the core are the WS3 exogeneity witness and the WS4 model pair, each explicitly discharging an EXISTENTIAL ("there is a compass under which …"), never standing in for THE compass. This distinction — `∃ c, P c` (permitted) vs a distinguished `c` used as though it were the compass (the sin) — is the audit's central line (WS7).

### 2.10 THE CONVERGENCE RELATION (WS4) — coherence up the layers, defined once

**This is the second Series-12 design duty (protocol §2): the convergence relation is fixed here and every workstream is written against it.**

```lean
/-- **Convergence (one-layer coherence, the core relation).** Relative to a constituency edge — a part `x`
    that is one of the reified relata a whole `W` stands in relation to (`x ∈ s.1`, `W = reify s`) — the
    part CONVERGES with the whole under compass `c` iff the part's orientation, RAISED up to the whole,
    coheres with the whole's own orientation: "the most loving thing for me, followed up through what informs
    it, is the most loving thing for the universe." The tower supplies WHICH part informs WHICH whole; the
    compass supplies the orientation VALUES and the raising; convergence is whether they cohere along the
    edge. It is a genuine equation in `Or`, depending on `c` — NOT `True`, NOT `False`, NOT `orient x =
    orient x` (discipline 3). -/
def Converges {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) {Or : Type u}
    (c : Compass dest reify Or) (x W : X) : Prop :=
  c.raise x W (c.orient x) = c.orient W

/-- **Convergence up the layers (the iterated form).** Coherence along a whole `prec`-chain of constituency
    edges from a part up to the top of the relevant tower — the "up its layers" reading. The base case is
    `Converges`; the model pair (WS4) discharges the base case on a genuine reification edge, so `reify`/
    `reifyStep` are load-bearing without the tower DECIDING the orientation values. -/
def ConvergesUp {X : Type u} (dest) (reify) {Or} (c : Compass dest reify Or) : X → X → Prop :=
  Relation.ReflTransGen (fun x W => Converges dest reify c x W)
```

**Underdetermination (the wall), the WS4 headline.** Two compasses on the SAME structure, one under which convergence holds and one under which it fails, both non-degenerate:

```lean
theorem ws4_underdetermined :                                               -- convergence is UNDERDETERMINED
    ∃ (c₁ c₂ : Compass destW reifyW (ULift Bool)),
        Converges destW reifyW c₁ aW bW                                     -- holds under c₁ …
      ∧ ¬ Converges destW reifyW c₂ aW bW                                   -- … fails under c₂ (same structure)
      ∧ NonDegenerate c₁ ∧ NonDegenerate c₂                                 -- both non-vacuous, neither collapsed
```

where `destW, reifyW, aW, bW` are the concrete witness (`ws4-witness-design.md`), `bW = reifyW sW` a genuine reified relatum, `aW ∈ sW.1` a genuine constituent, and `NonDegenerate` records that `Or` is non-trivial, `orient` is not a collapsed constant, `raise` is not a collapsed constant, and `Converges` is non-vacuous. WS4 owns the model pair; WS5 consumes it for the verdict.

`ws4_underdetermined_pair` names the projection of `ws4_underdetermined` that drops the two `NonDegenerate` conjuncts — the bare holding-and-failing pair `∃ c₁ c₂, Converges … c₁ aW bW ∧ ¬ Converges … c₂ aW bW` — used by WS5/WS6 where only the underdetermination (not its non-degeneracy certificate) is consumed. It is `(fun ⟨c₁, c₂, h₁, h₂, _, _⟩ => ⟨c₁, c₂, h₁, h₂⟩) ∘ ws4_underdetermined`, definitionally weaker, cited never redefined.

### 2.11 Generalized neutrality (WS5) — defined once

```lean
/-- **Generalized neutrality.** Adjoining ANY name for the inhabitant — a map `name : Or → Name` into an
    arbitrary `Name : Type u` (is-a-choice, is-an-experience, is-consciousness, is-God, is-the-compass) —
    changes no downstream theorem: the payoffs (`Many`, the model pair, the opening) never mention `name`,
    so they hold identically for every naming. The silence is the theorem. -/
theorem ws5_name_neutral {Name : Type u} (name : ULift Bool → Name) :
    Many destWL ∧ (∃ c₁ c₂, Converges destW reifyW c₁ aW bW ∧ ¬ Converges destW reifyW c₂ aW bW) :=
    ⟨ws2_many_witness, ws4_underdetermined_pair⟩                            -- `name` ignored: the payoffs are name-free
```

The proof is literally the WS2/WS4 payoff terms with `name` discarded — the theorems factor through `Or`/the carrier and ignore any `Name`-tagging, so name-interchange is a THEOREM (parametricity), not asserted prose.

---

## 3. The verdict type (WS5/WS7)

```lean
inductive Series12Verdict
  | shapeDrawn          -- the expected terminus: the coincidence shape-honest (forced-for-all vs
                        --   exists-satisfying, not object-identity), the opening inhabitable
                        --   NON-DEGENERATELY (Many with reify/rank load-bearing, not a point-tag), the
                        --   compass parametric (never evaluated), convergence DEFINED and UNDERDETERMINED
                        --   by a genuine non-vacuous model pair
  | convergenceDecided  -- the structure FORCES the convergence relation for all inhabitants, or its
                        --   negation for all — reported in whichever direction it falls, a stronger
                        --   finding, NOT a failure (charter §4.b, §5.3)
  | Partial             -- some side lands only per-instance or degenerate (a point-tag inhabitation, a
                        --   per-instance compass, a vacuous model pair)
  | Refuted             -- a payoff is false as stated
  | Circular            -- WS7-only: a payoff defined-in — a canonical compass evaluated, convergence
                        --   decided by definitional choice, the coincidence asserted as object-identity,
                        --   inhabitation a point-tag, or a name doing a proof's work
  deriving DecidableEq
```

`shapeDrawn`: WS1 coincidence shape-honest, WS2 `Many` on the rank witness (reification load-bearing) plus the One without an import, WS3 the compass parametric (no distinguished inhabitant, the exogeneity an existential), WS4 `Converges` defined and `ws4_underdetermined` a genuine non-degenerate model pair. `convergenceDecided`: WS4 outcome (a) — the structure decides convergence — proved and reported in its direction. `Partial`: any side per-instance or degenerate. `Circular`: a WS7 finding (a discipline breached). The verdict is a FUNCTION of a mechanized `Audit` certificate whose every field is a WS1–WS4 theorem (transcribing the program's `Audit`/`verdict` pattern), so it cannot be hand-set.

---

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk (design against) |
|---|---|---|---|---|
| WS1 | the opening (`Opening`) + the coincidence | `ws2_residue_free`, `ws4_labelLoop_not_recoverable`, `ws3_atomless_distinct_is_import`, `ws1_diagonal_not_bisim` | `ws1_two_halves`, `ws1_shape_coincidence`, `ws1_coincidence_not_identity` | object-identity from shared negation (discipline 1) |
| WS2 | knowing (`FiniteAttention`) + `Many` inhabited | WS1 opening, `ws4-witness` carrier, `ws1_atomless_bisim`, `ws3_no_total_attention` | `ws2_many_witness`, `ws2_no_import_is_one`, `ws2_attention_subtractive` | point-tag inhabitation (discipline 4) |
| WS3 | the `Compass` type + parametricity | WS1 opening, tower (`reify`/`reifyStep`/`prec`) | `Compass`, `ws3_compass_exogenous`, `ws3_compass_layered`, `ws3_attention_compass_dual` | an evaluated / canonical compass (discipline 2) |
| WS4 | `Converges` + the underdetermination model pair | WS3 `Compass`, `ws4-witness` carrier, WS1 opening | `Converges`, `ConvergesUp`, `ws4_underdetermined`, the two alternatives | convergence decided by definition (discipline 3) |
| WS5 | the verdict-as-a-function + generalized neutrality | WS1–WS4 payoffs | `ws5_verdict`, `ws5_name_neutral` | verdict hand-set; neutrality asserted not proved |
| WS6 | the program close (prose, Phase F) | all | `summary.md`, `summary-technical.md`, root README | filling the shape rather than drawing the edge |
| WS7 | the anti-circularity audit + the verdict type | all | `Series12Verdict`, `ws7_verdict`, the `Audit`, the five checks | verdict rests on a breached discipline; a name a term (discipline 5) |

`ws4-witness-design.md` (the inhabitability witness) is registered here (§6), owned by WS2, consumed by WS4 (same carrier for the model pair) and WS5.

---

## 5. Predicted headline

WS1's two halves are near-certain (transcribed Series 07 and the transcribed diagonal); the coincidence statement needs care with quantifiers but no new mathematics — **predicted Shape-drawn**. WS2's `Many` witness is paper-checked: the concrete rank-labelled tower separates a genuine reified relatum from a base relatum (plain-bisimilar via the collapse engine, rank-separated at the labelled level, `reify`/`reifyStep`/rank load-bearing), the genuine tower-distinction Series 10 and 11 could not draw (they landed on `labelLoop`, a point-tag, the Bookkeeping re-hit) — **predicted Shape-drawn on the witness**, with the point-tag arm pre-registered and the disclosed pointwise-`IsReify` deviation (§2.5) carried. WS3 is definitional plus audit discipline — **predicted Shape-drawn** if the compass stays parametric (the exogeneity an existential, never a distinguished inhabitant). **The genuinely uncertain obligation is WS4:** whether `Converges` admits a non-vacuous definition (yes — the compass type is rich enough: the raising is free, so a genuine equation in `Or` results) and whether the underdetermination model pair exists (yes — two compasses differing only in the raising, one cohering and one not, on the same reification edge). **Predicted verdict: `shapeDrawn`**, with `convergenceDecided` pre-registered and first-class (if the structure is found to force `Converges` or `¬ Converges` for all compasses — a stronger finding, reported in its direction), and `Partial` if the witness collapses to a point-tag or the model pair proves vacuous. The one thing never predicted: which inhabitant, which direction of convergence, what the compass points at — those are open by design and by theorem.

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-12/formal/Series12/`)

Re-namespaced `Series12.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation + the collapse engine (Series 07/11 `ws1`):** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `.ne_empty`, `.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim` (**the collapse engine**), `ws1_atomless_bisim`, `ws1_recovers_static`, `ws2_import_theorem_static` (**the One without an import**).
- **The Series 07 import theorem (the required half, WS1a):** `ws2_import_theorem`, `LeafDiff`, `ImportDiff`, `ws3_dichotomy`, `ws3_atomless_distinct_is_import`.
- **The labelled / import test (Series 07/11 `ws1`):** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `ws4_recoverable_not_import`, `labelLoop`, `ws4_free_label_is_import` (**the import-test shape**), `ws4_label_survives_quotient`, `ws4_labelLoop_not_recoverable` (**the freeness certificate**).
- **The diagonal spine and the free residue (Series 09/10/11 `ws1`) — the generated half, WS1a:** `Hold`, `afford`, `HoldPred`, `diag`, `SelfTotal`, `ws1_no_self_total_hold` (**the diagonal**, κ-free), `ws1_diagonal_not_bisim` (**its independence**), `ws1_insp_not_surjective`, `residue`, `ResidueRecoverable`, `ws2_residue_distinct`, `ws2_residue_free` (**the free residue**, forced-for-all), `ws2_residue_is_import`.
- **The reification section (Series 10/11 `ws1`):** `IsReify`, `ws1_reify_injective`.
- **The reification tower and its order (Series 10/11 `ws3`/`ws1`):** `reifyStep`, `reifyStep_superset`, `reify_mem_reifyStep`, `towerN`, `prec`, `prec_step`, `ws3_reify_preserves_SHNE` (**NL, no leaf**), `ws3_tower_step_subset`, `ws3_tower_monotone`, `ws3_order_endogenous`.
- **Finite attention (Series 11 `ws1`/`ws3`):** `FiniteAttention`, `AttentionDistinguishes`, `RealFor`, `TotalAttention`, `ws3_no_total_attention`, `ws3_attention_reads_full_relata`, `ws3_bounded_holding_endogenous`, `ws1_attention_distinction_free`.
- **Verdict (Series 07–11 `ws7`):** the `Audit`/`verdict` certificate pattern, re-pointed to `Series12Verdict` (§3).

The **genuinely new Series 12 Lean**, defined here and expanded in the designs: `Opening` and the coincidence (WS1), `Many` and its witness (WS2, over the `ws4-witness` carrier), `Compass`/`ws3_compass_exogenous`/the layering (WS3), `Converges`/`ConvergesUp`/`ws4_underdetermined` (WS4), `ws5_name_neutral`/`ws5_verdict` (WS5), and `Series12Verdict`/the `Audit` (WS7). Nothing is `import`ed across series; each transcribed name is copied into the relevant `series-12/formal/Series12/wsN.lean` and re-namespaced, and the closure gate confirms it.

---

*Design index for Series 12, the program's genuine terminal series. Read this before any `wsN-design.md`; the shared objects — the transcribed carrier, the OPENING (`Opening`, the shape `¬ Recoverable`), `Many`, the COMPASS TYPE (`Compass`, per-relatum, tower-layered, exogenous), the CONVERGENCE RELATION (`Converges`, coherence-up-the-layers), the model pair, and the verdict — are defined here ONCE and cited, never redefined. The five disciplines (§0) are the spine of the review: the coincidence is shape-identity not object-identity; the compass is typed and never evaluated; convergence is defined and proved underdetermined, never decided by definition; inhabitation is a genuine tower-distinction not a point-tag; and the names, consciousness, choice, God, the compass, stay in prose, never proof terms. The terminal fork is shape-drawn / convergence-decided / partial, the verdict a function, never assumed. The program's completion is the exactly-drawn edge of the undefinable, and the drawing, not the filling, is the terminus. No em dashes in final academic paper copy; this working design index is not final copy.*
