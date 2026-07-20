# Program 2 Series 0 (2.0), Design Index

**The anchor for the five design docs. Fixes, once, every decision the workstreams share: the prior art imported from the P1 foundation (`program-2/formal/P1`, Program 2 permits importing), the ONE new carrier (the ATTENTION CARRIER, `attends : X → Finset X`, finite out-attention the sole bound) and the ONE new distinction (the KNOWING-ASYMMETRY, the plain symmetric relating versus the labelled directed knowing), the cross-workstream triage, the outcome classes, and the names-in-prose rule. The signatures below are normative; `ws1…ws5-design.md` are written against this file, cite it, and never redefine a shared object. Series 0 adds NO structural machinery beyond the carrier and the asymmetry: everything else is imported from P1.**

*Series 0 is NOT standalone; unlike a Program 1 series it IMPORTS the P1 foundation (`import P1`, using `P1.Core.*`) rather than transcribing it. The prior art presupposed and named: the diagonal and free residue (`ws1_no_self_total_hold`, `residue`, `ws2_residue_free`), the reification section machinery (`IsReify`, `ws1_reify_injective`), the recoverability test (`Recoverable`, `plainOf`, `IsBisim`, `IsBisimL`, `LkObj`), and the collapse engine (`ws1_atomless_bisim`, `ws2_import_theorem_static`). What is proved, not assumed: the attention carrier and its reification on the FINITE functor (WS1), the inherited collapse restated over the symmetric relating (WS2, transcription), the asymmetry of knowing genuine, non-recoverable, and load-bearing (WS3, the knot), and the import seated as a quantified ingredient (WS4). The genuinely new Lean is small and sharp; the honesty discipline (§0) is the spine of the review.*

---

## 0. The disciplines (the honesty invariants, protocol §0)

The series turns on getting five signs right; each is a design constraint AND a review check.

1. **No cardinal ceiling (audit a, WS1).** The ontological bound is finite out-attention (`Finset`). Any `κ` that appears is the ambient carrier size for the symmetric reduct's possibly-infinite in-attention neighborhoods, refutably distinct from a chosen ontological ceiling. A bound that unfolds to "attention ranges over a κ-bounded set" is the Series 11 §4.4 wall rebuilt. SERIOUS.
2. **The asymmetry is not a label (audit b, WS3, the central sin).** The directed knowing must be load-bearing in what a relatum is. If passive constitution can be stripped and the relatum is unchanged, or if the plain and labelled structures do the same work, then knowing's directionality is an inert tag laid over the symmetric relating, the Series 11 Bookkeeping failure. `ws3_passive_constitution` must name a genuine reader and survive the strip. SERIOUS.
3. **Direction is non-recoverable (audit c, WS3).** Direction's non-recoverability from the plain symmetric relating (`ws3_direction_not_recoverable`) is a PROOF term, not an assumption. If direction were recoverable, being-attended-and-knowing and being-attended-without-knowing would coincide and the asymmetry would be fake.
4. **The collapse is inherited, not relitigated (audit d, WS2).** That without the import the atomless symmetric world is the One is Program 1's theorem, transcribed here as baseline (`ws2_collapse_inherited`). No series verdict may hinge on it, and no artifact may present it as a new, open, or uncertain result. SERIOUS.
5. **The import is quantified, not named (audit e, WS4).** No proof term, definition, or discharged obligation is named "love," "loved," "import," "God," "choice," "self," "other," "knowing," or "attention" as content. The import is quantified over; its content stays outside. SERIOUS.

And the strip test (protocol §0.3): for every payoff, delete the structural term and check the bare `Finset` / reification / `Recoverable` / bisimulation / diagonal fact survives. WS3's asymmetry strips to "direction is not recoverable from the symmetric reduct, by `Recoverable`, and a directed-structure reader is load-bearing"; WS2's collapse strips to "atomless plain-bisimilar states on the symmetric relating are equal, by the transcribed engine."

**Note on the names grep.** "attention" and "knowing" are this series' CONCEPT, so the carrier uses neutral Lean names (`attends`, the relation symbols, `knowLift`); the grep guards that no proof term or headline is NAMED for the interpretive content. Docstring prose may use the words freely.

---

## 1. The one-paragraph design

Program 1 proved a purely relational atomless world is the One unless a distinction is imported, and bounded that world by an imported cardinal `κ` with finite attention laid over it as a separate reader. Series 0 makes the correction structural: relating IS finite attending. WS1 fixes the carrier `attends : X → Finset X` (finite out-attention, the SOLE ontological bound, no `κ` ceiling), reads from it the directed knowing (`knows x y := y ∈ attends x`), the symmetric relating (`x ~ y := y ∈ attends x ∨ x ∈ attends y`), and the passive in-attention (`attendedBy x := {z | x ∈ attends z}`, possibly infinite), views the finite out-attention as a `PkObj κ`-coalgebra through `finsetToPk` (whose neighborhoods are always finite, `< ℵ₀ ≤ κ`, so `κ` never bounds the world), and establishes a reification section on the FINITE functor (`FinReify`, adapting P1's `IsReify` to `Finset`), proved to EXIST non-vacuously (`ws1_reification_exists`) on a carrier where `Finset X ≃ X`, with the ontological bound certified finite (`ws1_bound_is_finite_attention`). WS2 restates the inherited collapse over the symmetric relating (`ws2_collapse_inherited`), applying the imported P1 engine `ws2_import_theorem_static` to `symDest`, in a handful of transcribed lines, baseline not result, no verdict hanging on it. WS3, the knot, seats knowing's directionality as the plain/labelled split: the knowing-labelled lift `knowLift` tags each symmetric neighbor with the knowing bit, its plain reduct IS the symmetric relating (`plainOf_knowLift`), and on the two-state witness (`a` attends `b`, `b` attends nothing) the direction is proved NOT recoverable (`ws3_direction_not_recoverable`, the plain swap is a bisimulation, no label-bisimulation relates `a` and `b`), passive constitution is proved real and load-bearing (`ws3_passive_constitution`, `b` attended-but-not-attending is plain-bisimilar to the active `a` yet label-separated, the directed reader doing the work), and active and passive are proved two (`ws3_active_passive_distinct`, `attends a ≠ ∅ = attends b` at symmetric positions, invisible to the plain relating). WS4 seats the import as an exogenous, typed, quantified symmetry-breaker `impLift` (an exogenous label on the symmetric self-loops, transcribing P1's free-label shape), proves it breaks the WS2 baseline (`ws4_import_breaks_baseline`, quantified over ALL import value-spaces `Q` and ALL import functions `f`, whenever `f` separates two plain-bisimilar states the labelled world is plural), and proves it carried WITHOUT being named or selected (`ws4_import_quantified`, the `∀ {Q} (f)` binder is the whole content). WS5 computes the verdict from WS1/WS3/WS4 (never WS2, never hand-set), folds in the audit (a–e), and reports GROUND-ESTABLISHED, PARTIAL, or OBSTRUCTED. The pre-registered verdict is GROUND-ESTABLISHED; PARTIAL (an obligation lands only per-instance) and OBSTRUCTED (no reification section on the finite functor, or the asymmetry collapses to a label) are honorable, anticipated, reported in full.

---

## 2. Ambient theory (shared by all workstreams), fixed here once

### 2.1 The imported prior art (from `P1.Core`, NOT redefined)

`import P1` brings the whole Program 1 carrier under the `P1.Core` namespace. The used pieces (all `κ`-free where reused, `∀ κ ≥ ℵ₀`):

```lean
-- the κ-bounded powerset functor and the finite injector
P1.Core.PkObj κ X               -- {s : Set X // Cardinal.mk ↥s < κ}
P1.Core.PkMap κ (f : X → Y)     -- functorial action
P1.Core.toPk (hinf : ℵ₀ ≤ κ) [Finite X] (s : Set X) : PkObj κ X   -- finite carrier → bounded
-- reaching / atomlessness / bisimulation / the collapse engine
P1.Core.SReaches, SHNE (+ .ne_empty, .succ), IsBisim, BehaviorallyIdentified
P1.Core.ws1_atomless_bisim      -- any two atomless states are plain-bisimilar (THE ENGINE)
P1.Core.ws2_import_theorem_static (dest) (hbehav) (hatom) : Subsingleton X   -- THE COLLAPSE (baseline)
-- the labelled functor and the recoverable / free import test
P1.Core.LkObj κ Q X := PkObj κ (Q × X)
P1.Core.IsBisimL, BehaviorallyIdentifiedL
P1.Core.plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X   -- forget the label, keep the target
P1.Core.Recoverable (dest) : Prop := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
-- the diagonal and free residue, the reification section
P1.Core.Hold, HoldPred, diag, residue, ws1_no_self_total_hold, ws2_residue_free
P1.Core.IsReify (dest) (reify) : Prop := ∀ s, dest (reify s) = s
P1.Core.ws1_reify_injective     -- a section is injective
```

**This is the home. No workstream redefines these; they are imported.** Every theorem holds for all `κ ≥ ℵ₀`.

### 2.2 THE ATTENTION CARRIER (WS1, the one new carrier), defined once

For a carrier type `X : Type u`:

```lean
/-- **The attention carrier.** Each relatum attends only FINITELY; finite out-attention is the SOLE bound. -/
-- a coalgebra of the finite-powerset functor:  attends : X → Finset X   (a PARAMETER, not a fixed object)

/-- **Finite out-attention as a `PkObj κ`-coalgebra.** The neighborhoods are always finite (`< ℵ₀ ≤ κ`), so
    `κ` never bounds the world; the injector needs only that a `Finset` is finite, NOT that `X` is finite. -/
noncomputable def finsetToPk (hinf : ℵ₀ ≤ κ) {X : Type u} (s : Finset X) : PkObj κ X :=
  ⟨↑s, by/- s.finite_toSet.to_subtype ⇒ mk ↥↑s < ℵ₀ ≤ κ -/⟩
noncomputable def outDest (hinf : ℵ₀ ≤ κ) (attends : X → Finset X) : X → PkObj κ X :=
  fun x => finsetToPk hinf (attends x)

/-- **The directed knowing** (x KNOWS y iff x actively attends y). -/
def knows (attends : X → Finset X) (x y : X) : Prop := y ∈ attends x
/-- **The symmetric relating** (blind to direction). -/
def sym  (attends : X → Finset X) (x y : X) : Prop := y ∈ attends x ∨ x ∈ attends y
/-- **The passive in-attention** (possibly UNBOUNDED in-degree, the passive side). -/
def attendedBy (attends : X → Finset X) (x : X) : Set X := {z | x ∈ attends z}

/-- **The symmetric relating as a `PkObj κ`-coalgebra.** Its neighborhoods `{y | sym x y}` may be infinite
    (unbounded in-degree); `κ` here is AMBIENT CARRIER SIZE (`hcar : mk X < κ`), never an ontological ceiling. -/
noncomputable def symDest (hinf : ℵ₀ ≤ κ) (hcar : Cardinal.mk X < κ) (attends : X → Finset X) :
    X → PkObj κ X := fun x => ⟨{y | sym attends x y}, by/- mk_subtype_le ≤ mk X < κ -/⟩
```

**This is the ground. No workstream picks a different carrier.** `κ` enters ONLY as ambient carrier size for `symDest` (audit a); the out-attention is finite for every `κ`.

### 2.3 THE KNOWING-ASYMMETRY (WS3, the one new distinction), the plain/labelled split, defined once

```lean
/-- **The knowing-labelled lift.** Each symmetric neighbor `y` of `x` is tagged with the KNOWING BIT
    `⟨decide (y ∈ attends x)⟩ : ULift Bool` (does `x` actively attend `y`). The plain (label-forgetting)
    reduct is the SYMMETRIC relating (`plainOf_knowLift`); the label is the directed knowing laid over it. -/
noncomputable def knowLift (hinf : ℵ₀ ≤ κ) (hcar : Cardinal.mk X < κ) (attends : X → Finset X) :
    X → LkObj κ (ULift Bool) X :=
  fun x => ⟨{ p | sym attends x p.2 ∧ p.1 = ⟨decide (p.2 ∈ attends x)⟩ }, by/- injects into X -/⟩
theorem plainOf_knowLift (hinf) (hcar) (attends) : plainOf (knowLift hinf hcar attends) = symDest hinf hcar attends
```

`Recoverable (knowLift …)` is the razor: it holds iff every plain (symmetric) bisimulation already respects the knowing bit, i.e. iff direction is recoverable from the symmetric relating. WS3 proves it FALSE (`ws3_direction_not_recoverable`) on the passive witness. `AttentionDistinguishes` (a plain-bisimilar pair that is label-separated) is the load-bearing shape (following `P1.Reader`, which Series 0 may also cite).

### 2.4 THE VERDICT TYPE (WS5)

```lean
inductive Outcome
  | groundEstablished   -- carrier + reification (WS1), asymmetry genuine/non-recoverable/load-bearing (WS3),
                        --   import seated + quantified (WS4); collapse inherited cleanly (WS2, baseline)
  | partial             -- any obligation lands only per-instance or degenerate
  | obstructed          -- no reification section on the finite functor, OR the asymmetry collapses to a label
  deriving DecidableEq
```

The verdict is `verdict` applied to the WS1/WS3/WS4 flags, each justified by a proof term (§WS5), so it BRANCHES on the certified obligations and cannot be hand-set. WS2 (the inherited collapse) is NOT an input to the verdict (audit d: no verdict hinges on it).

---

## 3. Cross-workstream triage summary

| WS | Owns | Consumes (imported P1) | Delivers | Key risk (design against) |
|---|---|---|---|---|
| WS1 | `attends`, `finsetToPk`, `outDest`, `sym`/`knows`/`attendedBy`, `symDest`, `FinReify`, the tower | `PkObj`, `toPk`, `IsReify`, `ws1_reify_injective` | `ws1_reification_exists`, `ws1_bound_is_finite_attention` | cardinal ceiling readmitted (discipline 1); no reification section (OBSTRUCTED) |
| WS2 | `ws2_collapse_inherited` (transcription) | `ws2_import_theorem_static` | `ws2_collapse_inherited` | relitigating the collapse / a verdict hinging on it (discipline 4) |
| WS3 | `knowLift`, `plainOf_knowLift`, the passive witness | `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `ws1_atomless_bisim` | `ws3_direction_not_recoverable`, `ws3_passive_constitution`, `ws3_active_passive_distinct` | the asymmetry a bare label (discipline 2); direction assumed (discipline 3) |
| WS4 | `impLift`, the exogenous import | `plainOf`, `Recoverable`, `IsBisimL`, `toPk` | `ws4_import_breaks_baseline`, `ws4_import_quantified` | the import named or selected (discipline 5) |
| WS5 | `Outcome`, `verdict`, the audit | WS1/WS3/WS4 payoffs | `ws5_verdict_eq`, `ws5_audit_*`, falsifiability | verdict hand-set; a discipline breached; a name a term |

**The dependency law (protocol §2).** WS1 (the carrier) is ambient for WS2–WS4; WS2, WS3, WS4 are independent given WS1; WS5 consumes WS1/WS3/WS4 and cannot compute until they settle. WS3 is the knot: if it lands OBSTRUCTED (the asymmetry is provably a mere label), the series reports OBSTRUCTED and the ground goes back to the drawing board before S1 builds on it.

---

## 4. The outcomes (COMPUTED, none the lead), per charter §5

- **GROUND-ESTABLISHED** (expected): `ws1_reification_exists` and `ws1_bound_is_finite_attention` (WS1); `ws3_direction_not_recoverable`, `ws3_passive_constitution`, `ws3_active_passive_distinct` (WS3); `ws4_import_breaks_baseline`, `ws4_import_quantified` (WS4); with `ws2_collapse_inherited` transcribed cleanly as baseline.
- **PARTIAL** (pre-registered): reification lands only pointwise (no total section on the finite functor's patterns of interest), OR the asymmetry lands only per-instance (a single witness with no general reader). Reported PARTIAL with the shortfall recorded.
- **OBSTRUCTED** (pre-registered, first-class, the honest terminus): the finite-attention functor admits NO reification section, OR the asymmetry provably collapses to a label (the plain and labelled structures do the same work, `Recoverable (knowLift …)` holds), reported with the precise obstruction. It is far cheaper to learn the ground is wrong here than after S1 builds the tick on it.

The verdict is the residue of the process, not its premise.

---

## 5. The strip test, pre-annotated (protocol §0.3, aggregated by WS5)

- **`ws1_reification_exists`** SHOULD strip to: *"there is a carrier `X`, a finite-out-attention map `attends : X → Finset X`, and a `reify : Finset X → X` with `attends (reify s) = s` for all `s`; `reify` is injective."* A bare `Finset`-section fact.
- **`ws1_bound_is_finite_attention`** SHOULD strip to: *"the out-neighborhoods `(outDest hinf attends x).1` are finite (`mk < ℵ₀`) for every `x`, uniformly in `κ`."* A finiteness fact with no `κ` ceiling.
- **`ws2_collapse_inherited`** SHOULD strip to: *"a behaviorally-identified atomless coalgebra on the symmetric relating is a subsingleton, by `P1.Core.ws2_import_theorem_static`."* The imported engine, verbatim.
- **`ws3_direction_not_recoverable`** SHOULD strip to: *"`¬ Recoverable (knowLift …)`: some plain (symmetric) bisimulation is not a label-bisimulation."* A `Recoverable` fact.
- **`ws3_passive_constitution`** SHOULD strip to: *"an attended-but-not-attending relatum is plain-bisimilar (by `ws1_atomless_bisim`) to an actively-attending one yet not label-bisimilar over `knowLift`; `attendedBy`/`attends` are load-bearing in the statement."* A directed-structure `AttentionDistinguishes` fact, exactly discipline 2's demand.
- **`ws3_active_passive_distinct`** SHOULD strip to: *"`attends a ≠ attends b` for a plain-bisimilar `a, b`, the difference invisible to `symDest`."*
- **`ws4_import_breaks_baseline`** SHOULD strip to: *"for all `Q` and `f : impCar → Q` with `f` separating two states, the exogenous-labelled self-loops are plain-bisimilar yet not label-bisimilar (`¬ Recoverable`)."* A quantified free-label fact.

Any payoff that survives stripping as something OTHER than its named fact, or that needs the deleted word, is flagged. Any name doing a proof's work is SERIOUS.

---

## 6. The `P2S0` module and the registration (Phase E, never earlier)

Namespace `P2S0`. Layout mirrors `program-1/series-13/formal/Series13/`: `formal/P2S0.lean` (imports `P2S0.ws1`…`P2S0.ws5`), `formal/P2S0/wsN.lean`, `formal/P2S0/AxiomCheck.lean`. Each `wsN.lean` opens with `import P1` and `namespace P2S0.WSn` (WS1 also `import Mathlib`; the P1 import transitively supplies Mathlib). Registration in `lake/lakefile.toml` (`[[lean_lib]] name = "P2S0"`, `srcDir = "../program-2/series-0/formal"`, `roots = ["P2S0", "P2S0.AxiomCheck"]`, appended to `defaultTargets`) and in `scripts/gate.sh` (`check program-2/series-0 "^import (P1|P2S0)(\.[A-Za-z0-9_]+)*$"`). Series 0 may import the P1 foundation and its own `P2S0.*` roots, plus Mathlib; any other series' tree is forbidden.

---

*Design index for Series 0. Read this before any `wsN-design.md`; the imported prior art, the ONE new carrier (`attends`), and the ONE new distinction (`knowLift`, the plain/labelled split) are defined here ONCE and cited, never redefined. The five disciplines (§0) are the spine of the review: no cardinal ceiling; the asymmetry not a label; direction non-recoverable; the collapse inherited, not relitigated; the import quantified, not named. The verdict fork is GROUND-ESTABLISHED / PARTIAL / OBSTRUCTED, the verdict a function, never assumed. Program 1's result stands; Series 0 is the ground, relating as finite attending, and the asymmetry of knowing, not the One, is its whole ambition. No em dashes in final academic copy; this working design index is not final copy.*
