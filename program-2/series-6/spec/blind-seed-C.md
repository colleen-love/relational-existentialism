# Blind seed — Phase C (design review)

You are reviewing a set of Lean 4 (Mathlib, `Cardinal.{0}`) design signatures for coherence and non-vacuity.
Judge ONLY the mathematics below against the contracts stated here. This seed is self-contained; do NOT read any
other file in this repository.

## 0. Imported machinery you may assume (proved elsewhere, treat as given)

```
-- powerset-coalgebra / bisimulation / recoverability layer:
PkObj (κ) (X) : Type                          -- κ-bounded subsets of X
LkObj (κ) (Q) (X) : Type := PkObj κ (Q × X)   -- labelled: successors carry a coordinate from Q
SHNE (dest : X → PkObj κ X) (x : X) : Prop     -- every reachable node has a nonempty successor set (no leaf)
outDest (hinf : ℵ₀ ≤ κ) (attends : X → Finset X) : X → PkObj κ X
attendedBy (attends : X → Finset X) (x : X) : Set X := {z | x ∈ attends z}   -- passive in-attention
pkSingle (hinf : ℵ₀ ≤ κ) (y : Y) : PkObj κ Y   -- the bounded singleton {y}

IsBisim  (dest : X → PkObj κ X) (R : X → X → Prop) : Prop      -- plain bisimulation
IsBisimL (dest : X → LkObj κ Q X) (R : X → X → Prop) : Prop    -- label-respecting bisimulation
plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X               -- forget the label, keep the target
Recoverable (dest : X → LkObj κ Q X) : Prop
  := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R           -- every plain bisim is a label bisim
AttentionDistinguishes (dest : X → LkObj κ Q X) (x y : X) : Prop
  := (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)

-- THE COLLAPSE ENGINE: any two SHNE (atomless) states are plain-bisimilar.
ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y
-- A recoverable label is not an import (negative horn):
ws4_recoverable_not_import (dest) (hrec : Recoverable dest) (x y)
    (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) : ∃ R, IsBisimL dest R ∧ R x y

-- the rank-labelled lift (broadcasts a ℕ label on all out-edges of a node):
rankLift (dest : X → PkObj κ X) (lab : X → ℕ) : X → LkObj κ (ULift ℕ) X
plainOf_rankLift : plainOf (rankLift dest lab) = dest     -- (proved for each concrete carrier)

-- a fixed finite tick witness carrier (proved facts about it may be assumed):
TCar := Fin 7 ; nodes p0 p1 q0 q1 kA kB kC
attendsT : TCar → Finset TCar   -- p0⇄p1, q0⇄q1 (two 2-cycles); kA↦{p0,p1}, kB↦{q0,q1}, kC↦{kA,kB}
rankT    : TCar → ℕ             -- kA,kB ↦ 1 ; kC ↦ 2 ; else 0
reifyT   : Finset TCar → TCar   -- {p0,p1}↦kA, {q0,q1}↦kB, {kA,kB}↦kC
isTick (x) : Prop := x = kA ∨ x = kB ∨ x = kC
causal (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u
ws1_tcar_SHNE (hinf) (x) : SHNE (outDest hinf attendsT) x
-- Series 2.1's linearization import (treat as given, proved elsewhere):
ws4_linearization_import (hinf) : ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
      AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB
    ∧ ¬ Recoverable (rankLift (outDest hinf attendsT) ord)
ws4_causal_order_endogenous :
    (causal kA kC ∧ causal kB kC) ∧ (∀ t u, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA)
```

## 1. The definitions and signatures under review

```
-- WS1: the tick-successor relation, and STRICT identity failing across a tick.
@[reducible] def succDep (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u
theorem ws1_succ_witnessed : succDep kA kC ∧ succDep kB kC
theorem ws1_strict_fails (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA

-- WS2: general recoverability lemmas, the two fresh carriers, and the weak-continuity fork.
lemma plainOf_rankLift_gen (dest : X → PkObj κ X) (lab : X → ℕ) : plainOf (rankLift dest lab) = dest
theorem const_first_recoverable (destL : X → LkObj κ Q X) (c : Q)
    (hconst : ∀ x, ∀ p ∈ (destL x).1, p.1 = c) : Recoverable destL
theorem distinguishes_not_recoverable (destL : X → LkObj κ Q X) (x y : X)
    (h : AttentionDistinguishes destL x y) : ¬ Recoverable destL

abbrev MCar := Fin 2 ; def m0 : MCar := 0 ; def m1 : MCar := 1
def attendsM : MCar → Finset MCar := fun x => if x = m0 then {m1} else {m0}     -- m0 ⇄ m1 (mutual)
def rankM : MCar → ℕ := fun x => if x = m0 then 0 else 1
def mergeLift (hinf) : MCar → LkObj κ Bool MCar :=                              -- uniform mark `true`
  fun x => if x = m0 then pkSingle hinf (true, m1) else pkSingle hinf (true, m0)
lemma ws_mcar_SHNE (hinf) (x : MCar) : SHNE (outDest hinf attendsM) x

abbrev CCar := Bool ; def c0 : CCar := true ; def c1 : CCar := false
def cutAttends : CCar → Finset CCar := fun x => if x = c0 then {c1} else ∅      -- c0 → c1 (one-way)
def cutLift (hinf) : CCar → LkObj κ CCar CCar :=                                -- directional mark
  fun x => if x = c0 then pkSingle hinf (c0, c1) else pkSingle hinf (c1, c0)

theorem ws2_cont_recoverable (hinf) : Recoverable (mergeLift hinf)
theorem ws2_cont_is_import   (hinf) : ¬ Recoverable (cutLift hinf)
theorem ws2_weaker_than_strict (hinf) :
    AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0
  ∧ Recoverable (mergeLift hinf)

-- WS3: the single line as the linearization import (reuses the given ws4_linearization_import).
theorem ws3_line_is_import (hinf) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)
theorem ws3_partial_order_endogenous :
    (causal kA kC ∧ causal kB kC) ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
  ∧ (¬ causal kA kB ∧ ¬ causal kB kA)
theorem ws3_line_not_scalar : rankT kA = rankT kB

-- WS4: the fork (both reachable, self-relative) + the mortality companion.
theorem ws4_woven_reachable   (hinf) : Recoverable (mergeLift hinf)
theorem ws4_severed_reachable (hinf) : ¬ Recoverable (cutLift hinf)
theorem ws4_carrier_relative  (hinf) : Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
theorem ws4_cessation_relative (hinf) :
    (∃ x : CCar, attendedBy cutAttends x = ∅) ∧ ¬ Recoverable (cutLift hinf)
theorem ws4_conservative_reachable : ∀ x : MCar, (attendedBy attendsM x).Nonempty

-- WS5: the verdict computed from the flags.
inductive Outcome | woven | severed | shapeDrawn | partial'
def verdict (strictFails lineIsImport wovenReachable severedReachable carrierDecided carrierWoven : Bool) : Outcome :=
  if !strictFails || !lineIsImport then partial'
  else if !(wovenReachable && severedReachable) then partial'
  else if !carrierDecided then shapeDrawn
  else if carrierWoven then woven
  else severed
theorem ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn
theorem ws5_verdict_discriminates :
    verdict true true true true true true = woven ∧ verdict true true true true true false = severed
  ∧ verdict false true true true false false = partial' ∧ verdict true true true false false false = partial'
theorem ws5_flags_justified (hinf) :
    AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord))
  ∧ Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
theorem ws5_carrier_relative_verdict (hinf) :
    verdict true true true true false false = Outcome.shapeDrawn
  ∧ (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf))
-- audit clauses (a)–(e): ws5_audit_no_absolute, ws5_audit_fork_genuine, ws5_audit_knot_not_strict,
-- ws5_audit_line_is_import (bundles ws3_line_is_import, rankT kA = rankT kB, ws3_partial_order_endogenous),
-- ws5_audit_names_not_terms : True.
```

## 2. Success criteria (restated mechanically)

1. `succDep` holds on `(kA,kC)` and `(kB,kC)`; `kC` (the reified successor) and `kA` (its constituent) are
   plain-bisimilar yet not bisimilar over `rankLift … rankT` (`AttentionDistinguishes`). (WS1)
2. There is a labelled lift `mergeLift` that is `Recoverable`, and a labelled lift `cutLift` that is NOT
   `Recoverable`; and over one plain relating (`outDest hinf attendsM`) the rank lift separates `m1`,`m0` while
   the continuity lift `mergeLift` is `Recoverable` and its plain reduct relates them. (WS2)
3. For any `ord` with `ord kA ≠ ord kB`, `rankLift (outDest hinf attendsT) ord` is not `Recoverable`; the partial
   `causal` order is witnessed, rank-constrained, and has an incomparable pair; `rankT kA = rankT kB`. (WS3)
4. `Recoverable (mergeLift hinf)` and `¬ Recoverable (cutLift hinf)` both hold; there is a `CCar` node whose
   `attendedBy` is empty; every `MCar` node's `attendedBy` is nonempty. (WS4)
5. `verdict` computes `shapeDrawn` on the certified flag tuple by `rfl`, reaches all four outcomes, and its
   boolean inputs are exactly the WS1–WS4 propositions. (WS5)

## 3. Audit checks (mechanical instructions)

- **(a) NO ABSOLUTE PERSISTENCE.** Confirm no signature asserts a recoverable continuity holds for ALL carriers
  (frame-independently). The continuity results are each stated FOR a carrier (`mergeLift`, `cutLift`), and both a
  `Recoverable` and a non-`Recoverable` lift are exhibited (`ws4_carrier_relative`). Flag SERIOUS if any theorem
  asserts the continuity holds absolutely / on every carrier.
- **(b) THE FORK NOT BY FIAT.** Confirm WOVEN (`ws2_cont_recoverable`) and SEVERED (`ws2_cont_is_import`) are both
  reachable, and that the weak continuity is genuinely WEAKER than strict identity: `ws2_weaker_than_strict`
  exhibits, over one relating, a pair the rank lift (strict) separates while the continuity lift (weak) is
  recoverable. Flag SERIOUS if the weak continuity is secretly the rank lift relabelled (i.e. `mergeLift`'s plain
  reduct differs from `outDest hinf attendsM`, or `mergeLift` = `rankLift … rankM`), or if SEVERED is excluded by
  construction. Judge whether `const_first_recoverable` genuinely makes `mergeLift` recoverable and whether that
  recoverable continuity is NON-VACUOUS (relates the rank-distinct pair `m1`,`m0`).
- **(c) THE KNOT IS THE WEAK CONTINUITY, NOT THE STRICT FAILURE.** Trace `verdict`: it returns a decided outcome
  (`woven`/`severed`/`shapeDrawn`) only when `lineIsImport = true` AND `wovenReachable && severedReachable = true`.
  Confirm `verdict true false _ _ _ _ = partial'` (strict failing with no line import does NOT decide) and that
  the strict-failure flag alone never yields a decided outcome. Flag SERIOUS if `verdict` would return a decided
  outcome from `strictFails` alone (the knot resting on strict identity failing — the costume).
- **(d) THE LINE IS THE LINEARIZATION IMPORT, NOT SCALAR RANK.** Confirm `ws3_line_is_import` is the
  non-recoverability of the total order (quantified over all `ord`), reducing to the given
  `ws4_linearization_import`, and that `ws3_line_not_scalar` (`rankT kA = rankT kB`) shows the endogenous rank does
  NOT linearize the incomparable pair. Flag SERIOUS if the 1D-line claim rests on rank being a scalar rather than
  on the linearization being non-recoverable.
- **(e) NAMES-NOT-TERMS.** Grep the identifiers above for the forbidden content-words as WHOLE words
  (`\b`-delimited, case-insensitive): `self|thread|persistence|life|death|time|here|there|god|choice|subjectivity`.
  Report any identifier (definition, theorem, constructor) that IS one of these as a standalone word. (Substrings
  glued by `_`/camelCase, e.g. `succDep`, `ws3_line_is_import`, `Outcome.woven`, `carrier_relative`, are NOT
  whole-word matches and are acceptable.)

## 4. Strip test

For each payoff, delete the interpretive reading and check the statement still stands as a bare fact:
- `ws1_strict_fails` → "a reified relatum is plain-bisimilar to a constituent but rank-lift-separated."
- `ws2_cont_recoverable` → "a labelled lift with one edge-label value is `Recoverable`."
- `ws2_cont_is_import` → "a labelled lift separating a plain-bisimilar pair is not `Recoverable`."
- `ws2_weaker_than_strict` → "over one relating a coarse lift is recoverable while the rank lift separates the
  same pair."
- `ws3_line_is_import` → "for any order label distinguishing an incomparable pair, the ordered lift is not
  `Recoverable`."
- `ws4_carrier_relative` → "both a `Recoverable` and a non-`Recoverable` lift exist."
- `ws4_cessation_relative` → "a node with empty in-attention exists; a lift over its relating is not `Recoverable`."
- `verdict` → "an `Outcome`-valued function of six booleans reaching four values."
Flag any payoff that does NOT survive the strip (vacuous, circular, or dependent on the interpretation). In
particular judge: is `ws2_cont_recoverable` (a uniform-label lift is recoverable) a genuine continuity result or a
vacuous triviality that trivialises the WOVEN side of the fork?

## 5. Grading rubric

- **SERIOUS:** the verdict rests on it; the knot rests on strict identity failing rather than the weak continuity
  and the linearization (audit c); the 1D-line claim rests on scalar rank (audit d); the fork is a fiat — SEVERED
  excluded, or the weak continuity is the rank lift relabelled (audit b); persistence is asserted absolutely
  (audit a); a name is a forbidden content-word (audit e); an outcome is decided without the computation; or an
  undisclosed narrowing.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed statement, an assumed-and-returned
  hypothesis, an over-strong name, a strict-failure dressed as a weak-continuity interaction, a vacuous
  recoverable side).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings, each with a stable ID `Cn-Sm`, its grade, exact location (signature name),
and the defect. If you find nothing SERIOUS, say so explicitly.
