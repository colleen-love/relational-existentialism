# Blind seed — Phase F (code review)

You are reviewing Lean 4 (Mathlib, `Cardinal.{0}`) CODE and judging whether it PROVES the claimed signatures. The
code is sorry-free and compiles; your job is not to re-run the compiler but to judge whether each theorem's
STATEMENT is the claimed contract (no hidden weakening, no assumed-and-returned hypothesis, no vacuity, no
over-strong name), whether the audit clauses hold, and whether the strip test and names-not-terms grep pass.

## Files you MAY read

- `/home/user/relational-existentialism/program-2/series-6/spec/blind-seed-F.md` (this file)
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/ws1.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/ws2.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/ws3.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/ws4.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/ws5.lean`
- `/home/user/relational-existentialism/program-2/series-6/formal/P2S6/AxiomCheck.lean`

Do NOT read: `charter.md`, `charter-status.md`, `charter-extension.md`, any `summary*.md`, any `spec/*-design.md`,
`spec/README.md`, `spec/blind-seed-C.md`, or any predecessor series' files. Judge the code ONLY against the
contracts in this seed. The `formal/` files carry docstring prose; judge the THEOREMS, not the prose. If you
cannot answer without reading a forbidden file, say so rather than reading it.

## 0. Imported machinery (proved in the imported chain; treat as given, do not re-check)

```
PkObj κ X ; LkObj κ Q X := PkObj κ (Q × X) ; SHNE (dest) (x) ; outDest (hinf) (attends)
IsBisim (dest) (R) ; IsBisimL (dest) (R) ; plainOf (dest : X → LkObj κ Q X) : X → PkObj κ X
Recoverable (dest) := ∀ R, IsBisim (plainOf dest) R → IsBisimL dest R
AttentionDistinguishes (dest) (x y) := (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)
ws1_atomless_bisim (dest) (x y) (SHNE x) (SHNE y) : ∃ R, IsBisim dest R ∧ R x y          -- collapse engine
ws4_recoverable_not_import (dest) (Recoverable dest) (x y) (∃ R, IsBisim (plainOf dest) R ∧ R x y) : ∃ R, IsBisimL dest R ∧ R x y
rankLift (dest) (lab : X → ℕ) : X → LkObj κ (ULift ℕ) X ; pkSingle (hinf) (y) : PkObj κ {y}
-- the tick carrier TCar = Fin 7 with attendsT/rankT/reifyT/kA/kB/kC/isTick/causal, ws1_tcar_SHNE,
-- and Series 2.1's linearization import:
ws4_linearization_import (hinf) : ∀ ord : TCar → ℕ, ord kA ≠ ord kB →
    AttentionDistinguishes (rankLift (outDest hinf attendsT) ord) kA kB ∧ ¬ Recoverable (rankLift (outDest hinf attendsT) ord)
ws4_causal_order_endogenous : (causal kA kC ∧ causal kB kC) ∧ (∀ t u, causal t u → rankT t < rankT u) ∧ (¬ causal kA kB ∧ ¬ causal kB kA)
```

## 1. The contracts the code must prove (check each theorem's STATEMENT matches)

```
-- WS1 (ws1.lean): strict identity fails across a tick (the trivial ground).
succDep (t u : TCar) : Prop := isTick t ∧ isTick u ∧ t ∈ attendsT u
ws1_succ_witnessed : succDep kA kC ∧ succDep kB kC
ws1_strict_fails (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsT) rankT) kC kA

-- WS2 (ws2.lean): the weak continuity, its two carriers, and the fork's substance.
plainOf_rankLift_gen (dest) (lab) : plainOf (rankLift dest lab) = dest
const_first_recoverable (destL : X → LkObj κ Q X) (c : Q) (hconst : ∀ x, ∀ p ∈ (destL x).1, p.1 = c) : Recoverable destL
distinguishes_not_recoverable (destL) (x y) (AttentionDistinguishes destL x y) : ¬ Recoverable destL
MCar := Fin 2 ; m0 m1 ; attendsM (m0⇄m1) ; rankM (0,1) ; mergeLift (uniform mark `true`) ; ws_mcar_SHNE
CCar := Bool ; c0 c1 ; cutLift (directional mark) ; cutKnows (c0 knows c1) ; mergeKnows (mutual)
ws2_cont_recoverable   (hinf) : Recoverable (mergeLift hinf)
ws2_cont_is_import     (hinf) : ¬ Recoverable (cutLift hinf)
ws2_weaker_than_strict (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0 ∧ Recoverable (mergeLift hinf)

-- WS3 (ws3.lean): the single line is the linearization import.
ws3_line_is_import (hinf) : ∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord)
ws3_partial_order_endogenous : (causal kA kC ∧ causal kB kC) ∧ (∀ t u, causal t u → rankT t < rankT u) ∧ (¬ causal kA kB ∧ ¬ causal kB kA)
ws3_line_not_scalar : rankT kA = rankT kB

-- WS4 (ws4.lean): the fork (both reachable, self-relative) + the mortality companion.
ws4_woven_reachable    (hinf) : Recoverable (mergeLift hinf)
ws4_severed_reachable  (hinf) : ¬ Recoverable (cutLift hinf)
ws4_carrier_relative   (hinf) : Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
ws4_cessation_relative (hinf) : (∃ x : CCar, ∀ y : CCar, ¬ cutKnows y x) ∧ ¬ Recoverable (cutLift hinf)
ws4_conservative_reachable : ∀ x : MCar, ∃ y : MCar, mergeKnows y x

-- WS5 (ws5.lean): the verdict computed.
inductive Outcome | woven | severed | shapeDrawn | partial'
verdict (strictFails lineIsImport wovenReachable severedReachable carrierDecided carrierWoven : Bool) : Outcome
ws5_verdict_eq : verdict true true true true false false = Outcome.shapeDrawn
ws5_verdict_discriminates : reaches woven, severed, partial', partial' on flipped flags
ws5_flags_justified (hinf) : (strictFails prop) ∧ (lineIsImport prop) ∧ Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf)
ws5_carrier_relative_verdict (hinf) : verdict … = shapeDrawn ∧ (Recoverable (mergeLift hinf) ∧ ¬ Recoverable (cutLift hinf))
ws5_audit_no_absolute / _fork_genuine / _knot_not_strict / _line_is_import (hinf) ; ws5_audit_names_not_terms : True
```

## 2. Success criteria (restated mechanically) — same as the design contract

1. `ws1_strict_fails` proves `AttentionDistinguishes … kC kA` (plain-bisimilar via the collapse engine, rank-lift
   separated because `rankT kC ≠ rankT kA`). (WS1)
2. `ws2_cont_recoverable` proves `Recoverable (mergeLift hinf)` via `const_first_recoverable` (mark uniform
   `true`); `ws2_cont_is_import` proves `¬ Recoverable (cutLift hinf)` via `AttentionDistinguishes`;
   `ws2_weaker_than_strict` proves, over one relating `outDest hinf attendsM`, the rank lift separates `m1`,`m0`
   while `mergeLift` is recoverable. (WS2)
3. `ws3_line_is_import` proves, for all `ord` with `ord kA ≠ ord kB`, `¬ Recoverable (rankLift … ord)` (reducing
   to `ws4_linearization_import`); `ws3_line_not_scalar` proves `rankT kA = rankT kB`. (WS3)
4. `ws4_carrier_relative` proves both horns; `ws4_cessation_relative` proves a `CCar` node nothing knows plus the
   import; `ws4_conservative_reachable` proves every `MCar` node is known. (WS4)
5. `verdict` computes `shapeDrawn` on the certified tuple by `rfl` and reaches all four outcomes; the four
   DECIDING inputs are the WS1–WS4 propositions (the two carrier meta-flags are `carrierDecided = false` /
   `carrierWoven`, the former grounded by `ws5_carrier_relative_verdict`). (WS5)

## 3. Audit checks (mechanical instructions) — PRESS HARDEST on (c), (b), (d)

- **(c) THE KNOT IS THE WEAK CONTINUITY, NOT THE STRICT FAILURE (the costume gate).** Read `verdict`. Confirm it
  returns a decided outcome only when `lineIsImport = true` AND `wovenReachable && severedReachable = true`;
  confirm `verdict true false _ _ _ _ = partial'` and that `strictFails` alone never yields a decided outcome
  (check `ws5_audit_knot_not_strict`). Flag SERIOUS if the verdict rests on strict identity failing.
- **(b) THE FORK NOT BY FIAT.** Confirm `cutLift`'s plain reduct is the symmetric 2-cycle (both `SHNE`), so
  `c0`,`c1` are genuinely plain-bisimilar and the label-separation is real (SEVERED not excluded by construction).
  Confirm the weak continuity is genuinely WEAKER than strict identity: `ws2_weaker_than_strict` separates
  `m1`,`m0` by the rank lift while `mergeLift` is recoverable — i.e. `mergeLift` is NOT `rankLift … rankM`
  relabelled (its mark is constant `true`, not `rankM`). Judge whether `ws2_cont_recoverable` (constant-mark
  recoverable) is vacuous or genuinely pins the WOVEN branch to `outDest hinf attendsM`.
- **(d) THE LINE IS THE LINEARIZATION IMPORT, NOT SCALAR RANK.** Confirm `ws3_line_is_import` is the
  non-recoverability of the total order (all `ord`), and `ws3_line_not_scalar` (`rankT kA = rankT kB`) shows rank
  does not linearize the incomparable pair. Flag SERIOUS if the 1D-line claim rests on scalar rank.
- **(a) NO ABSOLUTE PERSISTENCE.** Confirm no theorem asserts a recoverable continuity for ALL carriers; both a
  `Recoverable` and a non-`Recoverable` lift are exhibited. Flag SERIOUS if persistence is asserted absolutely.
- **(e) NAMES-NOT-TERMS.** Grep every identifier (def / theorem / lemma / abbrev / inductive / constructor) in the
  `formal/` files for the forbidden content-words as WHOLE words (`\b`, case-insensitive):
  `self|thread|persistence|life|death|time|here|there|god|choice|subjectivity`. Report any IDENTIFIER that is one
  of these as a standalone word. Docstring/comment prose is exempt (report only if the WORD is a proof-term name).

## 4. Strip test

For each payoff, delete the interpretive reading and confirm it stands as a bare fact:
- `ws1_strict_fails` → reified relatum plain-bisimilar to constituent, rank-lift-separated.
- `ws2_cont_recoverable` → uniform-label lift is `Recoverable`; `ws2_cont_is_import` → separating lift not
  `Recoverable`; `ws2_weaker_than_strict` → coarse lift recoverable while rank lift separates the same pair.
- `ws3_line_is_import` → any incomparable-pair-distinguishing order lift not `Recoverable`; `ws3_line_not_scalar`
  → `rankT kA = rankT kB`.
- `ws4_carrier_relative` → a `Recoverable` and a non-`Recoverable` lift both exist; `ws4_cessation_relative` → a
  node no directed edge points to, plus a non-`Recoverable` lift; `ws4_conservative_reachable` → every node is a
  directed-edge target.
- `verdict` → a six-boolean function into `Outcome` reaching four values, `= shapeDrawn` on the certified tuple.
Flag any payoff that does NOT survive (vacuous, circular, interpretation-dependent). In particular judge whether
`ws2_cont_recoverable` is a genuine continuity result or a vacuous triviality.

## 5. Grading rubric

- **SERIOUS:** the verdict rests on it; the knot rests on strict identity failing not the weak continuity + the
  linearization (audit c); the 1D-line claim rests on scalar rank (audit d); the fork is a fiat — SEVERED excluded
  or the weak continuity is the rank lift relabelled (audit b); persistence asserted absolutely (audit a); a name
  is a forbidden content-word (audit e); an outcome decided without the computation; a theorem's STATEMENT
  silently weaker than the claimed contract; or a hypothesis assumed and returned.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed statement/docstring, an over-strong name,
  a vacuous side, a mismatched-carrier bundle).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings, each with a stable ID `Fn-Sm`, its grade, exact location (file + theorem
name), and the defect. If you find nothing SERIOUS, say so explicitly.
