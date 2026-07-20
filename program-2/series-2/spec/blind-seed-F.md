# Blind seed F — code review (motivation-free)

You are reviewing a BUILT Lean 4 / Mathlib formalization. The code is at
`program-2/series-2/formal/P2S2/ws1.lean … ws5.lean` (aggregator `formal/P2S2.lean`, axiom pass
`formal/P2S2/AxiomCheck.lean`). Judge ONLY whether the CODE proves the claims below, against the mechanical
criteria in this file. Do not seek motivation or interpretation; there is none to judge.

The build imports an already-verified ground (`P2S1`, reaching `P2S0` and `P1` transitively) with this API:

- `PkObj κ X`; `LkObj κ Q X := PkObj κ (Q × X)`; `outDest hinf attends : X → PkObj κ X` (finite-out-attention
  coalgebra of `attends : X → Finset X`); `IsBisim` / `IsBisimL`; `plainOf`; `Recoverable`.
- `ws1_atomless_bisim dest x y (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y`.
- `ws4_recoverable_not_import dest (hrec : Recoverable dest) x y (h : ∃ R, IsBisim (plainOf dest) R ∧ R x y) : ∃ R, IsBisimL dest R ∧ R x y`.
- `rankLift dest (rank : X → ℕ) : X → LkObj κ (ULift ℕ) X` (tags every edge of `dest x` with `rank x`).
- `AttentionDistinguishes dest x y := (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ ¬ (∃ R, IsBisimL dest R ∧ R x y)`.
- `FiniteAttention dest = ⟨focus, reads, fin, grounded⟩`; `RealFor dest att x := ∃ y ∈ att.reads, AttentionDistinguishes dest x y`.
- `Hold dest`, `HoldPred dest`, `SelfTotal insp t`, `ws1_no_self_total_hold dest insp : ¬ ∃ t, SelfTotal insp t`.
- `ws1_bound_is_finite_attention hinf attends : ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < ℵ₀`.

## What you may read

- `program-2/series-2/formal/P2S2/ws1.lean … ws5.lean`, `formal/P2S2.lean`, `formal/P2S2/AxiomCheck.lean` (the code under review).
- The imported ground sources IF you need to verify an API claim: `program-2/series-1/formal/`,
  `program-2/series-0/formal/`, `program-2/formal/P1/`.

DO NOT read `charter.md`, `charter-status.md`, any `summary*.md`, any `spec/wsNN-design.md`, or any file with
motivating/interpretive prose. Judge the code ONLY against the contracts below. If you accidentally read a
forbidden file, say so explicitly.

## The carrier (in `ws1.lean`)

`RCar := Fin 5`; `slf=0`, `oth=1`, `p=2`, `q=3`, `bnd=4`. `attendsR slf = {slf,oth,p}`, `attendsR oth =
{slf,oth,q}`, `attendsR p = {p}`, `attendsR q = {q}`, `attendsR bnd = {oth}`. `rankR oth = 1`, `rankR bnd = 2`,
else `0`. `reifyR {slf,oth,q} = oth`, `reifyR {oth} = bnd`, else `slf`. `rfield = {slf,oth,p,q}`. The two reaches
`{slf,oth,p}` and `{slf,oth,q}` are INCOMPARABLE (`p ∈ slf∖oth`, `q ∈ oth∖slf`).

## The signatures the code must prove

```lean
-- WS1
theorem ws1_other_is_locus (hinf : ℵ₀ ≤ κ) :
    (reifyR {slf, oth, q} = oth ∧ attendsR (reifyR {slf, oth, q}) = {slf, oth, q})
  ∧ oth ≠ slf ∧ (attendsR oth).Nonempty
  ∧ (slf ∈ rfield ∧ oth ∈ rfield ∧ (∀ z ∈ attendsR slf, z ∈ rfield) ∧ (∀ z ∈ attendsR oth, z ∈ rfield))
  ∧ (∀ x : RCar, Cardinal.mk (↥((outDest hinf attendsR x).1)) < Cardinal.aleph0)
-- WS2
theorem ws2_other_distinguishes (hinf) : AttentionDistinguishes (rankLift (outDest hinf attendsR) rankR) oth slf
noncomputable def slfReader (hinf) : FiniteAttention (rankLift (outDest hinf attendsR) rankR)   -- focus slf, reads {slf}
theorem ws2_other_reader_wise (hinf) : RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth
theorem ws2_other_non_recoverable (hinf) : ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
-- WS3
def faces (x y : RCar) : Prop := y ∈ attendsR x
theorem ws3_four_readings : faces slf slf ∧ faces slf oth ∧ faces oth slf ∧ faces oth oth
noncomputable def faceLift (hinf) : RCar → LkObj κ (ULift Bool) RCar   -- tags edge (x,z) with decide (rankR x < rankR z)
theorem ws3_facing_asymmetric (hinf) :
    (oth ∈ attendsR slf ∧ slf ∈ attendsR oth)
  ∧ (∃ z ∈ attendsR slf, rankR slf < rankR z) ∧ (¬ ∃ z ∈ attendsR oth, rankR oth < rankR z)
  ∧ ¬ Recoverable (faceLift hinf)
theorem ws3_facing_partial (hinf) :
    (slf ∈ attendsR slf ∧ oth ∈ attendsR oth)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
-- WS4
theorem ws4_mutual_residue (hinf) :
    ((oth ∈ attendsR slf ∧ slf ∈ attendsR oth) ∧ (slf ∈ attendsR slf ∧ oth ∈ attendsR oth))
  ∧ (∃ y : RCar, (∃ R, IsBisim (outDest hinf attendsR) R ∧ R oth y) ∧ y ∉ attendsR slf ∧ y ∉ attendsR oth)
  ∧ (∀ z ∈ attendsR bnd, rankR z < rankR bnd)
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
  ∧ (∀ insp : Hold (outDest hinf attendsR) → HoldPred (outDest hinf attendsR), ¬ ∃ t, SelfTotal insp t)
-- WS5
inductive Outcome | twoFacing | one | totalized | partial' | disconnected
def verdict (wf readerTwo facing nonCollapse nonTotal : Bool) : Outcome   -- (see ws5.lean)
theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoFacing
theorem ws5_verdict_discriminates : … (four flips → one / totalized / disconnected / partial')
theorem ws5_flags_justified (hinf) : … (bundles the WS1-WS4 headline props)
-- audit: ws5_audit_reader_loadbearing / twoness_import / facing_asymmetric / residue_genuine (proof-term aliases),
--        ws5_audit_downstream_open : True, ws5_audit_names_not_terms : True
```

## Your task

1. For EACH signature, verify the CODE actually proves the STATED type — no `sorry`, no `admit`, no cheat
   (e.g. an `axiom`, a `native_decide` masking a false claim, a hypothesis assumed then returned, a weaker
   theorem than the headline). Confirm the build is sorry-free and axiom-clean (standard three:
   `propext`, `Classical.choice`, `Quot.sound`) via `AxiomCheck.lean`.
2. Check each signature is NON-VACUOUS (the type is not trivially satisfiable / does not smuggle its content into
   a hypothesis). In particular verify `ws2_other_distinguishes` genuinely proves both the plain-bisim and the
   label-separation (not one horn), and `faceLift`'s `plainOf` is the symmetric relating.
3. Run the STRIP TEST on each payoff; report each stripped reading (delete the interpretive words; does the
   theorem still state a bare `attends`/`RealFor`/`AttentionDistinguishes`/`Recoverable`/bisim/rank/diagonal
   fact?).
4. Run the NAMES-NOT-TERMS grep over `formal/`: `grep -rniE "\b(self|other|perspective|love|loved|gaze|god|choice|subjectivity)\b"`.
   Confirm every hit is docstring/comment PROSE, and no proof term, `def`, or `theorem` IDENTIFIER is a standalone
   forbidden content word (underscore-embedded substrings like `..._other_...` are neutral position labels and
   permitted). Also grep `(converg|cohere)` and confirm no identifier decides coherence/convergence.
5. Confirm the audit clauses (a)-(e). ESPECIALLY:
   - **(a)** `ws2_other_reader_wise` proves `RealFor` for the FIXED named `slfReader` (reader load-bearing, not
     `∃ att`, not `Many`); `attendsR oth` is load-bearing (could `oth` be a fresh inert tag and every payoff
     still hold?).
   - **(d)** In `ws4_mutual_residue`: is conjunct (1)'s residue genuinely load-bearing on the JOINT/mutual
     attention given the INCOMPARABLE reaches (is EACH non-membership conjunct necessary — does dropping the
     `slf` conjunct admit a spurious witness, and dropping the `oth` conjunct another?), or is the payoff carried
     solely by conjunct (5), the global `ws1_no_self_total_hold` (true on every coalgebra)? Is the reading order
     rank-constrained (2), not free? Are the collapse/totalize arms reachable via `ws5_verdict_discriminates`?
     Does ANY signature decide coherence/convergence (a `Converges₂`-style claim)?
6. Grade every finding SERIOUS / REAL / COSMETIC per the rubric below.

## The grading rubric

- **SERIOUS:** the verdict rests on it; a `sorry`/`admit`/`axiom`/cheat; the other a bare label / the reader
  quantified out (a); the twoness recoverable (b); the facing asymmetry the twoness relabelled or an inert tag
  (c); the mutual residue decided by fiat / carried only by the global diagonal with mutuality decorative (d);
  the reading order free/total; the coherence decided; a forbidden content word is a proof-term identifier (e);
  or an undisclosed narrowing between the signatures and what the code proves.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed conjunct, an assumed-and-returned
  hypothesis, an over-strong name, a bare conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Report a structured list of findings, each with a stable ID (`Fn-Sm`), a GRADE, an EXACT location (file, theorem
name, conjunct/line), and the DEFECT. Give a one-line verdict per WS1-WS5 on whether the code proves the claimed
signature. If you find zero SERIOUS findings, say so explicitly. Be precise and terse.
