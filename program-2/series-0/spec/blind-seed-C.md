# Blind seed — Phase C (design review)

You are reviewing a set of Lean 4 / Mathlib design signatures for mathematical coherence and non-vacuity. Judge ONLY the mathematical claims below against the contracts stated here. Do not consult any other file except the ones this seed names (see "Files you may read").

## Files you may read

- THIS file (`spec/blind-seed-C.md`).
- The design signature docs `spec/ws1-design.md`, `spec/ws2-design.md`, `spec/ws3-design.md`, `spec/ws4-design.md`, `spec/ws5-design.md` — but ONLY the Lean signature blocks and the paper-triage tables. Ignore any surrounding prose.
- The imported prior art it builds on: `program-2/formal/P1/Core.lean` and `program-2/formal/P1/Reader.lean` (already built, sorry-free, axiom-clean). These are the definitions of `PkObj`, `IsReify`, `IsBisim`, `IsBisimL`, `plainOf`, `Recoverable`, `ws1_atomless_bisim`, `ws2_import_theorem_static`, `toPk`, `labelLoop`, `ws4_labelLoop_not_recoverable`, `AttentionDistinguishes`, `rankLift`, etc.

DO NOT READ: `charter.md`, `charter-status.md`, `README.md`, any `summary*.md`, or any file with motivating prose. Judge the signatures only against the contracts here. If you read a forbidden file, say so and stop.

## The objects under review (definitions, no motivation)

A new carrier `attends : X → Finset X` (a coalgebra of the finite-powerset functor). Read from it:
- `knows attends x y := y ∈ attends x` (a directed relation).
- `sym attends x y := y ∈ attends x ∨ x ∈ attends y` (the symmetric closure).
- `attendedBy attends x := {z | x ∈ attends z}` (a `Set X`, possibly infinite).
- `finsetToPk (hinf : ℵ₀ ≤ κ) (s : Finset X) : PkObj κ X := ⟨↑s, _⟩` (a finite set is `< ℵ₀ ≤ κ`).
- `outDest hinf attends x := finsetToPk hinf (attends x)` (the finite out-attention as a `PkObj κ`-coalgebra).
- `symDest hinf (hcar : mk X < κ) attends x := ⟨{y | sym attends x y}, _⟩` (the symmetric relating as a `PkObj κ`-coalgebra; well-defined because `{y | sym x y} ⊆ X` has cardinality `≤ mk X < κ`).
- `knowLift hinf (hcar : mk X < κ) attends x := ⟨{p | sym attends x p.2 ∧ p.1 = ⟨decide (p.2 ∈ attends x)⟩}, _⟩ : X → LkObj κ (ULift Bool) X` (each symmetric neighbor tagged with the knowing bit), with the claim `plainOf (knowLift …) = symDest …`.

## The signatures under review (the claims)

WS1:
- `FinReify attends reify := ∀ s : Finset X, attends (reify s) = s`.
- `ws1_finreify_injective : FinReify attends reify → Function.Injective reify`.
- `ws1_reification_exists : ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X), FinReify attends reify ∧ Function.Injective reify`.
- `ws1_bound_is_finite_attention (hinf) (attends) : ∀ x, Cardinal.mk (↥((outDest hinf attends x).1)) < Cardinal.aleph0`.
- `finReifyStep`, `finTowerN`, `ws1_tower_monotone` (a `⊆`-monotone `ℕ`-tower).

WS2:
- `ws2_collapse_inherited (hinf) (hcar : mk X < κ) (attends) (hbehav : BehaviorallyIdentified (symDest …)) (hatom : ∀ x, SHNE (symDest …) x) : Subsingleton X`, proved as `P1.Core.ws2_import_theorem_static (symDest …) hbehav hatom`.

WS3 (witness: `DCar := ULift Bool`, `a := ⟨true⟩`, `b := ⟨false⟩`, `attendsD x := if x = a then {b} else ∅`; `knowLiftD` the knowing-labelled lift on this carrier):
- `ws3_direction_not_recoverable (hinf) : ¬ Recoverable (knowLiftD hinf)`.
- `ws3_passive_constitution (hinf) : (a ∈ attendedBy attendsD b ∧ attendsD b = ∅) ∧ AttentionDistinguishes (knowLiftD hinf) a b`.
- `ws3_active_passive_distinct (hinf) : (attendsD a ≠ attendsD b) ∧ (∃ R, IsBisim (plainOf (knowLiftD hinf)) R ∧ R a b) ∧ (¬ ∃ R, IsBisimL (knowLiftD hinf) R ∧ R a b)`.

WS4 (import carrier `impCar := ULift Bool`, `attendsI x := {x}`; `impLift hinf (f : impCar → Q) i := toPk hinf {(f i, i)}`):
- `ws4_import_breaks_baseline (hinf) : ∀ {Q} (f : impCar → Q), f ⟨true⟩ ≠ f ⟨false⟩ → (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R ⟨true⟩ ⟨false⟩) ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R ⟨true⟩ ⟨false⟩)`.
- `ws4_import_quantified (hinf) : (∀ {Q} (f : impCar → Q), plainOf (impLift hinf f) = plainOf (impLift hinf (fun _ => (⟨true⟩ : impCar)))) ∧ ¬ Recoverable (impLift hinf id)`.

WS5:
- `Outcome := groundEstablished | partial | obstructed`.
- `verdict (reif asym imp : Bool) : Outcome := if reif && asym && imp then .groundEstablished else if reif && asym then .partial else .obstructed`.
- `ws5_verdict_eq : verdict true true true = .groundEstablished` (`rfl`).
- `ws5_flags_justified`, the audit clauses `ws5_audit_no_ceiling`/`_asymmetry_not_label`/`_direction_free`/`_collapse_inherited`/`_import_quantified`, and falsifiability `ws5_verdict_not_obstructed`/`_not_partial` (`by decide`).

## Success criteria (mechanical, motivation removed)

1. WS1: a `reify : Finset X → X` with `attends ∘ reify = id` on `Finset X`, shown to EXIST non-vacuously (a genuine — ideally bijective — witness, not the empty/degenerate carrier), plus a finiteness bound `mk (out-neighborhood) < ℵ₀` uniform in `κ`.
2. WS2: `Subsingleton X` from `BehaviorallyIdentified` + atomless over `symDest`, obtained as a direct application of the imported `ws2_import_theorem_static` (not re-derived).
3. WS3: (c) `¬ Recoverable (knowLiftD)` a proof term; (b) a plain-bisimilar-yet-label-separated pair with `attends`/`attendedBy` load-bearing in the statement; the two modes distinct.
4. WS4: a labelled lift, quantified over ALL `Q` and `f`, plain-bisimilar yet label-separated whenever `f` separates the two states; no single import selected.
5. WS5: `verdict` a FUNCTION of the WS1/WS3/WS4 flags (not WS2, not hand-set); the equalities `rfl`/`decide`; the audit clauses actual propositions.

## Audit checks (a–e), as mechanical instructions

- (a) NO CARDINAL CEILING. Confirm the ONLY ontological bound is finite out-attention: `outDest`'s neighborhoods are finite (`< ℵ₀`) for every `κ`, and every `κ` that appears (in `symDest`, `knowLift`) is `mk X` (ambient carrier size, `hcar`), NEVER a chosen ceiling on attention. FLAG if any bound unfolds to "attention ranges over a κ-bounded set."
- (b) THE ASYMMETRY IS NOT A LABEL. Confirm `ws3_passive_constitution` names a genuine reader: the directed/labelled structure (`knowLift`) does work the plain (`symDest`) does not, and `attends`/`attendedBy` are load-bearing in the STATEMENT (stripping them changes it). FLAG if the direction is a free tag no bisimulation reads.
- (c) DIRECTION IS NON-RECOVERABLE. Confirm `ws3_direction_not_recoverable` is a proof obligation discharged, not a hypothesis assumed.
- (d) COLLAPSE INHERITED, NOT RELITIGATED. Confirm `ws2_collapse_inherited` is the imported engine applied (not re-proved), and that `verdict` does NOT take the collapse as an argument (no verdict hinges on it).
- (e) IMPORT QUANTIFIED, NOT NAMED. Confirm the import is a universally-bound `f`/`Q`, no single import privileged, and (design-level) no signature names a proof term "love"/"import"/"God"/"choice"/"self"/"other"/"knowing"/"attention" as content.

## The strip test (run on each payoff)

Delete the structural word ("attention," "knowing," "relating," "active," "passive," "gaze," "import," "ground," "collapse," "verdict") from each signature and check the statement still goes through as a bare `Finset`-section, finiteness, `Subsingleton`, `Recoverable`, `IsBisim`/`IsBisimL`, `AttentionDistinguishes`, or `Outcome`-computation fact. A payoff that NEEDS the deleted word, or survives as something other than its named bare fact, is flagged. What SHOULD survive: WS3's asymmetry → "direction is not recoverable from the symmetric reduct, by `Recoverable`, a directed reader load-bearing"; WS2's collapse → "atomless plain-bisimilar states are equal, by the imported engine."

## Names-not-terms forbidden list

No definition, theorem name, or bound content is "love," "loved," "import," "God," "choice," "self," "other," "knowing," or "attention" AS A PROOF TERM / CONTENT. Neutral carrier names (`attends`, `knowLift`, `sym`, `knows`, `impLift`) are fine; the concept-words may appear in docstring prose only. At the design stage, confirm no SIGNATURE introduces such a named term.

## Your task

For EACH signature/definition above: (1) is the design coherent (well-typed against the imported P1 definitions) and non-vacuous (the claim is not trivially true or unsatisfiable)? (2) does it meet its success criterion? (3) does it pass the strip test and the names check? (4) run the five audit checks. Grade each finding.

## Grading rubric

- **SERIOUS:** the verdict rests on it; the asymmetry of knowing is a bare label; a cardinal ceiling is readmitted; the collapse is relitigated or a verdict hinges on it; the import is named or selected; direction is assumed rather than proved; a name is a proof term; or an undisclosed narrowing between the success criteria and the signatures.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed statement, an assumed-and-returned hypothesis, an over-strong name, a vacuous witness).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings with stable IDs `Cn-Sm`, each with grade, exact location (file + signature name), and the defect. If you find nothing at a grade, say so. Also state explicitly whether any signature is UNSATISFIABLE as written (e.g. a `∀`-claim with a counterexample, or a witness that does not exist).
