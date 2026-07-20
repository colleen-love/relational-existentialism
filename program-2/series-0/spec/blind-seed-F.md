# Blind seed — Phase F (code review)

You are reviewing a built Lean 4 / Mathlib development for whether the CODE proves the claimed signatures. Judge ONLY against the mathematical contracts below. The development is already built (`lake build P2S0` succeeds); your job is to confirm the proofs discharge the claims honestly, run the strip test, run the names-not-terms grep, and confirm the audit checks.

## Files you may read

- THIS file (`spec/blind-seed-F.md`).
- The built Lean sources under review: `program-2/series-0/formal/P2S0.lean` and `program-2/series-0/formal/P2S0/ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean`, `AxiomCheck.lean`.
- The imported prior art: `program-2/formal/P1/Core.lean` and `program-2/formal/P1/Reader.lean` (built, sorry-free, axiom-clean). These define `PkObj`, `IsReify`, `IsBisim`, `IsBisimL`, `plainOf`, `Recoverable`, `ws1_atomless_bisim`, `ws2_import_theorem_static`, `toPk`, `AttentionDistinguishes`, `mk_singleton_lt`, etc.

DO NOT READ: `charter.md`, `charter-status.md`, `spec/README.md` (the design index), `spec/ws1-design.md`…`ws5-design.md` (the design docs), any `summary*.md`, or any file with motivating/positioning prose. The Lean sources under review contain docstrings; those docstrings' interpretive words (e.g. "the knot," "you are loved," "the gaze") are PROSE and are exactly what the names-not-terms grep guards — judge the code, not the prose. If you accidentally open a forbidden file, say so and stop (your pass is discarded).

## What to check, per theorem: does the CODE prove the SIGNATURE?

For each headline below, confirm the Lean proof actually discharges the stated type with no `sorry`, no smuggled hypothesis, no vacuity, and no name doing a proof's work.

WS1 (`ws1.lean`):
- `FinReify attends reify := ∀ s : Finset X, attends (reify s) = s`.
- `ws1_finreify_injective : FinReify attends reify → Function.Injective reify`.
- `ws1_reification_exists : ∃ (X : Type) (attends : X → Finset X) (reify : Finset X → X), FinReify attends reify ∧ Function.Injective reify`. CHECK: is the witness genuinely constructed (not vacuous)? Is it a real section (ideally bijective)?
- `ws1_bound_is_finite_attention : ∀ x, Cardinal.mk ↥((outDest hinf attends x).1) < Cardinal.aleph0`. CHECK audit (a): is the bound `< ℵ₀` (finite), uniform in `κ`, with `κ` never the bound?
- `finReifyStep`, `finTowerN`, `ws1_tower_monotone`.

WS2 (`ws2.lean`):
- `ws2_collapse_inherited … : Subsingleton X`. CHECK audit (d): is the proof term the imported `ws2_import_theorem_static` applied to `symDest` (NOT re-derived)? Is `hcar : mk X < κ` used only for well-definedness of the symmetric reduct, not as an ontological ceiling?

WS3 (`ws3.lean`) — witness `a := true`, `b := false : Bool`, `attendsD x := if x = a then {b} else ∅`, `knowLiftD`:
- `ws3_direction_not_recoverable : ¬ Recoverable (knowLiftD hinf)`. CHECK audit (c): is non-recoverability DISCHARGED (a plain bisimulation relating `a`,`b` that is not a label-bisimulation), not assumed?
- `ws3_passive_constitution : (a ∈ attendedBy attendsD b ∧ attendsD b = ∅) ∧ AttentionDistinguishes (knowLiftD hinf) a b`. CHECK audit (b) — THE CENTRAL RISK: is the asymmetry LOAD-BEARING (the directed/labelled `knowLiftD` does work the plain `plainOf` reduct cannot), or a bare tag? Confirm `plainOf (knowLiftD hinf)` really is the symmetric relating (`a ↦ {b}`, `b ↦ {a}`), that `a`,`b` are plain-bisimilar yet label-separated, and that `attends`/`attendedBy` are load-bearing in the statement (stripping them changes it).
- `ws3_active_passive_distinct : (attendsD a ≠ attendsD b) ∧ (plain-bisimilar) ∧ (¬ label-bisimilar)`.

WS4 (`ws4.lean`) — `impLift hinf (f : Bool → Q) i := pkSingle hinf (f i, i)`:
- `ws4_import_breaks_baseline : ∀ {Q} (f : Bool → Q), f true ≠ f false → (∃ R, IsBisim (plainOf (impLift hinf f)) R ∧ R true false) ∧ (¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false)`. CHECK audit (e): genuinely `∀ Q, f` with none selected?
- `ws4_import_quantified : (∀ {Q} (f : Bool → Q), plainOf (impLift hinf f) = plainOf (impLift hinf (fun _ => true))) ∧ ¬ Recoverable (impLift hinf id)`.

WS5 (`ws5.lean`):
- `Outcome`, `verdict (reif asym imp : Bool) : Outcome`, `ws5_verdict_eq : verdict true true true = groundEstablished`. CHECK: is `verdict` a genuine FUNCTION of the flags (not hand-set)? Is the collapse (WS2) NOT an argument (audit d)?
- `ws5_verdict_not_obstructed`, `ws5_verdict_not_partial` (the function discriminates).
- `ws5_flags_justified` (the three flags earned by WS1/WS3/WS4 payoffs).
- `ws5_audit_no_ceiling`, `ws5_audit_asymmetry_not_label`, `ws5_audit_direction_free`, `ws5_audit_collapse_inherited` (`rfl` identity with the imported engine), `ws5_audit_import_quantified`.

## Success criteria (mechanical, motivation removed)

1. WS1: a real finite section, exhibited non-vacuously; a finiteness bound `< ℵ₀` uniform in `κ`.
2. WS2: `Subsingleton X` via the imported engine, not re-derived.
3. WS3: (c) `¬ Recoverable` a proof term; (b) a plain-bisimilar-yet-label-separated pair with `attends`/`attendedBy` load-bearing; the two modes distinct.
4. WS4: a labelled lift, `∀ Q, f`, plain-bisimilar yet label-separated when `f` separates the states; none selected.
5. WS5: `verdict` a function of the WS1/WS3/WS4 flags (not WS2, not hand-set); the equalities `rfl`/`decide`; the audit clauses proved.

## Audit checks (a–e), as mechanical instructions

- (a) NO CARDINAL CEILING. `outDest`'s neighborhoods `< ℵ₀` for every `κ`; every `κ` (in `symDest`, `knowLiftD`, `impLift`) is `mk X` / ambient (`hcar`), never a chosen ceiling on attention.
- (b) THE ASYMMETRY IS NOT A LABEL. `ws3_passive_constitution` names a genuine reader; `knowLiftD` does work `plainOf` cannot; `attends`/`attendedBy` load-bearing in the statement.
- (c) DIRECTION IS NON-RECOVERABLE. `ws3_direction_not_recoverable` discharged, not assumed.
- (d) COLLAPSE INHERITED, NOT RELITIGATED. `ws2_collapse_inherited` is the imported engine applied; `verdict` does not take the collapse as an argument.
- (e) IMPORT QUANTIFIED, NOT NAMED. The import is a universally-bound `f`/`Q`; no proof term named "love"/"import"/"God"/"choice"/"self"/"other"/"knowing"/"attention" as content.

## The strip test (run on each payoff)

Delete the structural word ("attention," "knowing," "relating," "active," "passive," "gaze," "import," "ground," "collapse," "verdict") and confirm the statement still goes through as a bare `Finset`-section, finiteness, `Subsingleton`, `Recoverable`, `IsBisim`/`IsBisimL`, `AttentionDistinguishes`, or `Outcome`-computation fact. What SHOULD survive: WS3 → "direction is not recoverable from the symmetric reduct, by `Recoverable`, a directed reader load-bearing"; WS2 → "atomless plain-bisimilar states are equal, by the imported engine."

## Names-not-terms grep (run it)

Run: `grep -rniE "\b(love|loved|import|god|choice|self|other|knowing|attention)\b" program-2/series-0/formal`. Confirm EVERY hit is docstring/comment prose or the Lean `import` keyword — NO definition, theorem name, or bound content is named for the interpretive content. Neutral names (`attends`, `knowLift`/`knowLiftD`, `sym`, `knows`, `impLift`, `attendedBy`) are fine.

## Also confirm

- The build is sorry-free (grep `sorry` in `formal/`; hits must be prose only).
- The axiom record (`AxiomCheck.lean`) shows every headline on the standard three (`propext`/`Classical.choice`/`Quot.sound`) with no `sorryAx`, no custom `axiom` (the `ws5_verdict_*` may depend on none).

## Grading rubric

- **SERIOUS:** a verdict rests on it; the asymmetry is a bare label; a cardinal ceiling is readmitted; the collapse is relitigated or a verdict hinges on it; the import is named or selected; direction is assumed; a `sorry` or custom axiom; a name is a proof term; an undisclosed narrowing between signature and code.
- **REAL:** a genuine gap correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name, a vacuous witness).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

Return a structured list of findings with stable IDs `Fn-Sm`, each with grade, exact location (file + line/signature), and defect. If a grade level has no findings, say so. State explicitly whether any theorem's proof FAILS to discharge its signature (a `sorry`, a vacuity, a smuggled hypothesis, or a name-as-term).
