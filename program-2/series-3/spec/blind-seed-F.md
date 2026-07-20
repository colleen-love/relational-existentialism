# Blind seed — Phase F (code review)

You are reviewing BUILT Lean 4 code. Judge whether the CODE proves the claimed signatures, ONLY against the
contracts below. The code compiles (sorry-free, axiom-clean on `propext`/`Classical.choice`/`Quot.sound` or
fewer); your job is to judge whether the statements say what they claim, whether the fork is genuine, and whether
the discipline holds — not to re-run the compiler.

## 0. The ambient machinery (given, from prior VERIFIED layers; treat as sound)

Coalgebra `dest : X → PkObj κ X` (κ-bounded powerset functor). Given (you MAY confirm these in the imported
prior-layer sources `program-2/formal/P1/Core.lean`, `program-2/formal/P1/Reader.lean`,
`program-2/series-2/formal/P2S2/*.lean`; treat them as sound):

- `IsBisim dest R`, `IsBisimL destL R`, `plainOf destL`, `LkObj κ Q X := PkObj κ (Q × X)`, `PkMap`.
- `Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R`.
- `ws4_recoverable_not_import : Recoverable destL → (∃ R, IsBisim (plainOf destL) R ∧ R x y) → (∃ R, IsBisimL destL R ∧ R x y)`.
- `ws1_atomless_bisim : SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y` (the collapse engine, Series 07).
- Carrier `RCar := Fin 5`, loci `slf`, `oth` (`slf ≠ oth`), coalgebra `outDest hinf attendsR`; every node is
  `SHNE` (`ws1_rcar_SHNE`), so any two nodes (in particular `slf`, `oth`) are plain-bisimilar.
- `ws2_other_reader_wise : RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth` and
  `ws2_other_non_recoverable : ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)` (prior layer).

## 1. The files under review

`program-2/series-3/formal/P2S3/ws1.lean`, `ws2.lean`, `ws3.lean`, `ws4.lean`, `ws5.lean` (+ aggregator
`P2S3.lean`, `AxiomCheck.lean`). Do NOT read S3's `charter.md`, `charter-status.md`, `summary*.md`,
`spec/README.md`, `spec/*-design.md`, or `protocol.md` — judge the code only against this seed. If you open any of
those, STOP and say so; I will discard the pass.

## 2. The claims the code must prove (final names)

```lean
structure Valuation (X Or : Type) where  val : X → Or ;  raise : X → X → Or → Or
def Converges₂ (c : Valuation X Or) (x y : X) : Prop := c.raise x y (c.val x) = c.val y
def Faithful₂  (c : Valuation X Or) : Prop := ∀ x y, c.raise x y = id
def InSight (dest : X → PkObj κ X) (c : Valuation X Or) : Prop :=
  ∀ x y, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y
noncomputable def valLift (dest) (f : X → Or) : X → LkObj κ Or X := fun x => PkMap κ (fun z => (f x, z)) (dest x)

theorem faithful_converges_iff (c) (hf : Faithful₂ c) (x y) : Converges₂ c x y ↔ c.val x = c.val y
theorem ws1_converges_typed : ∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ Converges₂ c slf oth
theorem ws1_two_sided_free :  ∃ c₁ c₂ : Valuation RCar (ULift Bool),
    Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth
theorem plainOf_valLift (dest) (f) : plainOf (valLift dest f) = dest
theorem valLift_not_recoverable (dest) (f) (x y) (hx : SHNE dest x) (hy : SHNE dest y) (hne : f x ≠ f y) :
    ¬ Recoverable (valLift dest f)
theorem ws2_converges_decided_in_sight (hinf) : ∀ (Or) (c : Valuation RCar Or),
    Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth
theorem ws2_insight_inhabited (hinf) : ∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c
theorem ws2_sight_is_uniform (hinf) : ∀ (Or) (c : Valuation RCar Or),
    InSight (outDest hinf attendsR) c → ∀ x y : RCar, c.val x = c.val y
theorem ws3_dissent_is_import (hinf) : ∀ (Or) (c : Valuation RCar Or),
    Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val)
theorem ws4_insight_proper (hinf) :
    (∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
  ∧ (∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c)
theorem ws4_two_zone (hinf) :
    (∃ c₁ c₂ : Valuation RCar (ULift Bool), Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or) (c : Valuation RCar Or), Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth → ¬ Recoverable (valLift (outDest hinf attendsR) c.val))
inductive Outcome | shapeDrawn | forcedFull | disconnected | partial'
def verdict (typed forcedInSight dissentImport forkBoth : Bool) : Outcome := ...
theorem ws5_verdict_eq : verdict true true true true = Outcome.shapeDrawn
theorem ws5_verdict_discriminates :
    verdict true true true false = Outcome.forcedFull ∧ verdict false true true true = Outcome.disconnected
  ∧ verdict true false true true = Outcome.partial' ∧ verdict true true false true = Outcome.partial'
theorem ws5_flags_justified (hinf) : <ws1_two_sided_free ∧ ws2 forcing ∧ ws3 import ∧ ws4_insight_proper, written in full>
theorem ws5_audit_no_evaluation : <= ws1_two_sided_free>
theorem ws5_audit_fork_genuine (hinf) : <= ws4_two_zone ∧ ws4_insight_proper>
theorem ws5_audit_dissent_import (hinf) : <= ws3_dissent_is_import>
theorem ws5_audit_faces_are_readers (hinf) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
theorem ws5_audit_direction_open : True    -- grep-certified placeholder
theorem ws5_audit_names_not_terms : True   -- grep-certified placeholder
```

## 3. Success criteria (mechanical)

1. `Converges₂` genuine, quantified over all `c`/`Or`, no canonical valuation as a proof term (witnesses only in
   existentials); non-vacuous AND non-trivial at `(slf, oth)`.
2. Over the non-vacuous, genuinely constrained `InSight` sub-class, `Converges₂` at `(slf, oth)` is FORCED.
3. Every faithful valuation FAILING `Converges₂` at `(slf, oth)` yields a `¬ Recoverable` lift, resting on the
   collapse engine (Series 07), not an assumed hypothesis.
4. The fork reaches BOTH values on witnessed valuations at `(slf, oth)`; `InSight ⊊ Faithful₂` (proper, both
   inhabited); the verdict reaches more than one value.
5. The verdict computes `shapeDrawn` from earned flags; the direction (whether `slf`, `oth` cohere) is never
   decided by any theorem/definition.

## 4. Audit checks (a-e), mechanical

- **(a) NO VALUATION EVALUATED.** Does any `∀`-obligation get discharged by a canonical valuation? Do `cUnif`,
  `cDiss` appear only inside existentials? Does `ws1_two_sided_free` genuinely establish two-sided freedom?
- **(b) DIRECTION NEVER DECIDED — check carefully.** Does any theorem state `∀ c, Converges₂ c slf oth` (or its
  negation) UNCONDITIONALLY? (Forcing conditional on `InSight`/`Faithful₂` is allowed; an unconditional coherence
  decision is the sin.) Do the witnesses (`cUnif` converges, `cDiss` fails) sit inside existentials, deciding
  nothing globally?
- **(c) FORK GENUINE — PRESS HARDEST.** Is the fork a tautology of the `Valuation` type (would land the same on
  every coalgebra, `dest` phantom)? Verify: (i) `ws2_converges_decided_in_sight`'s proof genuinely uses `slf`,
  `oth` plain-bisimilar under `outDest attendsR` (so it would fail on a non-bisimilar carrier); (ii)
  `ws4_insight_proper` genuinely shows `InSight ⊊ Faithful₂` (the `cDiss` witness is faithful yet NOT in-sight);
  (iii) both zones witnessed on the SAME pair. Does `InSight` reference `dest` (not phantom)?
- **(d) DISSENT IS AN IMPORT.** Does `ws3_dissent_is_import` reduce through `valLift_not_recoverable` to
  `ws1_atomless_bisim` + `ws4_recoverable_not_import`, not an assumed `¬ Recoverable`?
- **(e) NAMES-NOT-TERMS.** Grep the forbidden full words in `formal/`:
  `love|loved|coherence|convergence|compass|orientation|self|other|god|choice|subjectivity`. Hits MUST be
  docstring/comment prose only, NEVER an identifier (def/theorem/constructor/field). Note `Converges₂`/`converges`
  ≠ `convergence`; `val`/`Valuation` ≠ `orientation`; `slf`/`oth` ≠ `self`/`other`; these are allowed.

## 5. Strip test (run on each payoff)

Delete "convergence"/"coherence"/"orientation"/"in-sight"/"dissent" and check the statement still goes through as
a bare `Recoverable`/`¬ Recoverable`/`IsBisim`/equality fact:
- WS2 forcing → "a valuation agreeing on plain-bisimilar states agrees on `slf`, `oth`."
- WS3 dissent → "`val slf ≠ val oth` on plain-bisimilar `slf`, `oth` ⇒ `val`-lift `¬ Recoverable`."
- WS4 → "a discriminating function over a constrained class reaching two values, both witnessed."
If a payoff needs its structural word to be non-trivial, flag it.

## 6. Grading rubric

- **SERIOUS:** the verdict rests on it; the fork is a tautology of an unconstrained valuation type (audit c);
  the direction is decided (audit b); a valuation is evaluated (audit a); a name is a proof term (audit e); the
  faces collapse to labels / the valuation goes inert; an overclaimed signature the code does not prove; an
  assumed-and-returned hypothesis dressed as a result.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an over-strong name, a bare
  conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

## 7. Your output

For each theorem: does the code prove the claimed statement, and does it meet its criterion? Run the audit
(a)-(e), pressing hardest on (c) and (b). Run the strip test. Run the names grep. Return a structured list of
findings with stable IDs `Fn-Sm`, each with grade, exact location, and the precise defect (with a suggested
correction). If no issue at a grade, say so. End with a one-line verdict on whether the built code lands a
genuine, non-tautological two-zone fork with the direction never decided. State which files you read.
