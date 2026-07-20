# Blind seed — Phase C (design review)

You are reviewing a Lean 4 formal DESIGN (typed signatures, not yet built). Judge the design ONLY against the
contracts below. This seed is self-contained; do not seek motivating prose.

---

## 0. The ambient machinery (given, from a prior verified layer; treat as sound)

A coalgebra is `dest : X → PkObj κ X` (κ-bounded powerset functor, `κ` infinite). Relevant given objects:

- `IsBisim dest R` — a plain bisimulation. `plainOf destL` — the label-forgetting reduct of a labelled coalgebra
  `destL : X → LkObj κ Q X` (`LkObj κ Q X := PkObj κ (Q × X)`). `IsBisimL destL R` — a label-respecting bisimulation.
- `Recoverable destL := ∀ R, IsBisim (plainOf destL) R → IsBisimL destL R` (the label is forced by the plain
  relating). `ws4_recoverable_not_import : Recoverable destL → (∃ R, IsBisim (plainOf destL) R ∧ R x y) → (∃ R,
  IsBisimL destL R ∧ R x y)`.
- `ws1_atomless_bisim : SHNE dest x → SHNE dest y → ∃ R, IsBisim dest R ∧ R x y` (the collapse engine: any two
  states with hereditarily-nonempty successors are plain-bisimilar).
- `PkMap`, `SHNE`, `SReaches` as usual. `rankLift dest rank`, `FiniteAttention`, `AttentionDistinguishes`,
  `RealFor` given.

The carrier under review, `RCar := Fin 5`, has two distinguished loci `slf`, `oth` (`slf ≠ oth`) with a coalgebra
`outDest hinf attendsR : RCar → PkObj κ RCar`. Given facts about this carrier (from the prior layer, treat as
proven):

- Every node is `SHNE`: `ws1_rcar_SHNE hinf x : SHNE (outDest hinf attendsR) x`. Hence ANY two nodes are
  plain-bisimilar (via `ws1_atomless_bisim`); in particular `slf`, `oth` are plain-bisimilar.
- `slf`, `oth` are label-separated over `rankLift (outDest hinf attendsR) rankR` and that separation is
  `¬ Recoverable` (an import): `ws2_other_non_recoverable`, and `oth` is `RealFor` a named finite attention
  `slfReader`: `ws2_other_reader_wise`.

## 1. The definitions under review

```lean
structure Valuation (X Or : Type) where
  val   : X → Or
  raise : X → X → Or → Or

def Converges₂ {X Or : Type} (c : Valuation X Or) (x y : X) : Prop := c.raise x y (c.val x) = c.val y
def Faithful₂ {X Or : Type} (c : Valuation X Or) : Prop := ∀ x y : X, c.raise x y = id
def InSight {X Or : Type} (dest : X → PkObj κ X) (c : Valuation X Or) : Prop :=
  ∀ x y : X, (∃ R, IsBisim dest R ∧ R x y) → c.val x = c.val y
noncomputable def valLift {X Or : Type} (dest : X → PkObj κ X) (f : X → Or) : X → LkObj κ Or X :=
  fun x => PkMap κ (fun z => (f x, z)) (dest x)

def cUnif : Valuation RCar (ULift.{0} Bool) := ⟨fun _ => ⟨true⟩, fun _ _ o => o⟩
def cDiss : Valuation RCar (ULift.{0} Bool) := ⟨fun z => if z = slf then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩

inductive Outcome | shapeDrawn | convergenceDecided | disconnected | partial'
def verdict (typed forcedInSight dissentImport forkBoth : Bool) : Outcome :=
  if !typed then Outcome.disconnected
  else if !(forcedInSight && dissentImport) then Outcome.partial'
  else if forkBoth then Outcome.shapeDrawn
  else Outcome.convergenceDecided
```

## 2. The theorem signatures under review

```lean
theorem faithful_converges_iff (c : Valuation X Or) (hf : Faithful₂ c) (x y : X) :
    Converges₂ c x y ↔ c.val x = c.val y
theorem ws1_converges_typed (hinf) : ∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ Converges₂ c slf oth
theorem ws1_no_orientation_evaluated (hinf) :
    ∃ c₁ c₂ : Valuation RCar (ULift Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth
theorem plainOf_valLift (dest) (f) : plainOf (valLift dest f) = dest
theorem valLift_not_recoverable (dest) (f) (x y) (hx : SHNE dest x) (hy : SHNE dest y) (hne : f x ≠ f y) :
    ¬ Recoverable (valLift dest f)
theorem ws2_converges_decided_in_sight (hinf) :
    ∀ (Or) (c : Valuation RCar Or), Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth
theorem ws2_insight_inhabited (hinf) :
    ∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c
theorem ws2_sight_is_uniform (hinf) :
    ∀ (Or) (c : Valuation RCar Or), InSight (outDest hinf attendsR) c → ∀ x y : RCar, c.val x = c.val y
theorem ws3_dissent_is_import (hinf) :
    ∀ (Or) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
    ¬ Recoverable (valLift (outDest hinf attendsR) c.val)
theorem ws4_insight_proper (hinf) :
    (∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ InSight (outDest hinf attendsR) c)
  ∧ (∃ c : Valuation RCar (ULift Bool), Faithful₂ c ∧ ¬ InSight (outDest hinf attendsR) c)
theorem ws4_two_zone_convergence (hinf) :
    (∃ c₁ c₂ : Valuation RCar (ULift Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth)
  ∧ (∀ (Or) (c : Valuation RCar Or), Faithful₂ c → InSight (outDest hinf attendsR) c → Converges₂ c slf oth)
  ∧ (∀ (Or) (c : Valuation RCar Or), Faithful₂ c → ¬ Converges₂ c slf oth →
        ¬ Recoverable (valLift (outDest hinf attendsR) c.val))
theorem ws5_verdict_eq : verdict true true true true = Outcome.shapeDrawn
theorem ws5_verdict_discriminates :
    verdict true true true false = Outcome.convergenceDecided ∧ verdict false true true true = Outcome.disconnected
  ∧ verdict true false true true = Outcome.partial' ∧ verdict true true false true = Outcome.partial'
theorem ws5_flags_justified (hinf) : (ws1_no_orientation_evaluated) ∧ (ws2_converges_decided_in_sight)
  ∧ (ws3_dissent_is_import) ∧ (ws4_insight_proper)          -- the four headline props conjoined
theorem ws5_audit_faces_are_readers (hinf) :
    RealFor (rankLift (outDest hinf attendsR) rankR) (slfReader hinf) oth
  ∧ ¬ Recoverable (rankLift (outDest hinf attendsR) rankR)
-- ws5_audit_direction_open : True   and   ws5_audit_names_not_terms : True   (grep-certified placeholders)
```

## 3. Success criteria (restated, mechanical)

1. `Converges₂` is a genuine relation between two valuations, quantified over all valuations `c` and spaces `Or`;
   no canonical valuation is a proof term (witnesses only in existentials). It is non-vacuous (some `c` converge)
   and non-trivial (some `c` do not) at `(slf, oth)`.
2. Over a NON-VACUOUS, GENUINELY CONSTRAINED sub-class (`InSight`), `Converges₂` at `(slf, oth)` is FORCED.
3. Every valuation FAILING `Converges₂` at `(slf, oth)` (in the faithful class) yields a `¬ Recoverable` lift.
4. The fork reaches BOTH values on witnessed valuations at `(slf, oth)`, the class is structurally constrained
   (in-sight ⊊ faithful, both inhabited), and the verdict is a function reaching more than one value.
5. The verdict computes `shapeDrawn` from the earned flags; the direction (whether `slf`, `oth` cohere) is never
   decided by any theorem/definition.

## 4. Audit checks (mechanical, a-e)

- **(a) NO VALUATION EVALUATED.** Is any proof term a canonical `val`/valuation that discharges a `∀`-obligation?
  Or do concrete valuations (`cUnif`, `cDiss`) appear ONLY inside existentials? Does `ws1_no_orientation_evaluated`
  genuinely show two-sided freedom?
- **(b) THE DIRECTION IS NEVER DECIDED.** Does any signature state `∀ c, Converges₂ c slf oth` (unconditionally) or
  `∀ c, ¬ Converges₂ c slf oth`, i.e. decide that `slf`, `oth` DO or DO NOT cohere? (The in-sight forcing is
  CONDITIONAL on `InSight`, a proper sub-class — that is allowed. An UNconditional decision is the sin.)
- **(c) THE FORK IS GENUINE — PRESS HARDEST HERE.** Is the fork decided by the parameter type alone (a tautology
  that would land the same on EVERY coalgebra, ignoring `slf`/`oth`/`outDest`)? Or is it load-bearing on the
  structure? Specifically: (i) does `ws2_converges_decided_in_sight` genuinely use `slf`, `oth` plain-bisimilar
  (a fact about `outDest attendsR`), so it would FAIL on a structure where they are not bisimilar? (ii) is the
  in-sight class a PROPER, INHABITED sub-class of faithful (`ws4_insight_proper`), so restricting to it is a real
  constraint? (iii) are both zones witnessed on the SAME pair? A `Faithful₂`/`InSight` that any valuation
  satisfies, or a fork constructible with `dest` phantom, is the tautology (the prior-art failure this design
  must avoid).
- **(d) DISSENT IS AN IMPORT.** Is `ws3_dissent_is_import` a proof term reducing to the collapse engine +
  `ws4_recoverable_not_import` (the prior import theorem), not an assumed hypothesis?
- **(e) NAMES-NOT-TERMS.** Do any identifiers embed, as CONTENT, the words: `love`, `loved`, `coherence`,
  `convergence`, `compass`, `orientation`, `self`, `other`, `god`, `choice`, `subjectivity`? (Note: `Converges₂`
  and `converges` do NOT contain the full word `convergence`; `val`/`Valuation` do NOT contain `orientation`;
  these are allowed. Flag only a full-word content-name.)

## 5. The strip test (run on each payoff)

Delete the structural words ("convergence", "coherence", "orientation", "in-sight", "dissent") and check the
statement still goes through as a bare `Recoverable`/`¬ Recoverable`, `IsBisim`, or equality/order fact:
- WS2 forcing should strip to "a valuation agreeing on plain-bisimilar states agrees on `slf`, `oth`."
- WS3 dissent should strip to "`val slf ≠ val oth` on the plain-bisimilar `slf`, `oth` ⇒ the `val`-lift is
  `¬ Recoverable`."
- WS4 shape-drawn should strip to "a discriminating function over a constrained class reaching two values, both
  witnessed."
If a payoff needs its structural word to be non-trivial, that is a strip-test failure (flag it).

## 6. Grading rubric

- **SERIOUS:** the verdict rests on it; the fork is a tautology of an unconstrained valuation type (audit (c));
  the direction is decided (audit (b)); a valuation is evaluated (audit (a)); the faces collapse to labels / the
  valuation goes inert; a name is a proof term (audit (e)); an undisclosed narrowing.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed signature, an assumed-and-returned
  hypothesis, an over-strong name, a bare conjunction dressed as an interaction).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, over-hypothesis, or naming nit.

## 7. Your output

For each signature: is the design coherent and non-vacuous, and does it meet the criterion it targets? Run the
audit (a)-(e), pressing hardest on (c). Run the strip test. Return a structured list of findings with stable IDs
`Cn-Sm`, each with grade (SERIOUS/REAL/COSMETIC), exact location (theorem/def name), and the precise defect.
State explicitly which files you read.
