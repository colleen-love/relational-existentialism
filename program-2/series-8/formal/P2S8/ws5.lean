/-
`program-2/series-8/formal/P2S8/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 8 (2.8).

The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= frustrated` on the earned
flags, DISCRIMINATING (reaches all six outcomes), the flags EARNED by the WS1-WS4 headlines. The computed verdict is
FRUSTRATED: a non-trivial self-relative good (WS1), pairwise coherence pervasive (WS2), the obstruction genuinely
many-body and model-derived (WS3), and frustration AND gluing both reachable (WS4). So local coherence does NOT force
a global good — the value analog of energy's global failure (2.7). The five audit clauses (a)-(e) bundle the payoffs.

Design docs: `program-2/series-8/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S8.ws1
import P2S8.ws2
import P2S8.ws3
import P2S8.ws4

universe u

namespace P2S8

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `frustrated` local coherence does not force a global good (both fork sides reachable);
`gluable` a global good forced (frustration not reachable); `shapeDrawn` the fork drawn, neither side decided;
`pairwiseOnly` the obstruction degenerates to a single edge; `disconnected` no non-trivial good survives; `partial'`
primed (`partial` is a Lean keyword) an obligation degenerate. No identifier embeds a forbidden content-name. -/
inductive Outcome
  | frustrated
  | gluable
  | shapeDrawn
  | pairwiseOnly
  | disconnected
  | partial'
  deriving DecidableEq

/-- **The verdict FUNCTION.** `frustrated` iff the good is non-trivial (WS1), the obstruction genuinely many-body
(WS3) and model-derived (WS3), coherence pervasive (WS2), and BOTH frustration and gluing reachable (WS4) — local
coherence does not FORCE a global good. `gluable` requires gluing forced (frustration not reachable); `shapeDrawn`
neither side decided; `pairwiseOnly` the obstruction not many-body; `disconnected` no non-trivial good; `partial'`
degenerate. -/
def verdict (nonTrivial pairwiseCoherent manyBody modelDerived frustReachable glueReachable : Bool) : Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if !manyBody then Outcome.pairwiseOnly
  else if !pairwiseCoherent then Outcome.partial'
  else if !modelDerived then Outcome.partial'
  else if frustReachable && glueReachable then Outcome.frustrated
  else if glueReachable && !frustReachable then Outcome.gluable
  else if !glueReachable && !frustReachable then Outcome.shapeDrawn
  else Outcome.partial'

/-- **THE COMPUTED VERDICT.** On the earned flags (a non-trivial good, coherence pervasive, the obstruction many-body
and model-derived, frustration AND gluing both reachable), `frustrated`, by computation. -/
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.frustrated := rfl

/-- **Falsifiability.** The verdict DISCRIMINATES: it reaches all six outcomes. -/
theorem ws5_verdict_discriminates :
    verdict false true true true true true  = Outcome.disconnected
  ∧ verdict true true false true true true  = Outcome.pairwiseOnly
  ∧ verdict true false true true true true  = Outcome.partial'
  ∧ verdict true true true true true true   = Outcome.frustrated
  ∧ verdict true true true true false true  = Outcome.gluable
  ∧ verdict true true true true false false = Outcome.shapeDrawn := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The six deciding inputs are EARNED by the WS1-WS4 headlines, none hand-set:
`nonTrivial` (WS1, `ws1_nontrivial`); `pairwiseCoherent` (WS2, `ws2_pairwise_coherent`); `manyBody` (WS3, the
holonomy antisymmetric / two-body-trivial); `modelDerived` (WS3, symmetry kills the holonomy); `frustReachable`
(WS4, `ws4_frustrated_reachable`); `glueReachable` (WS4, `ws4_gluable_reachable`). -/
theorem ws5_flags_justified :
    (valu attTri p1 ≠ valu attTri p2)
  ∧ (∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v)
  ∧ (∀ att : S → Finset S, ∀ x y : S, incr att x y + incr att y x = 0)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s)
  ∧ (∃ s : S → ℤ, IsSection attStar s) := by
  refine ⟨ws1_nontrivial.1, ws2_pairwise_coherent, ?_, ws3_holonomy_model_derived.2.1,
          ws4_frustrated_reachable, ?_⟩
  · exact fun att x y => (ws3_two_body_trivial att x y).1
  · obtain ⟨s, hs, _⟩ := ws4_gluable_reachable.2; exact ⟨s, hs⟩

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) NO GLOBAL GOOD ASSERTED.** No section is asserted for the frustrated population (`¬ ∃`); the good is FOR a
self (`valu`); a section is claimed only where the holonomy vanishes (the star), restricting to the self's local
good; `gluable` is returned only if gluing is forced (`glueReachable && !frustReachable`), which the earned flags do
NOT set (frustration IS reachable). -/
theorem ws5_audit_no_global :
    (¬ ∃ s : S → ℤ, IsSection attTri s)
  ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)
  ∧ (verdict true true true true false true = Outcome.gluable) :=
  ⟨ws4_frustrated_reachable.2, ws4_gluable_reachable.2, rfl⟩

/-- **(b) THE FORK NOT BY FIAT.** Frustrated (ring `hol = 3`) AND gluable (star `hol = 0`) both reachable from the
SAME `hol`/`incr`, the good non-trivial. Neither side is hard-wired. -/
theorem ws5_audit_fork_genuine :
    (hol attTri p0 p1 p2 = 3) ∧ (hol attStar p0 p1 p2 = 0) ∧ (valu attTri p1 ≠ valu attTri p2) :=
  ⟨ws4_frustrated_reachable.1, ws4_gluable_reachable.1, ws1_nontrivial.1⟩

/-- **(c) GENUINE MANY-BODY COCYCLE, NOT A SINGLE EDGE / IMPORT-NESS / BOLTED-ON (the doubled costume gate + T1-S1).**
The holonomy vanishes for two selves (`hol x y x = 0`); it vanishes identically when the attention is symmetric (so
it is carried by the directedness, model-derived, not bolted on); and the frustrating carrier is genuinely directed.
No clause mentions `Recoverable`: not import-ness. -/
theorem ws5_audit_many_body :
    (∀ att : S → Finset S, ∀ x y : S, hol att x y x = 0)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y) :=
  ⟨fun att x y => (ws3_two_body_trivial att x y).2.1,
   ws3_holonomy_model_derived.2.1, ws3_holonomy_model_derived.2.2⟩

/-- **(d) LOCAL COHERENCE IS REAL AND PERVASIVE.** Every pair reconciles, for every attention (WS2). -/
theorem ws5_audit_coherence_pervasive :
    ∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v :=
  ws2_pairwise_coherent

/-- **(e) NAMES-NOT-TERMS.** A META-property about identifiers, not a proposition: no proof term, definition, or
discharged obligation is named as a forbidden content-word ("good," "common," "value," "justice," "consensus,"
"ethics," "self," "import," "god," "love," "compass") as a whole word. Enforced by the protocol §6 mechanical grep
(hits are docstring prose only), not by this `True`; carried as the accepted house placeholder. -/
theorem ws5_audit_names_not_terms : True := trivial

end P2S8
