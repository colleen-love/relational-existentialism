/-
`series-08/formal/Series08/ws6.lean`

WS6 — **The heuristic ceiling.** Series 08, the honest boundary.

The universal forms of layering-as-narrowing (WS4) and the conservation law (WS5), reported as
defended theses floored by the mechanized core; and the retraction ledger — the STRONG conservation
law is refuted (WS5), the WEAK bound (mere boundedness) survives on `PkObj`'s κ-bound. Introduces no
new object; draws the line. Consumes WS4 and WS5.

Design doc: `series-08/spec/ws6-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series08.ws4
import Series08.ws5

universe u

namespace Series08.WS6

open Series08.WS1 Series08.WS3 Series08.WS4 Series08.WS5 Cardinal

variable {κ : Cardinal.{u}} {X : Type u}

/-- **D1 — per-hold finiteness.** Every hold affords a `< κ`-bounded breadth: the carrier's own
constraint. The floor of the "bounded" thesis. -/
theorem ws6_hold_finite (dest : X → PkObj κ X) (h : Hold dest) : breadth dest h < κ :=
  (dest h.1.2).2

/-- **D2 — the provable core.** Narrowing is monotone along `≺` and every hold is finite. -/
theorem ws6_provable_core (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    afford dest h' ⊆ afford dest h ∧ breadth dest h < κ :=
  ⟨ws4_depth_is_narrowing dest h h' hp, ws6_hold_finite dest h⟩

/-- **D3 — the retraction ledger.** The STRONG conservation law is refuted (WS5); the WEAK bound
(mere boundedness) survives on every hold. The "self-limiting universe" is retracted. -/
theorem ws6_conservation_retracted :
    ws5_conservation_verdict = ConservationVerdict.partialV
  ∧ (∀ (Y : Type u) (dest : Y → PkObj κ Y) (h : Hold dest), breadth dest h < κ) :=
  ⟨rfl, fun _ dest h => ws6_hold_finite dest h⟩

/-- **D4 — the defended universals, NOT theorems.** Documentation of what is defended above the
floor (all-constructions narrowing; universal mere-boundedness) and why it is off the machine (the
un-rangeable quantifier). The Lean payoff is D1–D3. -/
theorem ws6_universal_theses : True := trivial

end Series08.WS6
