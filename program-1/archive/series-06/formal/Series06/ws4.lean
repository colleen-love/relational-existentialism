/-
`series-06/formal/ws4.lean`

WS4 — **The arrow: self-knowing gives directionality.** Series 06, payoff workstream.

Consumes `prec` (= README §4's order, built from WS3's `stepM`) and proves it a strict,
directional order. The lossy self-survey (`trunc` many-to-one — the past) and the
one-to-many residue-opening (the open future) are delivered as genuine fibre facts.

BUILD FINDING (routed to WS4 design, recorded in `charter-status.md`). The pre-registered
**Partial — imported axis** outcome fires. On the founded-approximation model:
* the arrow IS strict and directional (`ws4_arrow_strict`, `ws4_no_return`), but its
  strictness is carried by the survey-DEPTH index `ℕ` (`prec_depth_lt`), which does NOT
  survive the strip of the external time index; and
* there IS a first moment — the depth-0 bud `⟨0, unit⟩` has no `≺`-predecessor
  (`ws4_arrow_has_first_moment`), so endogeneity (no first moment) is NOT earned here.
The genuinely diagonal-driven content is that each step opens a residue that moves the
state (`ws3_residue_new`); the ORDER's strictness, as formalized, rests on the counter.
Escalation to the richer home (metric C4) is owed for the endogenous arrow.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series06.ws3

universe u

namespace Series06.WS4

open Series06.WS1 Series06.WS3 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The lossy self-survey (the past) and the one-to-many residue (the future) -/

/-- **`ws4_survey_lossy` — the survey/truncation is many-to-one (the past is settled but
lossy).** At every stage there are two distinct approximations with the same truncation:
coarsening forgets detail. -/
theorem ws4_survey_lossy (hinf : ℵ₀ ≤ κ) :
    ∀ n, ∃ s t : Approx κ (n+1), s ≠ t ∧ trunc κ n s = trunc κ n t := by
  intro n
  induction n with
  | zero =>
      refine ⟨toPk hinf (∅ : Set (Approx κ 0)),
              toPk hinf ({PUnit.unit} : Set (Approx κ 0)), ?_, rfl⟩
      intro h
      have hv := congrArg Subtype.val h
      simp only [toPk_val] at hv
      exact (Set.singleton_ne_empty (PUnit.unit : Approx κ 0)) hv.symm
  | succ n ih =>
      obtain ⟨s', t', hne, heq⟩ := ih
      refine ⟨toPk hinf {s'}, toPk hinf {t'}, ?_, ?_⟩
      · intro h
        apply hne
        have hv := congrArg Subtype.val h
        simp only [toPk_val] at hv
        exact Set.singleton_injective hv
      · apply Subtype.ext
        show (trunc κ n) '' ({s'} : Set (Approx κ (n+1))) = (trunc κ n) '' {t'}
        rw [Set.image_singleton, Set.image_singleton, heq]

/-- **`ws4_residue_one_to_many` — residue-opening is a relation, not a function (the open
future).** Some stage-`n` state has `≥ 2` truncation-preimages: forgetting is a function,
generating its multivalued converse. -/
theorem ws4_residue_one_to_many (hinf : ℵ₀ ≤ κ) (n : ℕ) :
    ∃ x : Approx κ n, 2 ≤ Cardinal.mk {s : Approx κ (n+1) // trunc κ n s = x} := by
  obtain ⟨s, t, hne, heq⟩ := ws4_survey_lossy hinf n
  refine ⟨trunc κ n s, ?_⟩
  rw [Cardinal.two_le_iff]
  exact ⟨⟨s, rfl⟩, ⟨t, heq.symm⟩, fun h => hne (congrArg Subtype.val h)⟩

/-! ## The order is strict and directional -/

/-- **`ws4_arrow_strict` — `≺` is irreflexive and transitive.** -/
theorem ws4_arrow_strict (hinf : ℵ₀ ≤ κ) :
    Irreflexive (prec hinf) ∧ Transitive (prec (κ := κ) hinf) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    exact (Nat.lt_irrefl m.1) (prec_depth_lt hinf hm)
  · intro a b c hab hbc
    exact Relation.TransGen.trans hab hbc

/-- **`ws4_no_return` — asymmetry: no cycles.** Perpetuity (WS3) plus strictness gives no
return. -/
theorem ws4_no_return (hinf : ℵ₀ ≤ κ) (m m' : Moment κ) :
    prec hinf m m' → ¬ prec hinf m' m := by
  intro h h'
  exact (Nat.lt_irrefl m.1) (lt_trans (prec_depth_lt hinf h) (prec_depth_lt hinf h'))

/-! ## The endogeneity FAILURE (Partial — imported axis)

The arrow's strictness rests on the survey-depth index, and there is a first moment. This is
the pre-registered honest Partial; the endogenous arrow (no first moment, strictness from
properness alone) is owed to the metric home C4. -/

/-- The depth-0 bud is a moment with no `≺`-predecessor: a first moment. So the arrow is NOT
endogenous on this carrier. (Strictness is charged to the depth counter, not to properness.) -/
theorem ws4_arrow_has_first_moment (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ m₀ : Moment κ, prec hinf m₀ (⟨0, PUnit.unit⟩ : Moment κ))
  ∧ (∀ m m' : Moment κ, prec hinf m m' → m.1 < m'.1) := by
  refine ⟨?_, fun _ _ h => prec_depth_lt hinf h⟩
  rintro ⟨m₀, h⟩
  exact (Nat.not_lt_zero m₀.1) (prec_depth_lt hinf h)

/-- **The genuinely diagonal-driven half (what survives).** Each single `≺`-step opens a
residue that genuinely moves the state away from self-reproduction — the properness of
self-knowledge (Cantor, `ws3_residue_new`). This is the counter-free content of the arrow;
the ORDER's strictness above additionally uses the depth index (the imported-axis Partial). -/
theorem ws4_arrow_from_properness (hinf : ℵ₀ ≤ κ) (m : Moment κ) :
    (stepM hinf m).2 = residue hinf m
  ∧ (residue hinf m).1 ≠ ({m.2} : Set (Approx κ m.1)) :=
  ⟨rfl, ws3_residue_new hinf m⟩

end Series06.WS4
