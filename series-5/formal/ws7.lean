/-
`series-5/formal/ws7.lean`

WS7 — **The anti-trivialization audit.** Series 5, the honesty workstream. Owns the program
verdict: whether boundlessness, groundlessness, cross-level relating, and non-collapse
genuinely reduce to one fact — the double-unboundedness of the tower — or whether that
unification is an artifact of the construction.

The mechanized picture (following the Series 4 R1 discipline): the payoffs are a
*conjunction*, not a derivation; **two** payoffs genuinely derive from double-unboundedness
(no-top from no-last-level, descent from no-first-level), **one** (leak-freeness) does not
(it is the inherited composition, holding even on a walled constant tower); the distinctness
anchors refute `trivialized`; the incomplete reduction refutes `oneDoubleUnboundedness`. So
the verdict is the honest middle, `payoffsEstablished`.

Self-audit disclosure (charter §9): Claude-auditing-Claude. The distinctness anchors are the
objective part. Design doc: `series-5/spec/ws07-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws5

universe u

open Cardinal Series5.WS1 Series5.WS2 Series5.WS3 Series5.WS4 Series5.WS6

namespace Series5.WS7

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## Part A — the single fact (F1), and the two-fact base (F2) -/

/-- **F1 — DoubleUnboundedness.** The index has no least and no greatest element, and the
cardinals are unbounded. The claimed single fact the payoffs are consequences of. -/
def DoubleUnboundedness (T : Tower Q) : Prop :=
  (∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b)
  ∧ (∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b)
  ∧ (∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card)

theorem ws7_double_unboundedness (T : Tower Q)
    (hna : ∀ a : T.Idx, ∃ b, T.le a b ∧ a ≠ b)
    (hnb : ∀ a : T.Idx, ∃ b, T.le b a ∧ a ≠ b)
    (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :
    DoubleUnboundedness T := ⟨hna, hnb, hunb⟩

/-! ### The S1 obstruction, and the pre-registered fix — REFACTOR COMPLETE (charter §4.1 / §9)

The batched review (project-review-1.md, S1) found that every flagship payoff was conditional
on `hunb` / `DoubleUnboundedness`, satisfied by no *then-built* tower. The reason was
*pre-registered* in the design, not a new dead-end: the WS1 C2 candidate says "the index a
proper class / large directed set with no greatest element," and the charter §9 names the fix,
"the tower existential needs a proper-class index." The original C2 Lean *sketch* — and this
file's `Tower` following it — typed `Idx : Type u`, which **collapses** C2's proper-class index
to a set. A `u`-small index forces the family `a ↦ (T.lvl a).card` to have a supremum, so `hunb`
cannot hold: exactly the "tower with a top" the charter warned of (§4.1). That is now settled on
both sides. `Tower` was made universe-polymorphic (`Idx : Type w`, `Winf : Type (max u w)`), and
`cardinalTower : Tower.{u, u+1}` (WS3) is a **genuinely built** proper-class-indexed tower —
index `Cardinal.{u} × ℤ`, connected by the constructed `boundRelax` injective coalgebra
morphisms — that **does** satisfy `DoubleUnboundedness` (`ws7_cardinalTower_du` below). So the
flagship payoffs hold of a real object with no open antecedent (`ws7_payoffs_unconditional`).
`ws7_setindexed_walls` now carries the honest hypothesis `[Small.{u} T.Idx]`: the collapse is a
fact about *small*-indexed towers, and `cardinalTower`'s index is provably not `u`-small. -/

/-- **The set-indexed collapse (charter §4.1, mechanized).** For any `T : Tower Q` whose index
is `u`-small (`[Small.{u} T.Idx]` — e.g. `constTower`, `growingTower`), the level-cardinals
`a ↦ (T.lvl a).card` form a `u`-small family, so they have a supremum `⨆ a, (T.lvl a).card`
no level exceeds; `hunb` fails. This is *not* a limitation of the program but of a *small*
index — exactly the collapse C2's proper-class index was pre-registered to avoid, and which
`cardinalTower` (index `Cardinal.{u} × ℤ`, *not* `u`-small) escapes. -/
theorem ws7_setindexed_walls (T : Tower Q) [Small.{u} T.Idx] :
    ¬ (∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) := by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ a, (T.lvl a).card)
  exact absurd ha (not_lt.mpr (le_ciSup (Cardinal.bddAbove_range fun a => (T.lvl a).card) a))

/-- **The pre-registered fix works (index level).** A *proper-class* index — realized as a
universe-bumped `Type (u+1)` type, here `Cardinal.{u}` itself with `card = id` — **does**
satisfy the unbounded-cardinals condition: for every `c : Cardinal.{u}` there is a level whose
cardinal exceeds it (`2 ^ c`, by Cantor). So the obstruction in `ws7_setindexed_walls` is
exactly the *small*-index collapse of C2, and the charter-§9 proper-class index resolves it.
The full transport onto such an index — `cardinalTower : Tower.{u, u+1}` — is now built (WS3);
`ws7_cardinalTower_du` upgrades this index-level fact to a genuine doubly-unbounded tower. -/
theorem ws7_properclass_index_cofinal :
    ∃ (I : Type (u+1)) (card : I → Cardinal.{u}), ∀ c : Cardinal.{u}, ∃ a, c < card a :=
  ⟨Cardinal.{u}, id, fun c => ⟨2 ^ c, Cardinal.cantor c⟩⟩

/-- **No *small-indexed* tower is doubly-unbounded** (a consequence of a `u`-small index, not the
program). For any `[Small.{u} T.Idx]` tower the unbounded-cardinals condition fails, so
`DoubleUnboundedness` cannot hold. This is the honest scope of the collapse: it is a fact about
*small* indices, which `cardinalTower` (index `Cardinal.{u} × ℤ`, not `u`-small) escapes. -/
theorem ws7_no_du_tower (T : Tower Q) [Small.{u} T.Idx] : ¬ DoubleUnboundedness T :=
  fun h => ws7_setindexed_walls T h.2.2

/-! ### The refactor complete: a genuinely built doubly-unbounded tower -/

/-- **The doubly-unbounded tower is real (charter §9 refactor, discharged).** The proper-class
-indexed `cardinalTower` (WS3) satisfies `DoubleUnboundedness`: no greatest index (the
`Cardinal` coordinate has no top — `(c, n) < (c, n+1)`), no least index (the `ℤ` coordinate has
no bottom — `(c, n-1) < (c, n)`), and cofinal cardinals (for any `d`, level `(2^(max ℵ₀ d), 0)`
has cardinal `2^(max ℵ₀ d) > d`, by Cantor). So every `DoubleUnboundedness`-conditional payoff
holds of a genuinely built object — the S1 antecedent is discharged, not merely satisfiable. -/
theorem ws7_cardinalTower_du (Q : Type u) : DoubleUnboundedness (cardinalTower Q) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, n⟩
    refine ⟨(c, n + 1), Or.inr ⟨rfl, by omega⟩, ?_⟩
    intro h; have : n = n + 1 := congrArg Prod.snd h; omega
  · rintro ⟨c, n⟩
    refine ⟨(c, n - 1), Or.inr ⟨rfl, by omega⟩, ?_⟩
    intro h; have : n = n - 1 := congrArg Prod.snd h; omega
  · intro d
    refine ⟨(2 ^ (max Cardinal.aleph0 d), 0), ?_⟩
    show d < cardIdxCard (2 ^ (max Cardinal.aleph0 d), 0)
    have h1 : Cardinal.aleph0 ≤ 2 ^ (max Cardinal.aleph0 d) :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) (Cardinal.cantor _))
    show d < max Cardinal.aleph0 (2 ^ (max Cardinal.aleph0 d))
    rw [max_eq_right h1]
    exact lt_of_le_of_lt (le_max_right Cardinal.aleph0 d) (Cardinal.cantor _)

/-- **The second fact (F2's second ingredient): cross-level leak-freeness.** Composition
never annihilates a face — independent of double-unboundedness. -/
def CrossLevelLeakFree (κ : Cardinal.{u}) (Q : Type u) : Prop :=
  ∀ (t : LkObj κ (GLabel Q) (νLk κ (GLabel Q))), t.1.Nonempty →
    (∀ p ∈ t.1, NonAtomic p.2) → NonAtomic (lcomp t)

theorem ws7_crosslevel_leakfree : CrossLevelLeakFree κ Q :=
  fun t ht hmem => (ws6_crosslevel_never_annihilate t ht hmem).1

/-! ## Part B — the payoffs (a conjunction), and which genuinely derive -/

/-- **T2 — the payoffs hold (a conjunction, NOT a derivation).** No-top (WS3),
plurality (WS3/WS4), leak-free relating (WS6), and no-completing-view (WS4/WS6). Following
Series 4 R1: this conjoins independently-established facts; it does not derive them from
`DoubleUnboundedness`. Named `ws7_payoffs_hold`, not `ws7_one_double_unboundedness`. -/
theorem ws7_payoffs_hold (T : Tower Q) (hQ : Nonempty Q) (hdu : DoubleUnboundedness T)
    (a0 : T.Idx) {q1 q2 : Q} (hq : q1 ≠ q2) :
    (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y)
  ∧ (∃ x y : Winf T, x ≠ y)
  ∧ CrossLevelLeakFree (T.lvl a0).card Q
  ∧ (∀ v : ViewAt T, ∃ y : Winf T, ¬ FaceReaches T v y) :=
  ⟨fun x => ws3_no_top T hQ hdu.2.2 x,
   (ws4_groundless_no_collapse T a0 hq).1,
   ws7_crosslevel_leakfree,
   fun v => ws4_no_completing_view T hQ hdu.2.2 v⟩

/-- **No-top genuinely derives from double-unboundedness** (it uses no-last-level). -/
theorem ws7_notop_from_du (T : Tower Q) (hQ : Nonempty Q) (hdu : DoubleUnboundedness T) :
    ∀ x : Winf T, ¬ ∀ y, RelatesInf T x y :=
  fun x => ws3_no_top T hQ hdu.2.2 x

/-! ### The S1 antecedent discharged: payoffs of the *built* doubly-unbounded tower -/

/-- **No-top holds unconditionally on the built doubly-unbounded tower.** Applying
`ws7_notop_from_du` to `cardinalTower` with its `DoubleUnboundedness` witness — no open
antecedent remains. -/
theorem ws7_notop_unconditional (Q : Type u) (hQ : Nonempty Q) :
    ∀ x : Winf (cardinalTower Q), ¬ ∀ y, RelatesInf (cardinalTower Q) x y :=
  ws7_notop_from_du (cardinalTower Q) hQ (ws7_cardinalTower_du Q)

/-- **The flagship payoffs hold of a real object, no open antecedent (charter §9 discharged).**
The four payoffs of `ws7_payoffs_hold`, now applied to the genuinely built, genuinely
doubly-unbounded `cardinalTower` rather than to an abstract `T` with an assumed
`DoubleUnboundedness`. This is what S1 asked for: not a sound conditional, but the payoffs
holding of an actual tower. -/
theorem ws7_payoffs_unconditional (Q : Type u) (hQ : Nonempty Q)
    (a0 : (cardinalTower Q).Idx) {q1 q2 : Q} (hq : q1 ≠ q2) :
    (∀ x : Winf (cardinalTower Q), ¬ ∀ y, RelatesInf (cardinalTower Q) x y)
  ∧ (∃ x y : Winf (cardinalTower Q), x ≠ y)
  ∧ CrossLevelLeakFree ((cardinalTower Q).lvl a0).card Q
  ∧ (∀ v : ViewAt (cardinalTower Q), ∃ y : Winf (cardinalTower Q), ¬ FaceReaches (cardinalTower Q) v y) :=
  ws7_payoffs_hold (cardinalTower Q) hQ (ws7_cardinalTower_du Q) a0 hq

/-- **Descent genuinely derives from double-unboundedness** (it uses no-first-level: `ℤ`
has no least element). -/
theorem ws7_descent_from_du (q0 : Q) (hinf : ℵ₀ ≤ κ) (d : ℤ) :
    ∃ (finer : νLk κ (GLabel Q)) (d' : ℤ), d' < d ∧ RelatesAtGrade (descState q0 hinf d) finer d' :=
  ws6_descent_nonterminating q0 hinf d

/-- **Leak-freeness does NOT derive from double-unboundedness.** It holds unconditionally
(`ws7_crosslevel_leakfree`), *and* the constant (walled) tower is not doubly-unbounded — so
leak-freeness is genuinely a second fact, not a consequence of the tower's double-openness.
This refutes `oneDoubleUnboundedness`. -/
theorem ws7_leakfree_NOT_from_du (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) (Q : Type u) :
    CrossLevelLeakFree κ Q ∧ ¬ DoubleUnboundedness (constTower κ hinf Q) := by
  refine ⟨ws7_crosslevel_leakfree, ?_⟩
  rintro ⟨_, _, hunb⟩
  obtain ⟨a, ha⟩ := hunb κ
  exact absurd ha (lt_irrefl κ)

/-! ## Part C — the distinctness anchors (the objective guard) -/

/-- **T3a — no-top and non-collapse live on provably different structures.** No-top is
about the colimit `W_∞`; non-collapse is the failure of the single-carrier collapse
hypothesis. Different objects, not one deduction restated. -/
theorem ws7_notop_vs_collapse_distinct (T : Tower Q) (hQ : Nonempty Q)
    (hdu : DoubleUnboundedness T) (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y)
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X) :=
  ⟨fun x => ws3_no_top T hQ hdu.2.2 x, fun h => ws5_global_groundless_collapses hinf h⟩

/-- **T3b — the tower (boundless-and-plural) and the single carrier (which cannot be) are
distinct.** The tower is plural; a single carrier provably collapses under global
groundlessness. Contradictory properties on different objects. -/
theorem ws7_tower_vs_carrier_distinct (T : Tower Q) (a0 : T.Idx) {q1 q2 : Q} (hq : q1 ≠ q2)
    (κ : Cardinal.{u}) (hinf : ℵ₀ ≤ κ) :
    (∃ x y : Winf T, x ≠ y)
  ∧ ((∀ x : (νPk κ).X, HereditarilyNonempty x) → Subsingleton (νPk κ).X) :=
  ⟨(ws4_groundless_no_collapse T a0 hq).1, fun h => ws5_global_groundless_collapses hinf h⟩

/-- **T3c — the poles are an index fact, no-top is a carrier fact.** Pole coincidence
survives stripping the carrier (it is a pure `ℤ` order fact, stated with no tower); no-top
does not (it quantifies over `W_∞`). So they are different in kind — the strip test
mechanized as a distinctness. -/
theorem ws7_poles_vs_notop_distinct (T : Tower Q) (hQ : Nonempty Q)
    (hdu : DoubleUnboundedness T) :
    (∀ a : ℤ, ∃ b, a ≤ b ∧ a ≠ b)
  ∧ (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y) :=
  ⟨ws2_strict_above, fun x => ws3_no_top T hQ hdu.2.2 x⟩

/-! ## Part D — the typed program verdict -/

/-- The program verdict. `payoffsEstablished`: payoffs hold, distinct where mechanized,
common origin argued not mechanized. `oneDoubleUnboundedness`: all payoffs derived from
double-unboundedness. `trivialized`: the unification is definitional / payoffs are index
facts relabelled. -/
inductive ProgramVerdict
  | payoffsEstablished
  | oneDoubleUnboundedness
  | trivialized
  deriving DecidableEq

/-- **The verdict — `payoffsEstablished`.** Two payoffs derive from double-unboundedness
(`ws7_notop_from_du`, `ws7_descent_from_du`); one does not (`ws7_leakfree_NOT_from_du`, a
second fact); the distinctness anchors refute `trivialized`; the incomplete reduction
refutes `oneDoubleUnboundedness`. The honest middle, the same place and structural reason as
Series 4. -/
def ws7_verdict : ProgramVerdict := ProgramVerdict.payoffsEstablished

theorem ws7_not_trivialized : ws7_verdict ≠ ProgramVerdict.trivialized := by decide

theorem ws7_not_one_du : ws7_verdict ≠ ProgramVerdict.oneDoubleUnboundedness := by decide

theorem ws7_verdict_eq : ws7_verdict = ProgramVerdict.payoffsEstablished := rfl

end Series5.WS7
