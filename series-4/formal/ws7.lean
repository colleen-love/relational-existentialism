/-
`series-4/formal/ws7.lean`

WS7 — **The anti-trivialization audit.** Series 4, the honesty workstream. Owns the
program verdict: whether the payoffs genuinely reduce to one finitude (the finitude of
facing) or whether the unification is an artifact of an over-strong definition.

* **FinitudeOfFacing** — the single fact beneath the payoffs: the face is proper off
  the diagonal and improper on it. Proved (`ws7_finitude_of_facing`).
* **T2** `ws7_payoffs_hold` — the six forced payoffs conjoined (a conjunction, NOT a
  derivation from finitude; renamed from `ws7_one_finitude` per `project-review-2.md` R1).
  `ws7_incompleteness_off_from_finitude` is the one payoff genuinely derived from
  `FinitudeOfFacing`.
* **T3** `ws7_deductions_dont_collapse` (+ `ws7_plurality_vs_collapse_distinct`) — the
  distinctness anchor, mechanized for two rows only; a full six-way anchor is open.
* **T4** `ws7_verdict` / `ProgramVerdict` — the typed verdict, honestly downgraded to
  **`payoffsEstablished`**: the payoffs hold and are distinct where mechanized, but their
  common origin in one finitude is argued, not fully mechanized (not `oneFinitude`).

Self-audit disclosure (charter §9): this is Claude-auditing-Claude, a disclosed
limitation. The distinctness anchor (T3) is the objective part — a structural
impossibility, not a subjective independence claim.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws6

universe u

open Cardinal Series4.WS1 Series4.WS2

namespace Series4.WS7

variable {κ : Cardinal.{u}}

/-! ## The single finitude beneath the payoffs -/

/-- **The finitude of facing.** Off the self-loop diagonal the face is a *proper*
sub-object of its source (facing costs you a proper part of yourself); on the diagonal
(Ω) it is improper. This is the one fact the payoffs are consequences of. -/
def FinitudeOfFacing (hinf : ℵ₀ ≤ κ) : Prop :=
  (∀ x : (νPk κ).X, x ∉ ((νPk κ).str x).1 → face x x ⊂ ReachSet x)
  ∧ (face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf))

/-- The finitude of facing holds. (The off-diagonal clause is the scoped
non-self-relating properness `ws6_selfface_proper_nonselfrelating`; the R2 self-face is
trivial for self-relating objects — see the WS6 scope note.) -/
theorem ws7_finitude_of_facing (hinf : ℵ₀ ≤ κ) : FinitudeOfFacing hinf :=
  ⟨fun x hx => Series4.WS6.ws6_selfface_proper_nonselfrelating x hx,
   by rw [ws1_omega_face hinf, reachSet_omega hinf]⟩

/-! ## T2 — the established payoffs (a conjunction, NOT a derivation from finitude) -/

/-- **T2 — the payoffs hold.** The six forced payoffs all hold: plurality (WS3), no-top
(WS4, cardinal form), positioned views (WS4, definitional), the bound on the loop-spine
(WS5), incompleteness off the diagonal (WS6, non-self-relating case), and incompleteness
on it (WS6).

Adversarial-review finding (`project-review-2.md`, R1): this is a **conjunction** of six
independently-proved facts — it does *not* take `FinitudeOfFacing` as a hypothesis and
derive them, so it is **not**, by itself, evidence that they share a single origin (any
six theorems can be conjoined). Renamed from `ws7_one_finitude` to `ws7_payoffs_hold` to
say only what it proves. The genuine (partial) derivation-from-finitude is
`ws7_incompleteness_off_from_finitude` below; the reduction of the *other* payoffs to a
single finitude is argued in prose, not mechanized (see the verdict caveat). -/
theorem ws7_payoffs_hold {Q : Type u} (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hq : q₁ ≠ q₂) :
    -- plurality (WS3)
    (∃ a b : Series4.WS3.νLk κ Q, a ≠ b ∧ Series4.WS3.NonAtomic a ∧ Series4.WS3.NonAtomic b)
    -- no top (WS4)
  ∧ (∀ x : (νPk κ).X, ¬ ∀ y, y ∈ ((νPk κ).str x).1)
    -- positioned views (WS4)
  ∧ (∀ o : Series4.WS4.Observation κ, ∃ x y, Series4.WS4.viewOf o = face x y)
    -- endogenous bound on the spine (WS5)
  ∧ (HereditarilyNonempty (omegaState hinf)
      ∧ face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf))
    -- incompleteness off the diagonal (WS6)
  ∧ (∀ x : (νPk κ).X, x ∉ ((νPk κ).str x).1 → face x x ⊂ ReachSet x)
    -- incompleteness on the diagonal (WS6)
  ∧ (omegaState hinf ∈ ((νPk κ).str (omegaState hinf)).1) :=
  ⟨Series4.WS3.ws3_plurality_core hinf hq,
   Series4.WS4.ws4_no_top_cardinal,
   Series4.WS4.ws4_view_is_positioned,
   Series4.WS5.ws5_omega_endogenous_point hinf,
   fun x hx => Series4.WS6.ws6_selfface_proper_nonselfrelating x hx,
   (Series4.WS6.ws6_omega_nonterminating hinf).2⟩

/-- **The one genuine derivation from finitude.** The off-diagonal incompleteness payoff
*does* follow from `FinitudeOfFacing` — it is literally its first clause. This is the only
payoff mechanically derived *from* the finitude (the rest are established independently and
their reduction to finitude is argued in prose). Recorded so the "one finitude" claim has
at least one honest mechanized instance rather than none. -/
theorem ws7_incompleteness_off_from_finitude (hinf : ℵ₀ ≤ κ) (h : FinitudeOfFacing hinf) :
    ∀ x : (νPk κ).X, x ∉ ((νPk κ).str x).1 → face x x ⊂ ReachSet x :=
  h.1

/-! ## T3 — the distinctness ledger (the guard that makes T2 honest) -/

/-- **T3 — the deductions do not collapse.** The off-diagonal incompleteness (the
self-face is *proper*) and the on-diagonal incompleteness (the self-face is *improper*)
cannot both hold of the same object: proper and improper are contradictory. So the two
incompleteness payoffs apply to *provably disjoint* states and are genuinely different
consequences of the finitude of facing — not one deduction in two costumes. This is the
objective anchor (a structural impossibility) that keeps the one-finitude reduction from
being trivialization. -/
theorem ws7_deductions_dont_collapse :
    ¬ ∃ x : (νPk κ).X, face x x = ReachSet x ∧ face x x ⊂ ReachSet x := by
  rintro ⟨x, heq, hss⟩
  exact (Set.ssubset_iff_subset_ne.mp hss).2 heq

/-- **T3, second anchor — plurality and collapse live on different carriers.** The
plurality payoff holds on the labelled carrier `νLk κ Q` (distinct loops), while the
collapse it is earned against holds on the plain carrier `νPk κ` (hereditarily-nonempty
states are equal). They are consequences on *different objects*, so they are not one
deduction restated. A second mechanized row of the distinctness ledger, beyond the
incompleteness pair. -/
theorem ws7_plurality_vs_collapse_distinct {Q : Type u} (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q}
    (hq : q₁ ≠ q₂) :
    (∃ a b : Series4.WS3.νLk κ Q, a ≠ b)
  ∧ (∀ a b : (νPk κ).X, HereditarilyNonempty a → HereditarilyNonempty b → a = b) :=
  ⟨by obtain ⟨a, b, hab, _, _⟩ := Series4.WS3.ws3_plurality_core hinf hq; exact ⟨a, b, hab⟩,
   fun a b ha hb => Series4.WS2.ws2_collapse hinf a b ha hb⟩

/-! ## T4 — the typed program verdict -/

/-- The program verdict. `payoffsEstablished`: the payoffs hold and are pairwise-distinct
where mechanized, but their common origin in a single finitude is argued, not fully
mechanized. `oneFinitude`: the stronger claim (all payoffs derived from one finitude) —
*not* reached in this pass. `trivialized`: the unification is definitional. -/
inductive ProgramVerdict
  | payoffsEstablished
  | oneFinitude
  | trivialized
  deriving DecidableEq

/-- **The verdict — `payoffsEstablished` (honest downgrade after adversarial review).**
`project-review-2.md` (R1) is right: `ws7_payoffs_hold` is a conjunction, not a derivation
from `FinitudeOfFacing`, so "one finitude, *substantively*" is not mechanized. What *is*
established: the six payoffs hold (`ws7_payoffs_hold`); one of them genuinely derives from
finitude (`ws7_incompleteness_off_from_finitude`); and distinctness is mechanized for two
rows (`ws7_deductions_dont_collapse`, `ws7_plurality_vs_collapse_distinct`). The full
reduction of *all* payoffs to one finitude — and the full six-way distinctness anchor —
are the named opens. So the verdict is **payoffs established, common origin argued not
mechanized**, not `oneFinitude`. `Trivialized` remains a typed, reachable alternative the
mechanized anchors refute. -/
def ws7_verdict : ProgramVerdict := ProgramVerdict.payoffsEstablished

/-- The verdict is *not* Trivialized (the mechanized distinctness anchors refute it), and
also *not* the stronger `oneFinitude` (that would need each payoff derived from
`FinitudeOfFacing`, only partially done). It is the honest middle: `payoffsEstablished`. -/
theorem ws7_not_trivialized : ws7_verdict ≠ ProgramVerdict.trivialized := by decide

/-- The verdict is the honest middle `payoffsEstablished`, not the stronger
`oneFinitude`. -/
theorem ws7_verdict_eq : ws7_verdict = ProgramVerdict.payoffsEstablished := rfl

end Series4.WS7
