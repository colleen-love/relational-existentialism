/-
`series-3/formal/ws10.lean` — WS10: statement–gloss reconciliation, the grounded moves.

The external review (`series-3/spec/review.md`) found one recurring failure mode:
formal statements weaker than the labels placed on them. WS10 closes what is cheaply
closable against the exact upstream definitions, sorry-free and on no new axioms. This
file discharges the **keystone O1** (the carrier-cardinality lower bound, which every
"Discharged that touches cardinality" silently assumed) and the obligations that fall
out of it once it lands (O4, O5, O6).

* **O1 — `carrier_card_ge`.** `κ ≤ #(νPk κ).X`, proved (not assumed): if `#X < κ` then
  every subset is `< κ`, so `PkObj κ X ≃ Set X`; Lambek gives `X ≃ Set X`, i.e.
  `#X = 2^#X`, contradicting Cantor. This removes the unproved `hcard` hypothesis from
  `ws6_no_maximal`, `ws6_no_global_observer`, and the WS7 collector, and lets the
  **concrete tuple** at `κ₀ = ℵ₀` be exhibited hypothesis-free — making the charter's
  "Discharged at one concrete tuple" true as stated.
* **O4 — incompleteness with content.** The diagonal (`ws5_carrier_incomplete`) is
  Cantor and structure-independent; the κ-consuming half — no observer window reaches
  the carrier — is `ws6_no_global_observer` with O1 discharged into it. Conjoined:
  the carrier strictly exceeds every observer's `< κ` window *because* it is `≥ κ`.
* **O5 — standpoints are proper.** Every positioned view genuinely misses something
  (its support is `< κ`, the carrier is `≥ κ`): the third leg that makes "positioned
  *partial* views" a theorem.
* **O6 — the dynamics–carrier bridge.** At `κ₀ = ℵ₀` every support is finite *by the
  carrier's own bound*, so per-state attention lives on a genuine `FlooredSimplex` over
  the carrier's support — the first convergence theorem whose state space is the
  carrier's, not an abstract `Fintype`.

O2 (the atom / grounded core) is out of scope here. O3 (canonicity among weak
distributive laws) and O7 (WS9 attractivity, the exact bifurcation boundary) are the
remaining WS10 program, noted at the end — not laundered into this file's theorems.
-/
import ws8
import ws9

namespace Series3.WS10

open Series3.WS1 Series3.WS2 Series3.WS5 Series3.WS6 Series3.WS7 Series3.WS8 Series3.WS9

/-! ### O1 — the carrier-cardinality lower bound (the keystone) -/

/-- **O1 (Discharged).** `κ ≤ #(νPk κ).X`. If instead `#X < κ`, every subset of `X`
is `< κ`-sized, so `PkObj κ X` is *all* of `Set X`; Lambek (`(νPk κ).str` bijective)
gives `X ≃ PkObj κ X ≃ Set X`, i.e. `#X = 2^#X`, contradicting Cantor. Unconditional in
`κ` (no `ℵ₀ ≤ κ` needed). This is the hypothesis every cardinality-touching "Discharged"
silently carried. -/
theorem carrier_card_ge (κ : Cardinal.{u}) : κ ≤ Cardinal.mk (νPk κ).X := by
  by_contra hlt
  push_neg at hlt
  have hall : ∀ s : Set (νPk κ).X, Cardinal.mk (↥s) < κ :=
    fun s => lt_of_le_of_lt (Cardinal.mk_subtype_le (· ∈ s)) hlt
  have e1 : PkObj κ (νPk κ).X ≃ Set (νPk κ).X := Equiv.subtypeUnivEquiv hall
  have hbij : Function.Bijective (νPk κ).str := lambek (νPk_terminal κ)
  have hc : Cardinal.mk (νPk κ).X = 2 ^ Cardinal.mk (νPk κ).X :=
    calc Cardinal.mk (νPk κ).X
        = Cardinal.mk (PkObj κ (νPk κ).X) := Cardinal.mk_congr (Equiv.ofBijective _ hbij)
      _ = Cardinal.mk (Set (νPk κ).X) := Cardinal.mk_congr e1
      _ = 2 ^ Cardinal.mk (νPk κ).X := Cardinal.mk_set
  have hcantor := Cardinal.cantor (Cardinal.mk (νPk κ).X)
  rw [← hc] at hcantor
  exact lt_irrefl _ hcantor

/-- **O1 corollary.** No carrier state is maximal — now hypothesis-free. -/
theorem ws10_no_maximal {κ : Cardinal.{u}} (u : (νPk κ).X) : ¬ IsMaximal u :=
  ws6_no_maximal (carrier_card_ge κ) u

/-- **O1 corollary.** No observer window surjects onto the carrier — hypothesis-free. -/
theorem ws10_no_global_observer {κ : Cardinal.{u}} (obs : (νPk κ).X) :
    ¬ ∃ f : SelfSupport κ obs → (νPk κ).X, Function.Surjective f :=
  ws6_no_global_observer (carrier_card_ge κ) obs

/-- **O1 (the concrete tuple, hypothesis-free).** At `κ₀ = ℵ₀` (regular, in Mathlib),
any `μ > 0`, and `Łₙ` (`n ≥ 2`), the WS7 non-collapse bundle holds with **no** unproved
cardinality hypothesis. The charter's "witnessed Goldilocks point" is now a fact, not a
universally-quantified schema. -/
theorem ws10_concrete_tuple (μ : ℝ) (hμ : 0 < μ) (A : Set ℝ) (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WS7NonCollapse Cardinal.aleph0.{0} μ A) :=
  ws7_band_and_retro Cardinal.aleph0.{0} Cardinal.isRegular_aleph0
    (carrier_card_ge Cardinal.aleph0.{0}) μ hμ A n hn

/-! ### O4 — incompleteness with content (the κ-consuming half) -/

/-- **O4 (Discharged).** Bounded self-modelling: every state's attention window both
(a) fails to enumerate its own predicates (the Cantor diagonal, structure-independent)
**and** (b) fails to reach the carrier (cardinality — genuinely consumes `κ` via
`carrier_card_ge`). Half (b) is the incompleteness the finiteness rhetoric was pointing
at: the object strictly exceeds every observer's window *because* windows are `< κ` and
the carrier is `≥ κ`. -/
theorem ws10_bounded_self_model {κ : Cardinal.{u}} (u : (νPk κ).X) :
    (¬ ∃ e : SelfSupport κ u → (SelfSupport κ u → Prop), Function.Surjective e)
  ∧ (¬ ∃ f : SelfSupport κ u → (νPk κ).X, Function.Surjective f) :=
  ⟨ws5_carrier_incomplete u, ws6_no_global_observer (carrier_card_ge κ) u⟩

/-! ### O5 — standpoints are proper (partial in fact, not just in name) -/

/-- **O5 (Discharged).** Every positioned standpoint is *proper*: its view holds on a
`< κ` set of states while the carrier has `≥ κ`, so some state lies outside the view.
This is the third leg — distinct (E1), non-global (E2), and now **partial** — that turns
"positioned partial views" from a noun phrase into a theorem. -/
theorem ws10_standpoint_proper {κ : Cardinal.{u}} (sp : Standpoint κ) :
    ∃ y, ¬ sp.view y := by
  by_contra h
  push_neg at h
  have hall : ∀ y, y ∈ ((νPk κ).str sp.base).1 := fun y => (sp.local' y).mp (h y)
  have hinj : Function.Injective
      (fun y : (νPk κ).X => (⟨y, hall y⟩ : SelfSupport κ sp.base)) :=
    fun a b hab => congrArg Subtype.val hab
  have hle : Cardinal.mk (νPk κ).X ≤ Cardinal.mk (SelfSupport κ sp.base) :=
    Cardinal.mk_le_of_injective hinj
  exact absurd (lt_of_le_of_lt hle ((νPk κ).str sp.base).2) (not_lt.mpr (carrier_card_ge κ))

/-! ### O6 — the dynamics–carrier bridge (at `κ₀ = ℵ₀`)

At `ℵ₀`, every support is finite *because the carrier's own `< ℵ₀` bound says so*, so
`FlooredSimplex` — which needs `Fintype` — can live on a carrier support. This is the
payoff that ratifies `ℵ₀`: "finite attention" stops being a slogan. -/

/-- Every `ℵ₀`-carrier support is finite, by the carrier's own bound `#(str u) < ℵ₀`. -/
noncomputable instance selfSupportFintype (u : (νPk Cardinal.aleph0.{0}).X) :
    Fintype (SelfSupport Cardinal.aleph0.{0} u) :=
  (Cardinal.lt_aleph0_iff_fintype.mp ((νPk Cardinal.aleph0.{0}).str u).2).some

/-- **O6 (Discharged).** For every state of the `ℵ₀`-carrier, per-state attention under a
**nonexpansive** selection converges to a unique fixed point **on that state's own
support** — the first convergence theorem whose state space is a carrier support, not an
abstract `Fintype S`. The `Fintype` the simplex needs is a theorem the carrier supplies;
convergence is WS9's conditional (band-free) result. -/
theorem ws10_carrier_attention_converges (u : (νPk Cardinal.aleph0.{0}).X)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (unif : SelfSupport Cardinal.aleph0.{0} u → ℝ) (hn : ∀ r, 0 ≤ unif r) (hs : ∑ r, unif r = 1)
    (sel : SelectionMap (SelfSupport Cardinal.aleph0.{0} u) unif)
    (sl : SelectionLipschitz (SelfSupport Cardinal.aleph0.{0} u) unif sel) (hL : (sl.L_R μ : ℝ) ≤ 1) :
    ∃! p : FlooredSimplex (SelfSupport Cardinal.aleph0.{0} u) μ unif,
      mutT μ hμ0.le hμ1 unif hn hs sel p = p := by
  -- the support is nonempty because a probability vector sums to 1 ≠ 0
  haveI : Nonempty (SelfSupport Cardinal.aleph0.{0} u) :=
    Finset.univ_nonempty_iff.mp
      (Finset.nonempty_of_sum_ne_zero (by rw [hs]; exact one_ne_zero))
  haveI := flooredSimplex_nonempty μ hμ1 unif hn hs
  exact ws9_nonexpansive_converges unif hn hs sel sl μ hμ0 hμ1 hL

/-!
### The remaining WS10 program (recorded, not laundered)

* **O3 — canonicity among weak distributive laws.** The review's Overreach 2:
  `ws3_weak_law_canonical` proves uniqueness of the map satisfying one concrete
  destructor equation (`destEquiv` injectivity), *not* canonicity over the class of weak
  distributive laws (natural transformations with the weak-law axioms) that §6.1 pinned.
  The honest reclassification: coherence and weak-pullback preservation stand Discharged;
  **canonicity among weak laws reopens** as the obligation `WeakDistLaw`
  inhabitation + uniqueness (Garner's Vietoris result is the literature signal it is
  true; the mechanization cost — the Egli–Milner multiplication square, easy to
  mis-transcribe per the pentagon erratum — is the unknown). Not attempted here.
* **O7 — WS9 residue.** `ws9_bifurcation` is a statement about the *multiplier* `2(1−μ)`;
  the orbit-level "attracting above, repelling below" (O7a) needs an MVT/Lipschitz bound
  on the induced map away from the center. The interval `μ ∈ (3/8, 1/2)` (O7b) and global
  uniqueness above `μ⋆` (O7c) remain characterized-open — the exact bifurcation boundary
  is a surface with no closed form. Not attempted here.
-/

end Series3.WS10
