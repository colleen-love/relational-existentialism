/-
`series-03/formal/ws10.lean` — WS10: statement–gloss reconciliation, the grounded moves.

The external review (`series-03/spec/ws9/03-project-review.md`) found one recurring failure mode:
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

Also discharged here:
* **O2 (Impossibility).** `ws10_unlabeled_atomless_collapses` — in unlabeled `νP_κ` any
  two hereditarily-nonempty states are *equal*: atomlessness and plurality are jointly
  unsatisfiable (an Aczel–Mendler bisimulation `ζ = str × str`, collapsed by `bisim_eq`).
  The atom is load-bearing for plurality; the positive (i)-object must move to the graded
  carrier (routed).
* **O7a / O7c.** `ws10_center_globally_attracting` — the induced attention map contracts
  toward the center with factor `2(1−μ)` (globally, by one algebraic identity), and
  `ws10_center_unique_above` — so for `μ > ½` the center is the *unique* fixed point,
  sharpening the pitchfork residue from "characterized open" to a theorem.

O2's graded-core (positive (i)) discharge, O3 (canonicity among weak distributive laws),
and O7b (the `(3/8, 1/2)` gap) are the remaining WS10 program, noted at the end — not
laundered into this file's theorems.
-/
import ws8
import ws9

namespace Series03.WS10

open Series03.WS1 Series03.WS2 Series03.WS5 Series03.WS6 Series03.WS7 Series03.WS8 Series03.WS9

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

/-! ### O2 — atomless + plural is unsatisfiable in unlabeled `νP_κ` (Impossibility proved)

The review's Overreach 5: the carrier contains `bottomState` (empty successor), a
relational atom. The two direct repairs — carve the hereditarily-nonempty subcarrier,
or move to the nonempty powerset functor — **both collapse**, and the collapse is a
theorem. `R x y := (x, y both hereditarily nonempty)` is an Aczel–Mendler bisimulation:
`ζ(x,y) := str x × str y` on the graph lands in `R` by closure, is `< κ` (a product of
two `< κ` cardinals, `κ` infinite), and `fst '' (A × B) = A` *exactly because* `B` is
nonempty. By `bisim_eq`, any two hereditarily-nonempty states are **equal** — the
groundless sub-universe of unlabeled `P_κ` is the single point `Ω`. Atomlessness is
load-bearing for plurality: an ungraded, groundless relation admits exactly One
(Parmenides-shaped), a *local* commitment that also prices against non-collapse. -/

section O2
variable {κ : Cardinal.{u}}

/-- Reachability along the successor relation. -/
def Reaches (x y : (νPk κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ ((νPk κ).str a).1) x y

/-- Hereditarily nonempty: every reachable state has a nonempty successor set. -/
def HereditarilyNonempty (x : (νPk κ).X) : Prop :=
  ∀ v, Reaches x v → ((νPk κ).str v).1 ≠ ∅

lemma HereditarilyNonempty.ne_empty {x : (νPk κ).X}
    (hx : HereditarilyNonempty x) : ((νPk κ).str x).1 ≠ ∅ :=
  hx x Relation.ReflTransGen.refl

lemma HereditarilyNonempty.succ {x w : (νPk κ).X}
    (hx : HereditarilyNonempty x) (hw : w ∈ ((νPk κ).str x).1) : HereditarilyNonempty w :=
  fun v hv => hx v (Relation.ReflTransGen.head hw hv)

/-- The graph of "both hereditarily nonempty". -/
private abbrev HNGraph (κ : Cardinal.{u}) : Type u :=
  {p : (νPk κ).X × (νPk κ).X // HereditarilyNonempty p.1 ∧ HereditarilyNonempty p.2}

/-- The bisimulation coalgebra structure `ζ(x,y) = str x × str y` on the graph. -/
noncomputable def hnZeta (hinf : Cardinal.aleph0 ≤ κ) (q : HNGraph κ) :
    PkObj κ (HNGraph κ) :=
  ⟨{ g : HNGraph κ | g.1.1 ∈ ((νPk κ).str q.1.1).1 ∧ g.1.2 ∈ ((νPk κ).str q.1.2).1 }, by
    have hinj : Function.Injective
        (fun g : ↥{ g : HNGraph κ |
              g.1.1 ∈ ((νPk κ).str q.1.1).1 ∧ g.1.2 ∈ ((νPk κ).str q.1.2).1 } =>
          ((⟨g.1.1.1, g.2.1⟩ : ↥((νPk κ).str q.1.1).1),
           (⟨g.1.1.2, g.2.2⟩ : ↥((νPk κ).str q.1.2).1))) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val (congrArg Prod.fst hab)
      · exact congrArg Subtype.val (congrArg Prod.snd hab)
    have hbmul : Cardinal.mk (↥((νPk κ).str q.1.1).1) * Cardinal.mk (↥((νPk κ).str q.1.2).1) < κ :=
      Cardinal.mul_lt_of_lt hinf ((νPk κ).str q.1.1).2 ((νPk κ).str q.1.2).2
    have hbprod : Cardinal.mk (↥((νPk κ).str q.1.1).1 × ↥((νPk κ).str q.1.2).1)
        = Cardinal.mk (↥((νPk κ).str q.1.1).1) * Cardinal.mk (↥((νPk κ).str q.1.2).1) := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) (hbprod ▸ hbmul)⟩

/-- `R x y := (both hereditarily nonempty)` is a `P_κ`-bisimulation on the carrier. -/
noncomputable def hereditarilyNonempty_bisim (hinf : Cardinal.aleph0 ≤ κ) :
    Bisim (νPk κ) (fun x y => HereditarilyNonempty x ∧ HereditarilyNonempty y) where
  ζ := hnZeta hinf
  nat_fst := fun q => by
    apply Subtype.ext
    rw [PkMap_val]
    ext c
    simp only [hnZeta, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hc
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr q.2.2.ne_empty
      exact ⟨⟨(c, d), q.2.1.succ hc, q.2.2.succ hd⟩, ⟨hc, hd⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg.1
  nat_snd := fun q => by
    apply Subtype.ext
    rw [PkMap_val]
    ext c
    simp only [hnZeta, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hc
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr q.2.1.ne_empty
      exact ⟨⟨(d, c), q.2.1.succ hd, q.2.2.succ hc⟩, ⟨hd, hc⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg.2

/-- **O2 (Impossibility proved).** In the unlabeled carrier `νP_κ`, any two
hereditarily-nonempty states are **equal**: the groundless (atomless) sub-universe is
the single self-relating point `Ω`. Atomlessness and plurality are jointly
unsatisfiable — removing the atom (by carving or by functor surgery) collapses the
universe. -/
theorem ws10_unlabeled_atomless_collapses (hinf : Cardinal.aleph0 ≤ κ)
    (x y : (νPk κ).X) (hx : HereditarilyNonempty x) (hy : HereditarilyNonempty y) : x = y :=
  ws2_bisim_eq _ (hereditarilyNonempty_bisim hinf) x y ⟨hx, hy⟩

/-- **O2 corollary.** The hereditarily-nonempty subcarrier is a **subsingleton** — the
"forbid atoms by restricting the carrier/functor" route is structural collapse (the
§3.8 failure mode), sharpening `ws7_general_branching_false`. -/
theorem ws10_grounded_core_subsingleton (hinf : Cardinal.aleph0 ≤ κ) :
    Subsingleton {x : (νPk κ).X // HereditarilyNonempty x} :=
  ⟨fun a b => Subtype.ext (ws10_unlabeled_atomless_collapses hinf a.1 b.1 a.2 b.2)⟩

end O2

/-! ### O7 — WS9 residue: the center is globally attracting, and unique above `μ⋆`

The pitchfork gloss "attracting above, repelling below" (R1) and "no global uniqueness
above μ⋆" (R3) were the WS9 residue. Both fall to one **algebraic** identity — no MVT,
no derivative bound. Writing `D = x²+(1−x)² = 2(x−½)²+½ ≥ ½`,
`coordIndF μ x − ½ = (1−μ)·(2x−1)/(2D)`, so since `1/(2D) ≤ 1`, the induced map
contracts toward the center with factor `2(1−μ)` **globally** (not just locally). Above
`μ⋆ = ½` that factor is `< 1`, forcing the center to be the *unique* fixed point of the
induced dynamics — sharpening R3 from "characterized open" to a theorem. (The gap
`μ ∈ (3/8, 1/2)`, R2, stays genuinely open — there the factor exceeds 1.) -/

/-- **O7a (Discharged, and global).** The induced attention map contracts toward the
center `½` with factor `2(1−μ)`, for every `x`: `|coordIndF μ x − ½| ≤ 2(1−μ)·|x − ½|`.
For `μ > ½` this factor is `< 1` — the dynamical "attracting" content the multiplier
`ws9_bifurcation` only hinted at. -/
theorem ws10_center_globally_attracting {μ : ℝ} (hμ1 : μ ≤ 1) (x : ℝ) :
    |coordIndF μ x - 1 / 2| ≤ 2 * (1 - μ) * |x - 1 / 2| := by
  have hD : (0 : ℝ) < x ^ 2 + (1 - x) ^ 2 := coordDen_pos x
  have h1μ : (0 : ℝ) ≤ 1 - μ := by linarith
  have h2D : (1 : ℝ) ≤ 2 * (x ^ 2 + (1 - x) ^ 2) := by nlinarith [sq_nonneg (2 * x - 1)]
  have hkey : coordIndF μ x - 1 / 2
      = (1 - μ) * (2 * x - 1) / (2 * (x ^ 2 + (1 - x) ^ 2)) := by
    unfold coordIndF; field_simp; ring
  have hxhalf : |x - 1 / 2| = |2 * x - 1| / 2 := by
    rw [show x - 1 / 2 = (2 * x - 1) / 2 by ring, abs_div]; norm_num
  have hLHS : |coordIndF μ x - 1 / 2|
      = (1 - μ) * |2 * x - 1| / (2 * (x ^ 2 + (1 - x) ^ 2)) := by
    rw [hkey, abs_div, abs_mul, abs_of_nonneg h1μ,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * (x ^ 2 + (1 - x) ^ 2))]
  rw [hLHS, hxhalf, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (x ^ 2 + (1 - x) ^ 2))]
  nlinarith [mul_nonneg h1μ (abs_nonneg (2 * x - 1)), h2D,
    mul_nonneg (mul_nonneg h1μ (abs_nonneg (2 * x - 1))) (by linarith [h2D] :
      (0 : ℝ) ≤ 2 * (x ^ 2 + (1 - x) ^ 2) - 1)]

/-- **O7c (Discharged above `μ⋆`).** For `μ > ½` the induced dynamics has a **unique**
fixed point — the center. Any fixed `x` satisfies `|x−½| ≤ 2(1−μ)|x−½|` with
`2(1−μ) < 1`, forcing `x = ½`. This closes the "no global uniqueness above `μ⋆`"
residue at the induced-map level. -/
theorem ws10_center_unique_above {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ ≤ 1) {x : ℝ}
    (hfix : coordIndF μ x = x) : x = 1 / 2 := by
  have h := ws10_center_globally_attracting hμ1 x
  rw [hfix] at h
  have hz : |x - 1 / 2| ≤ 0 := by nlinarith [abs_nonneg (x - 1 / 2), h]
  have : x - 1 / 2 = 0 := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  linarith

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
* **O2 (graded core — the Discharged half).** The collapse above shows atomlessness is
  unsatisfiable with plurality in *unlabeled* `P_κ`; the positive (i)-object therefore
  lives in the **graded** carrier `νW_Q` (WS4), where distinct weights distinguish where
  leaves cannot. Defining `wsupp`/`ΩQ`, the graded groundless core, and its plurality at
  `Łₙ` is graded-functor surgery routed to a follow-up (WS10-B), together with the
  KS-no-go / weak-law port under the nonempty-support restriction. Not built here; the
  Impossibility half above is the load-bearing content.
* **O3 — canonicity among weak distributive laws.** `ws3_weak_law_canonical` proves
  uniqueness of the map satisfying one concrete destructor equation (`destEquiv`
  injectivity), *not* canonicity over the class of weak distributive laws that §6.1
  pinned. Honest reclassification: coherence and weak-pullback preservation stand
  Discharged; canonicity among weak laws **reopens** as `WeakDistLaw` inhabitation +
  uniqueness. Garner's Vietoris result signals it is true; the mechanization cost — the
  Egli–Milner multiplication square, easy to mis-transcribe (the pentagon erratum) — is
  the unknown, and the propagation-to-all-of-`P_κ P_κ` step is the named obstruction. At
  risk of Partial; not attempted here (a wrong `mult_law` would be worse than an honest
  open).
* **O7b — the gap `μ ∈ (3/8, 1/2)`.** Multistability is proved on `(0, 3/8]`
  (`ws9_multistable_interval`) and uniqueness on `(1/2, 1]` (`ws10_center_unique_above`);
  the open interval `(3/8, 1/2)` — where the contraction factor `2(1−μ)` exceeds 1 but no
  multistability witness is exhibited — remains genuinely open, as does the exact
  bifurcation boundary (a surface with no closed form). Recorded, not laundered.
-/

end Series03.WS10
