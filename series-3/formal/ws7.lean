/-
`series-3/formal/ws7.lean`

WS7 (`series-3/spec/ws7/04-charter-design-review.md`, v3): **non-collapse — the
collector.** WS7 gathers the shared `(F, κ, μ, #Q)` parameter and retro-validates
that one concrete tuple discharges the upstream "for κ infinite regular" theorems;
it owns the richness/plurality floors and the dynamical-non-collapse axis, and
reports the genuinely-open pieces as typed obligations rather than laundering them.

Built on `ws2`/`ws4`/`ws5`/`ws6` (imported, axiom-free). Adapts to the **actual**
upstream signatures (see the honesty note below).

## Outcome: class deferred to Lemma B on the dynamical axis; collector duties explicit

* **Static band (C1) — Discharged (witness form).** `ws7_static_band`: ≥2 distinct
  states (`ws2_nondegenerate`), no maximal state (`ws6_no_maximal`), weak-pullback
  preservation (`ws2_weak_pullback`) — the (vii) structural floor + §3.7 no-maximal
  face, assembled.
* **Retro-validation (C5) — Discharged at one tuple, `#Q ≤ κ` recorded.**
  `ws7_retro_validate`: at a concrete `(κ₀, μ, Łₙ)` with `hQsmall : #Łₙ ≤ κ₀`
  *proved* (`luk_card_le`), the WS2 characterization, no-maximal, WS6 split, and the
  WS4 graded-law coherence all hold. The `#Q` side-condition is a typed premise, not
  silent vacuity (v3 fix 4).
* **Richness floor split (v3 fix 5).** `RichnessWitness` (≥2 distinct states) is
  Discharged; `GeneralBranching` (branching-≥2 everywhere — the (iv)-blocking floor
  WS3's sharp non-triviality needs) is a **named open obligation**
  (`RichnessGeneralStatus.open_iv_blocking`), never derived from the witness.
* **Ambient-category scope (v3 fix 6).** `CarrierScope.set_cofix_only`: WS7 speaks to
  §3.7's no-maximal face and (vii), **not** the zero-object face or criterion (vi)
  (WS6-owned, open across a possible category split).
* **Dynamical axis (C3) — deferred to Lemma B.** `DynamicalStatus` names the four
  terminal shapes plus the current `deferred` state. The convergence *theorem* is the
  Banach step given a contraction (`ws7_attention_fixed_point`, via
  `ws5_attention_converges`); whether the replicator-mutator actually contracts on the
  floored simplex is **Lemma B**, the one genuinely open analytic obligation — left
  open, exactly as the design's terminal status states.
* **Assembly.** `WS7NonCollapse` / `ws7_band_and_retro` — named `ws7_band_and_retro`,
  **not** `ws7_resolved`: the dynamical field is `deferred`, richness-general is
  `open_iv_blocking`, and the zero-object face is out of scope. The WS4/WS5/WS6
  naming discipline, transplanted.

All `sorry`-free and **axiom-free** beyond Mathlib's standard
`propext`/`Classical.choice`/`Quot.sound` (verify `#print axioms ws7_band_and_retro`).

## Honesty note (adaptation to the ACTUAL upstream API)

The v3 design was written against an idealized upstream. Faithful adaptations:
(1) my `GradedWeakLawCoherence`/`ws4_graded_law_coherence` (ws4.lean) do **not**
thread `hQsmall`; so `ws7_retro_validate` carries `hQsmall` as a recorded premise
(and re-exports it in the conclusion) rather than feeding it into the coherence — the
`#Q` duty is still visible and typed. (2) The Łukasiewicz witness is `Luk n`
(`Fin (n+1)`), so `#Q ≤ κ` is `Cardinal.mk (Luk n) ≤ κ`, discharged by `luk_card_le`.
(3) `GeneralBranching` is phrased with the actual carrier API (`(νPk κ).str`, distinct
successors) since on the terminal carrier bisimilarity is identity. (4) The
Łₙ-instantiated results fix `κ₀ : Cardinal.{0}` (as `ws4_graded_coherence_Luk` does),
since `Luk n : Type 0`. `κ.IsRegular` is genuinely consumed here (Banach/`hcard`).
-/
import ws6
import ws5
import ws4

universe u

open Cardinal Series3.WS1 Series3.WS2 Series3.WS4 Series3.WS5 Series3.WS6

namespace Series3.WS7

variable {κ : Cardinal.{u}}

/-! ## §2 Richness floors (v3 fix 5) -/

/-- (vii)-witness form — what `ws2_nondegenerate` already gives. Closed. -/
abbrev RichnessWitness (κ : Cardinal.{u}) : Prop := ∃ a b : (νPk κ).X, a ≠ b

/-- (iv)-blocking form — branching ≥ 2 everywhere, distinguishably. On the terminal
carrier bisimilarity is identity, so "distinguishable successors" is "distinct
successors". This is the general floor WS3's sharp `alg`-non-triviality consumes; it
is **not** implied by a single `a ≠ b` witness, and is left OPEN. -/
def GeneralBranching (κ : Cardinal.{u}) : Prop :=
  ∀ u : (νPk κ).X, ∃ x y, x ∈ ((νPk κ).str u).1 ∧ y ∈ ((νPk κ).str u).1 ∧ x ≠ y

/-! ## §3 C1 — the static band (Discharged, witness form) -/

/-- **C1 (Discharged, witness form).** The static non-collapse band: ≥2 distinct
states, no maximal state, and weak-pullback preservation — assembled from the
imported upstream facts. Note `ws2_nondegenerate` discharges the *witness* form only;
it does **not** discharge `GeneralBranching` (v3 fix 5). -/
theorem ws7_static_band (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) :
    RichnessWitness κ
  ∧ (∀ u : (νPk κ).X, ¬ IsMaximal u)
  ∧ PkPreservesWeakPullback κ :=
  ⟨ws2_nondegenerate hinf, fun u => ws6_no_maximal hcard u, ws2_weak_pullback⟩

/-! ## §3 C5 — retro-validation, tuple `(F, κ, μ, #Q)` (v3 fix 4) -/

/-- `#Łₙ = n+1 < ℵ₀ ≤ κ`: the shape-count side condition is **proved** for the finite
Łukasiewicz witness, not assumed (v3 fix 4). -/
theorem luk_card_le (n : ℕ) {κ₀ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ₀) :
    Cardinal.mk (Luk n) ≤ κ₀ := by
  have h : Cardinal.mk (Luk n) < Cardinal.aleph0 := by
    show Cardinal.mk (Fin (n + 1)) < Cardinal.aleph0
    rw [Cardinal.mk_fin]; exact Cardinal.nat_lt_aleph0 _
  exact le_of_lt (lt_of_lt_of_le h hinf)

/-- **C5 (Discharged at one tuple).** The collector spine: at a concrete regular `κ₀`
with `hcard` and the finite witness `Łₙ` (`n ≥ 2`), the upstream deliverables all
survive — WS2 characterization, no-maximal, the WS6 split, and the WS4 graded-law
coherence. The `#Q ≤ κ₀` side condition is a **typed premise** (`hQsmall`),
re-exported in the conclusion so it cannot be read as silently absorbed (v3 fix 4). -/
theorem ws7_retro_validate
    (κ₀ : Cardinal.{0}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X)
    (n : ℕ) (_hn : 2 ≤ n)
    (hQsmall : Cardinal.mk (Luk n) ≤ κ₀) :
    Nonempty (WS2Characterization κ₀)
  ∧ (∀ u : (νPk κ₀).X, ¬ IsMaximal u)
  ∧ Nonempty (WS6NoPoles κ₀)
  ∧ Nonempty (GradedWeakLawCoherence (Luk n) κ₀ hreg)
  ∧ Cardinal.mk (Luk n) ≤ κ₀ :=
  ⟨ws2_characterization hreg.aleph0_le hreg,
   fun u => ws6_no_maximal hcard u,
   ws6_split_and_no_maximal hreg.aleph0_le hcard,
   ws4_graded_law_coherence (Luk n) hreg,
   hQsmall⟩

/-! ## §4 Status types for the assembly (v3 fixes 4, 5, 6) -/

/-- The `#Q ≤ κ` collector duty as a first-class inspectable field (v3 fix 4). Both
constructors carry the proof; the distinction records provenance, not strength. -/
inductive QSmallRatified (κ : Cardinal.{u})
  | discharged (Q : Type u) (h : Cardinal.mk Q ≤ κ)
  | premised (Q : Type u) (h : Cardinal.mk Q ≤ κ)

/-- The (iv)-blocking richness floor: proved, or an explicitly-open tagged obligation
(v3 fix 5). There is deliberately **no** constructor deriving this from
`RichnessWitness`. -/
inductive RichnessGeneralStatus (κ : Cardinal.{u})
  | discharged (h : GeneralBranching κ)
  | open_iv_blocking

/-- Reserved bridge obligation (WS6-owned, open): whether the zero-object face and the
Set/Cofix carrier live in one ambient category. Kept abstract; WS7 does not settle it. -/
def SingleCategoryBridge (κ : Cardinal.{u}) : Prop := ws6_no_faithful_zero_host κ

/-- Ambient-category scope boundary (v3 fix 6): WS7 covers the §3.7 no-maximal face +
(vii), NOT the zero-object face / (vi). The `unified_category` case is reserved and
requires settling the WS6 bridge. -/
inductive CarrierScope (κ : Cardinal.{u})
  | set_cofix_only
  | unified_category (h : SingleCategoryBridge κ)

/-- The four nameable terminal shapes of the dynamical axis (v3 fix 3) plus the
current `deferred` state. Over an arbitrary admissible band `A ⊆ ℝ`. The resolved
shapes are claims about the band; `deferred` is the honest current label — the class
is routed to Lemma B (the open contraction obligation), not asserted. -/
inductive DynamicalStatus (A : Set ℝ)
  | discharged            -- contraction on all of `A`: converges
  | impossible            -- provably expansive on `A`: no fixed point
  | partial_band          -- converges only on a proper sub-band (interval/disconnected)
  | deferred              -- class open, routed to Lemma B (the current WS7 state)

/-! ## §4 The assembly -/

/-- The WS7 non-collapse bundle. Criterion (iv)'s richness floor and the dynamical
axis are carried as **typed status fields**, not discharged-looking proofs; the
zero-object face is out of scope. -/
structure WS7NonCollapse (κ : Cardinal.{u}) (μ : ℝ) (A : Set ℝ) where
  hinf             : ℵ₀ ≤ κ
  hcard            : κ ≤ Cardinal.mk (νPk κ).X
  richness_witness : RichnessWitness κ
  no_maximal       : ∀ u : (νPk κ).X, ¬ IsMaximal u
  weak_pb          : PkPreservesWeakPullback κ
  plurality        : 0 < μ
  q_small          : QSmallRatified κ
  richness_general : RichnessGeneralStatus κ
  carrier_category : CarrierScope κ
  dynamics         : DynamicalStatus A

/-- **The WS7 collector deliverable.** At a concrete regular `κ₀`, mutation floor
`μ > 0`, admissible band `A`, and the finite witness `Łₙ`, the non-collapse bundle
holds — with `#Q` discharged, the (iv)-blocking floor held OPEN, the scope limited to
Set/Cofix, and the dynamical class `deferred` to Lemma B. Named `ws7_band_and_retro`,
**not** `ws7_resolved`: three collector duties are visible and open, not laundered. -/
theorem ws7_band_and_retro
    (κ₀ : Cardinal.{0}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X)
    (μ : ℝ) (hμ : 0 < μ) (A : Set ℝ) (n : ℕ) (_hn : 2 ≤ n) :
    Nonempty (WS7NonCollapse κ₀ μ A) :=
  ⟨{ hinf             := hreg.aleph0_le
   , hcard            := hcard
   , richness_witness := ws2_nondegenerate hreg.aleph0_le
   , no_maximal       := fun u => ws6_no_maximal hcard u
   , weak_pb          := ws2_weak_pullback
   , plurality        := hμ
   , q_small          := QSmallRatified.discharged (Luk n) (luk_card_le n hreg.aleph0_le)
   , richness_general := RichnessGeneralStatus.open_iv_blocking
   , carrier_category := CarrierScope.set_cofix_only
   , dynamics         := DynamicalStatus.deferred }⟩

/-! ## §2–3 The dynamical spine (C3): the floored simplex and the Banach step

The convergence *class* is deferred to Lemma B (whether the replicator-mutator
contracts). What is proved here: the floored simplex is a nonempty-when-inhabited
complete metric space, the mutation step is a total self-map of it (invariance, B0),
the step is Lipschitz with constant `(1−μ)·L_R μ` **given** a `SelectionLipschitz`
bound (B/A), and Banach then yields the unique fixed point (via
`ws5_attention_converges`). Lemma B — the existence of a `SelectionLipschitz` with
`(1−μ)·L_R μ < 1` — is the one genuinely open analytic obligation, left open. -/

section Dynamics
open scoped NNReal
variable {S : Type u} [Fintype S]

/-- The `μ`-floored probability simplex on `S` (design §2). -/
def FlooredSimplex (S : Type u) [Fintype S] (μ : ℝ) (unif : S → ℝ) : Type u :=
  { w : S → ℝ // (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) }

instance (μ : ℝ) (unif : S → ℝ) : MetricSpace (FlooredSimplex S μ unif) :=
  inferInstanceAs (MetricSpace { w : S → ℝ // (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) })

/-- The floored simplex is complete: it is a closed subset of the complete `S → ℝ`
(closed floor half-spaces ∩ the sum-one hyperplane). -/
instance (μ : ℝ) (unif : S → ℝ) : CompleteSpace (FlooredSimplex S μ unif) := by
  have hcl : IsClosed { w : S → ℝ | (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) } := by
    rw [Set.setOf_and]
    apply IsClosed.inter
    · rw [Set.setOf_forall]
      exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
    · exact isClosed_eq (continuous_finset_sum _ fun r _ => continuous_apply r) continuous_const
  exact hcl.completeSpace_coe

/-- The floor region: weightings dominating the `μ`-scaled uniform reference. -/
def floorRegion (μ : ℝ) (unif : S → ℝ) : Set (S → ℝ) := { w | ∀ r, μ * unif r ≤ w r }

/-- A selection map: nonnegativity- and sum-preserving (design §2). -/
structure SelectionMap (S : Type u) [Fintype S] (unif : S → ℝ) where
  R       : (S → ℝ) → (S → ℝ)
  nonneg  : ∀ w, (∀ r, 0 ≤ w r) → ∀ r, 0 ≤ R w r
  sum_one : ∀ w, (∑ r, w r = 1) → (∑ r, R w r = 1)

/-- One feed/starve step: `(1−μ)·(selection) + μ·(uniform)` (design §2). -/
def mutationStep (μ : ℝ) (unif : S → ℝ) (sel : SelectionMap S unif) :
    (S → ℝ) → (S → ℝ) :=
  fun w r => (1 - μ) * sel.R w r + μ * unif r

/-- The selection map is Lipschitz on the floor region, with an `L_R` tied to `μ`
through `floorRegion μ` membership (design §2 fix 1). Its *existence with*
`(1−μ)·L_R μ < 1` is **Lemma B**, the open obligation. -/
structure SelectionLipschitz (S : Type u) [Fintype S] (unif : S → ℝ)
    (sel : SelectionMap S unif) where
  L_R   : ℝ → ℝ≥0
  bound : ∀ (μ : ℝ), 0 < μ → μ ≤ 1 →
            ∀ w ∈ floorRegion μ unif, ∀ w' ∈ floorRegion μ unif,
              dist (sel.R w) (sel.R w') ≤ (L_R μ) * dist w w'

/-- **B0 — invariance (Discharged).** The mutation step maps the floored simplex into
itself: the floor survives because `(1−μ)·(sel.R w r) ≥ 0`, and the sum is preserved
because selection and uniform are both probability vectors. -/
lemma mutationStep_maps_into (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (w : S → ℝ)
    (hw : ∀ r, μ * unif r ≤ w r) (hwsum : ∑ r, w r = 1) :
    (∀ r, μ * unif r ≤ mutationStep μ unif sel w r)
  ∧ (∑ r, mutationStep μ unif sel w r = 1) := by
  have hwnn : ∀ r, 0 ≤ w r := fun r => le_trans (mul_nonneg hμ0 (hunif_nonneg r)) (hw r)
  refine ⟨fun r => ?_, ?_⟩
  · have hRnn : 0 ≤ sel.R w r := sel.nonneg w hwnn r
    have : 0 ≤ (1 - μ) * sel.R w r := mul_nonneg (by linarith) hRnn
    simp only [mutationStep]; linarith
  · simp only [mutationStep, Finset.sum_add_distrib, ← Finset.mul_sum, sel.sum_one w hwsum,
      hunif_sum]
    ring

/-- The mutation step as a self-map of the floored simplex (needs B0). -/
def mutT (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) : FlooredSimplex S μ unif → FlooredSimplex S μ unif :=
  fun w => ⟨mutationStep μ unif sel w.1,
    mutationStep_maps_into μ hμ0 hμ1 unif hunif_nonneg hunif_sum sel w.1 w.2.1 w.2.2⟩

/-- **A — Lipschitz bound (Discharged given `sl`).** `Lip (mutT) ≤ (1−μ)·L_R μ` in the
sup metric: the `μ·unif` term cancels in the difference, leaving `(1−μ)` times the
selection's Lipschitz bound. -/
lemma mutation_lipschitz (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (w w' : FlooredSimplex S μ unif) :
    dist (mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel w)
         (mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel w')
      ≤ ((1 - μ) * (sl.L_R μ)) * dist w w' := by
  have h1μ : (0 : ℝ) ≤ 1 - μ := by linarith
  have hCnn : 0 ≤ ((1 - μ) * (sl.L_R μ)) * dist w w' :=
    mul_nonneg (mul_nonneg h1μ (sl.L_R μ).coe_nonneg) dist_nonneg
  rw [Subtype.dist_eq]
  rw [dist_pi_le_iff hCnn]
  intro r
  have e : ∀ v : FlooredSimplex S μ unif,
      (mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel v).1 r
        = (1 - μ) * sel.R v.1 r + μ * unif r := fun _ => rfl
  rw [e w, e w', Real.dist_eq,
    show ((1 - μ) * sel.R w.1 r + μ * unif r) - ((1 - μ) * sel.R w'.1 r + μ * unif r)
       = (1 - μ) * (sel.R w.1 r - sel.R w'.1 r) by ring,
    abs_mul, abs_of_nonneg h1μ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h1μ
  calc |sel.R w.1 r - sel.R w'.1 r| = dist (sel.R w.1 r) (sel.R w'.1 r) := (Real.dist_eq _ _).symm
    _ ≤ dist (sel.R w.1) (sel.R w'.1) := dist_le_pi_dist _ _ r
    _ ≤ (sl.L_R μ) * dist w.1 w'.1 := sl.bound μ hμ0 hμ1 w.1 w.2.1 w'.1 w'.2.1
    _ = (sl.L_R μ) * dist w w' := by rw [Subtype.dist_eq]

/-- **Contraction (Discharged given the Lemma-B premise `hfloor_contr`).** -/
theorem ws7_mutation_contracts (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (hfloor_contr : (1 - μ) * (sl.L_R μ) < 1) :
    ∃ K : ℝ≥0, K < 1 ∧ ∀ w w' : FlooredSimplex S μ unif,
      dist (mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel w)
           (mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel w')
        ≤ (K : ℝ) * dist w w' := by
  refine ⟨⟨(1 - μ) * (sl.L_R μ), mul_nonneg (by linarith) (sl.L_R μ).coe_nonneg⟩, ?_, ?_⟩
  · exact_mod_cast hfloor_contr
  · intro w w'
    exact mutation_lipschitz μ hμ0 hμ1 unif hunif_nonneg hunif_sum sel sl w w'

/-- **The Banach step (Discharged given a contraction).** On the nonempty complete
floored simplex, a contracting mutation step has a unique fixed point — via
`ws5_attention_converges`. The contraction (Lemma B) stays a hypothesis. -/
theorem ws7_attention_fixed_point (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (unif : S → ℝ)
    (hunif_nonneg : ∀ r, 0 ≤ unif r) (hunif_sum : ∑ r, unif r = 1)
    (sel : SelectionMap S unif) (sl : SelectionLipschitz S unif sel)
    (hfloor_contr : (1 - μ) * (sl.L_R μ) < 1) [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif,
      mutT μ (le_of_lt hμ0) hμ1 unif hunif_nonneg hunif_sum sel p = p := by
  obtain ⟨K, hK, hlip⟩ :=
    ws7_mutation_contracts μ hμ0 hμ1 unif hunif_nonneg hunif_sum sel sl hfloor_contr
  exact ws5_attention_converges _ K hK hlip

end Dynamics

end Series3.WS7
