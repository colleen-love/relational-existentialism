/-
`series-12/formal/Series12/ws2.lean`

WS2 - Knowing: finite attention, and the opening inhabited (the plurality). Series 12.

Consumes WS1 (the carrier, the opening). Adds the formalizable side of knowing: finite attention
(subtractive, plural, no total attention), the plurality predicate `Many`, and the concrete `dir := rank`
witness on a four-state carrier where a reified relatum CARRYING a reified constituent (`cW = reifyW {bW}`)
and a base relatum (`aW`) are genuinely plain-bisimilar (the collapse engine) yet separated at the labelled
level by their tower RANK, on a carrier where rank is NON-INJECTIVE (`aW`, `aW'` share rank 0), the
separation reinstated as the GENERAL theorem `ws2_many_general` (design-review-1 Finding 1). And without any
import, the One (`ws2_import_theorem_static`). The distinction is free (`¬ Recoverable`), its certificate.

Design docs: `series-12/spec/ws2-design.md`, `series-12/spec/ws4-witness-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import Series12.ws1

universe u

namespace Series12.WS2

open Series12.WS1 Cardinal

set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

variable {κ : Cardinal.{u}}

/-! ## Finite attention (the formalizable side of knowing) -/

/-- **Finite attention.** A hold on the labelled tower whose reading is FINITE. -/
structure FiniteAttention {Q X : Type u} (dest : X → LkObj κ Q X) : Type u where
  focus    : X
  reads    : Set X
  fin      : reads.Finite
  grounded : focus ∈ reads ∧ ∀ z ∈ reads, SReaches (plainOf dest) focus z

/-- **What an attention distinguishes**: plain-bisimilar (the quotient is blind) yet not label-bisimilar. -/
def AttentionDistinguishes {Q X : Type u} (dest : X → LkObj κ Q X) (x y : X) : Prop :=
  (∃ R, IsBisim (plainOf dest) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL dest R ∧ R x y)

/-- **Real for an attention.** -/
def RealFor {Q X : Type u} (dest : X → LkObj κ Q X) (att : FiniteAttention dest) (x : X) : Prop :=
  ∃ y, y ∈ att.reads ∧ AttentionDistinguishes dest x y

/-- **Total attention = self-total hold (the pin).** -/
def TotalAttention {X : Type u} {dest : X → PkObj κ X}
    (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop := SelfTotal insp t

/-- **(NT) THE IMPOSSIBILITY.** No self-total hold: no attention holds the whole. -/
theorem ws3_no_total_attention {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    ¬ ∃ t, TotalAttention insp t :=
  ws1_no_self_total_hold dest insp

/-- **D1 - attention is subtractive and never total.** -/
theorem ws2_attention_subtractive {X : Type u} (dest : X → PkObj κ X) (insp : Hold dest → HoldPred dest) :
    (¬ ∃ t, TotalAttention insp t) ∧ (∀ h : Hold dest, insp h ≠ residue insp) :=
  ⟨ws3_no_total_attention dest insp, ws2_residue_distinct dest insp⟩

/-! ## The plurality predicate `Many` (defined once, README §2.8) -/

/-- **The plurality predicate.** The many is real over a labelled lift `destL` iff SOME pair is separated
the two-sided way: plain-bisimilar yet not label-bisimilar. -/
def Many {Q X : Type u} (destL : X → LkObj κ Q X) : Prop :=
  ∃ x y : X, (∃ R, IsBisim (plainOf destL) R ∧ R x y) ∧ (¬ ∃ R, IsBisimL destL R ∧ R x y)

/-! ## The four-state `dir := rank` witness carrier -/

/-- The witness carrier: two base relata `aW`, `aW'` (rank 0), a reified relatum `bW` (rank 1), and a
reified relatum `cW` (rank 2) carrying the reified constituent `bW`. Realized as `ULift (Fin 4)` so it lands
concretely in `Type u` (like Series 11's `ULift Bool`), with `DecidableEq`/`Fintype`/`Finite`. -/
abbrev WCar : Type u := ULift.{u} (Fin 4)

def aW  : WCar := ⟨0⟩   -- a BASE relatum (rank 0)
def aW' : WCar := ⟨1⟩   -- a SECOND base relatum (rank 0): makes rank NON-INJECTIVE
def bW  : WCar := ⟨2⟩   -- a reified relatum (rank 1), = reifyW {aW}
def cW  : WCar := ⟨3⟩   -- a reified relatum (rank 2) CARRYING the reified constituent bW, = reifyW {bW}

/-- The plain relating: `aW`, `aW'` self-loop; `bW → aW`; `cW → bW`. All four are `SHNE`. -/
noncomputable def destW (hinf : ℵ₀ ≤ κ) : WCar → PkObj κ WCar := fun x =>
  if x = aW then toPk hinf {aW}
  else if x = aW' then toPk hinf {aW'}
  else if x = bW then toPk hinf {aW}     -- dest bW = {aW} = dest (reifyW {aW})
  else toPk hinf {bW}                    -- dest cW = {bW} = dest (reifyW {bW})

/-- The pattern reified into `bW` (the model-pair edge pattern: `aW ∈ sW.1`, `bW = reifyW sW`). -/
noncomputable def sW  (hinf : ℵ₀ ≤ κ) : PkObj κ WCar := toPk hinf {aW}
/-- The pattern reified into `cW` (the plurality pattern: `bW ∈ sW₂.1`, `cW = reifyW sW₂`). -/
noncomputable def sW₂ (hinf : ℵ₀ ≤ κ) : PkObj κ WCar := toPk hinf {bW}

/-- A section, defined pointwise at `{aW}` and `{bW}` (total `IsReify` is unsatisfiable here, disclosed). -/
noncomputable def reifyW (hinf : ℵ₀ ≤ κ) : PkObj κ WCar → WCar :=
  fun s => if s.1 = {aW} then bW else if s.1 = {bW} then cW else aW

/-- The RANK direction: position in the tower over `Ω₀ = {aW, aW'}`. NON-INJECTIVE at rank 0. -/
def rankW : WCar → ℕ := fun x =>
  if x = aW then 0 else if x = aW' then 0 else if x = bW then 1 else 2

/-- **The general rank-labelled lift.** Every relatum broadcasts its rank on its outgoing edges. -/
noncomputable def rankLift {X : Type u} (dest : X → PkObj κ X) (rank : X → ℕ) :
    X → LkObj κ (ULift.{u} ℕ) X :=
  fun x => PkMap κ (fun z => ((⟨rank x⟩ : ULift.{u} ℕ), z)) (dest x)

/-- The labelled lift of the witness (`dir := rank`). -/
noncomputable def destWL (hinf : ℵ₀ ≤ κ) : WCar → LkObj κ (ULift.{u} ℕ) WCar :=
  rankLift (destW hinf) rankW

/-! ## Carrier lemmas -/

@[simp] lemma aW_ne_aW' : aW ≠ aW' := by decide
@[simp] lemma bW_ne_aW  : bW ≠ aW := by decide

-- The `destW` values reduce by the kernel (WCar has a computable `DecidableEq`), so `rfl` suffices.
lemma destW_aW (hinf : ℵ₀ ≤ κ) : destW hinf aW = toPk hinf {aW} := rfl
lemma destW_bW (hinf : ℵ₀ ≤ κ) : destW hinf bW = toPk hinf {aW} := rfl
lemma destW_cW (hinf : ℵ₀ ≤ κ) : destW hinf cW = toPk hinf {bW} := rfl

lemma destW_ne_empty (hinf : ℵ₀ ≤ κ) : ∀ v : WCar, (destW hinf v).1 ≠ ∅ := by
  intro v
  simp only [destW]
  split_ifs <;> · rw [toPk_val]; exact Set.singleton_ne_empty _

/-- Every witness state is `SHNE` (all successor sets are nonempty singletons). -/
lemma ws_SHNE (hinf : ℵ₀ ≤ κ) (x : WCar) : SHNE (destW hinf) x :=
  fun v _ => destW_ne_empty hinf v

-- The `reifyW` values use classical `Set`-equality (opaque), so they need explicit `if_pos`/`if_neg`.
lemma reifyW_sW (hinf : ℵ₀ ≤ κ) : reifyW hinf (sW hinf) = bW := by
  have hc : (sW hinf).1 = {aW} := rfl
  simp only [reifyW]; rw [if_pos hc]

lemma reifyW_sW₂ (hinf : ℵ₀ ≤ κ) : reifyW hinf (sW₂ hinf) = cW := by
  have hc1 : ¬ ((sW₂ hinf).1 = {aW}) := by
    show ¬ (({bW} : Set WCar) = {aW})
    rw [Set.singleton_eq_singleton_iff]; exact bW_ne_aW
  have hc2 : (sW₂ hinf).1 = {bW} := rfl
  simp only [reifyW]; rw [if_neg hc1, if_pos hc2]

/-- Pointwise reification at `sW` and `sW₂` (what the lemmas consume; total `IsReify` unsatisfiable). -/
lemma ws_reify_pointwise_sW (hinf : ℵ₀ ≤ κ) : destW hinf (reifyW hinf (sW hinf)) = sW hinf := by
  rw [reifyW_sW hinf]; exact destW_bW hinf
lemma ws_reify_pointwise_sW₂ (hinf : ℵ₀ ≤ κ) : destW hinf (reifyW hinf (sW₂ hinf)) = sW₂ hinf := by
  rw [reifyW_sW₂ hinf]; exact destW_cW hinf

lemma aW_mem_sW (hinf : ℵ₀ ≤ κ) : aW ∈ (sW hinf).1 := by
  show aW ∈ ({aW} : Set WCar); exact Set.mem_singleton _
lemma bW_mem_sW₂ (hinf : ℵ₀ ≤ κ) : bW ∈ (sW₂ hinf).1 := by
  show bW ∈ ({bW} : Set WCar); exact Set.mem_singleton _

/-- **plainOf destWL = destW**: the plain quotient forgets the rank. -/
lemma ws_plainOf (hinf : ℵ₀ ≤ κ) : plainOf (destWL hinf) = destW hinf := by
  funext x
  apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨rankW x⟩ : ULift.{u} ℕ), z)) '' (destW hinf x).1) = (destW hinf x).1
  rw [Set.image_image]
  simp

/-- **Rank is NON-INJECTIVE** (the anti-point-indicator certificate, Finding 1). -/
theorem ws_witness_rank_noninjective : rankW aW = rankW aW' ∧ aW ≠ aW' := ⟨rfl, by decide⟩

/-! ## The general rank-separation (Finding 1, reinstated) -/

/-- **THE GENERAL RANK-SEPARATION.** For any `dest`, `reify`, `rank` where a reified relatum ranks strictly
above its constituents, any pattern `s` whose reified relatum `reify s` carries a constituent `w₀` of rank
at least 1, and any base relatum `y` of rank 0, the reified relatum and the base relatum are plain-bisimilar
(the collapse engine) yet NOT label-bisimilar over the rank-labelled lift. `reify`/`rank`/base-rank-0 are
load-bearing in the STATEMENT. -/
theorem ws2_many_general {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (rank : X → ℕ)
    (s : PkObj κ X) (hs : s.1 ≠ ∅) (hpt : dest (reify s) = s)
    (w₀ : X) (hw₀ : w₀ ∈ s.1) (hw₀rank : 1 ≤ rank w₀)
    (hstep : ∀ w ∈ s.1, rank w < rank (reify s))
    (y : X) (hyrank : rank y = 0)
    (hshne_r : SHNE dest (reify s)) (hshne_y : SHNE dest y) :
    (∃ R, IsBisim dest R ∧ R (reify s) y)
  ∧ (¬ ∃ R, IsBisimL (rankLift dest rank) R ∧ R (reify s) y) := by
  refine ⟨ws1_atomless_bisim dest (reify s) y hshne_r hshne_y, ?_⟩
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR (reify s) y hRel
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hs
  have hedge : ((⟨rank (reify s)⟩ : ULift.{u} ℕ), z) ∈ (rankLift dest rank (reify s)).1 := by
    show ((⟨rank (reify s)⟩ : ULift.{u} ℕ), z)
        ∈ (fun w => ((⟨rank (reify s)⟩ : ULift.{u} ℕ), w)) '' (dest (reify s)).1
    rw [hpt]; exact ⟨z, hz, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  have hq1 : q.1 = (⟨rank y⟩ : ULift.{u} ℕ) := by
    have hmem : q ∈ (fun w => ((⟨rank y⟩ : ULift.{u} ℕ), w)) '' (dest y).1 := hq
    obtain ⟨w, _, hw⟩ := hmem; rw [← hw]
  rw [hq1] at hfst
  have hfst' : (⟨rank (reify s)⟩ : ULift.{u} ℕ) = ⟨rank y⟩ := hfst
  have heq : rank (reify s) = rank y := congrArg ULift.down hfst'
  have hlt : rank w₀ < rank (reify s) := hstep w₀ hw₀
  omega

/-! ## The plurality witness (the concrete pair `cW` vs `aW`, an instance of the general theorem) -/

/-- **REIFICATION LOAD-BEARING.** The separated relatum `cW` is a genuine reified relatum, carrying the
reified constituent `bW` (rank 1), `dest (reify sW₂) = sW₂` pointwise. -/
theorem ws2_reification_loadbearing (hinf : ℵ₀ ≤ κ) :
    cW = reifyW hinf (sW₂ hinf)
  ∧ destW hinf (reifyW hinf (sW₂ hinf)) = sW₂ hinf
  ∧ bW ∈ (sW₂ hinf).1 ∧ 1 ≤ rankW bW :=
  ⟨(reifyW_sW₂ hinf).symm, ws_reify_pointwise_sW₂ hinf, bW_mem_sW₂ hinf, by decide⟩

/-- **THE PLURALITY (`Many`, on a genuine tower-distinction).** `cW` (a reified relatum carrying the reified
constituent `bW`) and the base relatum `aW` are plain-bisimilar (`ws1_atomless_bisim`) yet rank-separated,
an INSTANCE of `ws2_many_general`. -/
theorem ws2_many_witness (hinf : ℵ₀ ≤ κ) : Many (destWL hinf) := by
  refine ⟨cW, aW, ?_, ?_⟩
  · rw [ws_plainOf hinf]
    exact ws1_atomless_bisim (destW hinf) cW aW (ws_SHNE hinf cW) (ws_SHNE hinf aW)
  · have hgen :=
      (ws2_many_general (destW hinf) (reifyW hinf) rankW (sW₂ hinf)
        (by simp only [sW₂, toPk_val]; exact Set.singleton_ne_empty _)
        (ws_reify_pointwise_sW₂ hinf)
        bW (bW_mem_sW₂ hinf) (by decide)
        (by
          intro w hw
          rw [reifyW_sW₂ hinf]
          have hwb : w = bW := by
            simpa only [sW₂, toPk_val, Set.mem_singleton_iff] using hw
          subst hwb; decide)
        aW (by decide)
        (by rw [reifyW_sW₂ hinf]; exact ws_SHNE hinf cW)
        (ws_SHNE hinf aW)).2
    rw [reifyW_sW₂ hinf] at hgen
    exact hgen

/-! ## Without an import, the One; and the distinction free -/

/-- **WITHOUT AN IMPORT, THE ONE.** A plain, behaviorally-identified, atomless coalgebra is a subsingleton. -/
theorem ws2_no_import_is_one {X : Type u} (dest : X → PkObj κ X)
    (hbehav : BehaviorallyIdentified dest) (hatom : ∀ x, SHNE dest x) : Subsingleton X :=
  ws2_import_theorem_static dest hbehav hatom

/-- **THE DISTINCTION IS FREE (its certificate, not its defect).** The rank-separation is not recoverable
from the plain relating: an import, which by Series 07 is what a genuine atomless distinction MUST be. -/
theorem ws2_distinction_free (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (destWL hinf) := by
  intro hrec
  obtain ⟨_, _, hbisim, hsep⟩ := ws2_many_witness hinf
  exact hsep (ws4_recoverable_not_import (destWL hinf) hrec _ _ hbisim)

end Series12.WS2
