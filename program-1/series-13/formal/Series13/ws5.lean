/-
`series-13/formal/Series13/ws5.lean`

WS5 - The verdict, and the audit folded in. Series 13, the computed verdict.

Consumes WS1-WS4. The verdict is COMPUTED (never hand-set): `verdictOfFit` branches on a `FitFork` discharged
by CASING ON THE CARRIER (the hold count). On a carrier with a second hold the DUAL branch fires
(`ws5_verdict_eq`, the TOTAL target having been refuted by `outWit`); on a single-hold carrier the TOTAL
branch fires (`ws5_verdict_degenerate`). The `Audit` has one field per WS1-WS4 payoff plus the fork; the
audit checks (genuine-connection, exogeneity, structural-defect) are theorems, and the fork-open and
names-not-terms checks pass by inspection.

The layer-stability OPEN (single-layer scope): the carrier is FLAT (no reification tower), so this is a
flat-layer verdict; whether the mint commutes with reification, and whether a tower-carrying import survives
outside the mint's image up to `≈`, is left OPEN. This note is prose only, never a proof term; it bounds the
claim and does not sort the fork.

Design doc: `series-13/spec/ws5-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series13.ws4

universe u

namespace Series13.WS5

open Series13.WS1 Series13.WS2 Series13.WS3 Series13.WS4 Cardinal Classical

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- The verdict type. -/
inductive Series13Verdict
  | Dual | Total | Disconnected | Partial | Refuted | Circular
  deriving DecidableEq

/-- **The fit fork (data-level).** WHICH outcome the code discharged, each constructor carrying its proof
at the honest resolution (mintability up to `≈`). -/
inductive FitFork {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) : Type u
  | defectStructural (h₁ : Hold dest) (hne : h₁ ≠ h₀)
      (hd : ¬ Recoverable (coalg hinf (outWit h₀ h₁))
            ∧ ¬ ∃ insp, labEquiv h₀ (mintL h₀ insp) (outWit h₀ h₁))
  | mintSurjective
      (hs : ∀ b : Lab dest h₀, (¬ Recoverable (coalg hinf b)) → ∃ insp, labEquiv h₀ (mintL h₀ insp) b)
  -- `ordersTrivial` (DISCONNECTED) carries the inspection-order trivialities only; a full DISCONNECTED
  -- report would add the labelled-order disjuncts (`series-review-1.md` SR1-10). Unreached here (WS1 landed
  -- non-trivial), so latent; reserved for a build where an order proves vacuous.
  | ordersTrivial
      (ht : (∀ a b : Insp dest, a ≤ b) ∨ (∀ a b : Insp dest, a ≤ b → a = b))
  -- `perInstance` (PARTIAL) is a reserved hand-report constructor with no computable payload; `ws5_fork`
  -- never produces it (`series-review-1.md` SR1-9), so `Partial` is not computed on this build, only
  -- reachable by an explicit Partial report. `ws5_verdict_not_partial` is therefore true, if uninteresting.
  | perInstance (hp : True)

def verdictOfFit {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} {hinf : ℵ₀ ≤ κ} :
    FitFork dest h₀ hinf → Series13Verdict
  | .defectStructural _ _ _ => .Dual
  | .mintSurjective   _     => .Total
  | .ordersTrivial    _     => .Disconnected
  | .perInstance      _     => .Partial

/-- **The audit certificate.** Every field is a WS1-WS4 theorem, plus the `fork` (which outcome). -/
structure Audit {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) where
  orders_nontrivial :
      ((∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b))
    ∧ ((∃ a b : Lab dest h₀, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest h₀, ¬ a ≤ b)
        ∧ (∃ a b : Lab dest h₀, a.cT = b.cT ∧ ¬ a ≤ b))     -- the antitone reference position is load-bearing
  transport  : ∀ insp : Insp dest, ¬ Recoverable (coalg hinf (mintL h₀ insp))
  exogenous  : ∃ i₁ i₂ : Insp dest,
      plainOf (coalg hinf (mintL h₀ i₁)) = plainOf (coalg hinf (mintL h₀ i₂))
    ∧ mintL h₀ i₁ ≠ mintL h₀ i₂
  connection : GaloisConnection (mintL h₀ : Insp dest → Lab dest h₀) (readInsp h₀)
  roundtrip_defect :
      mintL h₀ (readInsp h₀ (bRefActive dest h₀)) ≤ bRefActive dest h₀
    ∧ ¬ (bRefActive dest h₀ ≤ mintL h₀ (readInsp h₀ (bRefActive dest h₀)))
  fork : FitFork dest h₀ hinf

/-- **The verdict branches on the certified fork.** -/
def verdict {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} {hinf : ℵ₀ ≤ κ}
    (cert : Audit dest h₀ hinf) : Series13Verdict := verdictOfFit cert.fork

/-- **The fork is discharged by casing on the carrier** (the hold count), so the verdict is COMPUTED. -/
noncomputable def ws5_fork {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    FitFork dest h₀ hinf :=
  if hsecond : ∃ h₁ : Hold dest, h₁ ≠ h₀ then
    .defectStructural hsecond.choose hsecond.choose_spec
      (ws4_mint_not_surjective h₀ hsecond.choose hsecond.choose_spec hinf)
  else
    .mintSurjective (ws4_mint_essentially_surjective_degenerate h₀
      (fun h => not_not.mp (fun hh => hsecond ⟨h, hh⟩)) hinf)

noncomputable def ws5_audit {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    Audit dest h₀ hinf where
  orders_nontrivial := ⟨ws1_orders_insp_nontrivial dest h₀, ws1_orders_lab_nontrivial dest h₀⟩
  transport := ws2_transport_forall h₀ hinf
  exogenous := ws2_mint_exogenous h₀ hinf
  connection := ws3_galois h₀
  roundtrip_defect := ws3_roundtrip_not_identity h₀
  fork := ws5_fork dest h₀ hinf

noncomputable def ws5_verdict {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    Series13Verdict := verdict (ws5_audit dest h₀ hinf)

/-- **The verdict on a carrier of interest is `Dual`, as a THEOREM** (computed): the second hold fires the
`defectStructural` branch, BECAUSE the TOTAL target was refuted by `outWit`. -/
theorem ws5_verdict_eq {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) : ws5_verdict dest h₀ hinf = Series13Verdict.Dual := by
  show verdictOfFit (ws5_fork dest h₀ hinf) = _
  unfold ws5_fork
  rw [dif_pos ⟨h₁, hne⟩]
  rfl

/-- **On a single-hold carrier the verdict is `Total`** (at the flat layer). -/
theorem ws5_verdict_degenerate {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest)
    (hone : ∀ h : Hold dest, h = h₀) (hinf : ℵ₀ ≤ κ) :
    ws5_verdict dest h₀ hinf = Series13Verdict.Total := by
  show verdictOfFit (ws5_fork dest h₀ hinf) = _
  unfold ws5_fork
  rw [dif_neg (by rintro ⟨h₁, hne⟩; exact hne (hone h₁))]
  rfl

/-! ### Falsifiability (on a carrier of interest) -/

theorem ws5_verdict_not_total {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) : ws5_verdict dest h₀ hinf ≠ Series13Verdict.Total := by
  rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide

theorem ws5_verdict_not_disconnected {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest)
    (hne : h₁ ≠ h₀) (hinf : ℵ₀ ≤ κ) : ws5_verdict dest h₀ hinf ≠ Series13Verdict.Disconnected := by
  rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide

theorem ws5_verdict_not_partial {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) : ws5_verdict dest h₀ hinf ≠ Series13Verdict.Partial := by
  rw [ws5_verdict_eq dest h₀ h₁ hne hinf]; decide

/-! ### The audit folded in -/

/-- **Genuine-connection check** (`series-review-1.md` SR1-1, SR1-2). Orders non-trivial — the inspection
order, the labelled order with its ANTITONE REFERENCE POSITION load-bearing (third conjunct), AND the
labelled order at MINT POINTS (`ws2_mint_nontrivial`) — together with a proved non-identity round trip. The
certificate now exercises the contested antitone half and the mint points, not two constant literals. -/
theorem ws5_audit_genuine_connection {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ((∃ a b : Insp dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Insp dest, ¬ a ≤ b))
  ∧ ((∃ a b : Lab dest h₀, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest h₀, ¬ a ≤ b)
      ∧ (∃ a b : Lab dest h₀, a.cT = b.cT ∧ ¬ a ≤ b))                       -- reference position load-bearing
  ∧ (mintL h₀ (fun _ _ => True) ≤ mintL h₀ (fun _ _ => False)
      ∧ mintL h₀ (fun _ _ => True) ≠ mintL h₀ (fun _ _ => False)
      ∧ ¬ (mintL h₀ (fun _ _ => False) ≤ mintL h₀ (fun _ _ => True)))        -- non-triviality AT MINT POINTS
  ∧ (mintL h₀ (readInsp h₀ (bRefActive dest h₀)) ≤ bRefActive dest h₀
     ∧ ¬ (bRefActive dest h₀ ≤ mintL h₀ (readInsp h₀ (bRefActive dest h₀)))) :=
  ⟨ws1_orders_insp_nontrivial dest h₀, ws1_orders_lab_nontrivial dest h₀,
   ws2_mint_nontrivial h₀, ws3_roundtrip_not_identity h₀⟩

/-- **Exogeneity check.** The mint above the plain layer, a proof term. -/
theorem ws5_audit_exogeneity {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    ∃ i₁ i₂ : Insp dest,
        plainOf (coalg hinf (mintL h₀ i₁)) = plainOf (coalg hinf (mintL h₀ i₂))
      ∧ mintL h₀ i₁ ≠ mintL h₀ i₂ :=
  ws2_mint_exogenous h₀ hinf

/-- **Structural-defect check.** `≈` preserves the link data; every mint is on the link; `outWit` is off it. -/
theorem ws5_audit_structural_defect {X : Type u} (dest : X → PkObj κ X) (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) :
    (∀ b b' : Lab dest h₀, labEquiv h₀ b b' → (b.cT = b'.cT) ∧ (b.cF h₀ ↔ b'.cF h₀))
  ∧ (∀ insp : Insp dest, (mintL h₀ insp).cT h₀ = ¬ (mintL h₀ insp).cF h₀)
  ∧ ((outWit h₀ h₁).cT h₀ = (outWit h₀ h₁).cF h₀) :=
  ws4_exclusion_structural h₀ h₁ hne hinf

/-! ### Concrete carriers: the verdict is UNCONDITIONAL on carrier existence (`series-review-2.md` SR2-2)

The headlines quantify over an arbitrary `dest` and take the carrier's hold-count as a hypothesis. Here we
DISCHARGE those hypotheses at concrete carriers, so `Dual` (two-hold carrier) and `Total` (single-hold
carrier) hold with `hinf` the only remaining (intrinsic) assumption, not merely `if a carrier exists`. -/

/-- A two-hold carrier: `ULift Bool` with each state self-looping. `Hold` is the diagonal, two elements. -/
def dest2 (hinf : ℵ₀ ≤ κ) : ULift.{u} Bool → PkObj κ (ULift.{u} Bool) := fun i => pkSingleton hinf i

def h0two (hinf : ℵ₀ ≤ κ) : Hold (dest2 hinf) :=
  ⟨(⟨true⟩, ⟨true⟩), by simp [dest2]⟩
def h1two (hinf : ℵ₀ ≤ κ) : Hold (dest2 hinf) :=
  ⟨(⟨false⟩, ⟨false⟩), by simp [dest2]⟩

theorem h1two_ne_h0two (hinf : ℵ₀ ≤ κ) : h1two hinf ≠ h0two hinf := by
  intro he
  have hb : (⟨false⟩ : ULift.{u} Bool) = ⟨true⟩ := congrArg (fun h => (Subtype.val h).1) he
  exact absurd hb (by decide)

/-- **`Dual` at a concrete two-hold carrier**, the carrier hypotheses discharged. -/
theorem ws5_dual_witnessed (hinf : ℵ₀ ≤ κ) :
    ws5_verdict (dest2 hinf) (h0two hinf) hinf = Series13Verdict.Dual :=
  ws5_verdict_eq (dest2 hinf) (h0two hinf) (h1two hinf) (h1two_ne_h0two hinf) hinf

/-- A single-hold carrier: `PUnit`, one state self-looping. `Hold` is a subsingleton, one element. -/
def destOne (hinf : ℵ₀ ≤ κ) : PUnit.{u+1} → PkObj κ PUnit.{u+1} := fun _ => pkSingleton hinf PUnit.unit

def h0one (hinf : ℵ₀ ≤ κ) : Hold (destOne hinf) :=
  ⟨(PUnit.unit, PUnit.unit), by simp [destOne]⟩

/-- **`Total` at a concrete single-hold carrier** (the degenerate case, at the flat layer), discharged. -/
theorem ws5_total_witnessed (hinf : ℵ₀ ≤ κ) :
    ws5_verdict (destOne hinf) (h0one hinf) hinf = Series13Verdict.Total :=
  ws5_verdict_degenerate (destOne hinf) (h0one hinf)
    (fun h => Subtype.ext (Subsingleton.elim h.1 (h0one hinf).1)) hinf

-- OPEN (layer-stability, single-layer scope): does the mint commute with reification, and does any
-- tower-carrying import survive outside the mint's image up to `≈`? The flat carrier here cannot test it;
-- left open, prose only, never a proof term. Any TOTAL above is TOTAL AT THE FLAT LAYER.

end Series13.WS5
