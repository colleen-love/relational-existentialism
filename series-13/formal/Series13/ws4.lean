/-
`series-13/formal/Series13/ws4.lean`

WS4 - The defect (the fork in order-theoretic clothes). Series 13. Genuinely uncertain in direction.

Consumes WS1 (the orders, the `Lab` codomain, `coalg`), WS2 (the mint), WS3 (`realizeAsResidue`). Tests
mintability UP TO EQUIVALENCE `≈` (order-equivalence in `instLELab`), not literal equality (which is too fine,
DUAL-by-construction). Mintability up to `≈` reduces to the diagonal link `b.cT h₀ = ¬ b.cF h₀`. Computed:
DUAL on carriers with a second hold (`ws4_mint_not_surjective`: `outWit` an import `≈` no mint, exclusion
surviving `≈`, `ws4_exclusion_structural`), TOTAL on the degenerate single-hold carrier
(`ws4_mint_essentially_surjective_degenerate`). The theorem LOCATES membership up to `≈`, never SORTS.

SCOPE (a named open, not a silent omission): the carrier is FLAT (no reification tower). So this is the
FLAT-LAYER mintability question; whether a tower-carrying import survives outside the mint's image up to `≈`
is left open (WS5). Any TOTAL here is TOTAL AT THE FLAT LAYER, bounded by the unexamined tower.

The words `given`/`chosen` appear in prose only; no `Origin`/`genealogy` term sorts an out-of-image import.

Design doc: `series-13/spec/ws4-design.md`.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series13.ws3

universe u

namespace Series13.WS4

open Series13.WS1 Series13.WS2 Series13.WS3 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{u}}

/-- **The equivalence.** Order-equivalence in `instLELab`. Written `≈` in the module prose and docstrings
(`series-review-1.md` SR1-8): `b ≈ b'` denotes `labEquiv h₀ b b'`; it is not registered as `Setoid`/`≈`
notation to avoid clashing with Mathlib's `Setoid` `≈`. -/
def labEquiv {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest) (b b' : Lab dest h₀) : Prop :=
  b ≤ b' ∧ b' ≤ b

/-- **The test article.** Residue-position `⊤`; reference-position `(≠ h₁)`. Off the diagonal link when
`h₀ ≠ h₁`, and `¬ Recoverable` (labels differ at `h₁`). -/
def outWit {X : Type u} {dest : X → PkObj κ X} (h₀ h₁ : Hold dest) : Lab dest h₀ :=
  ⟨(fun _ => True), (fun h => h ≠ h₁)⟩

/-- If a two-region coalgebra has EQUAL labels, it is `Recoverable` (constant labels match everywhere). -/
lemma coalg_recoverable_of_eq {X : Type u} {dest : X → PkObj κ X} {h₀ : Hold dest} (hinf : ℵ₀ ≤ κ)
    {b : Lab dest h₀} (heq : b.cT = b.cF) : Recoverable (coalg hinf b) := by
  have hset : ∀ z : MCar dest, (coalg hinf b z).1 = {(b.cT, z)} := by
    intro z
    cases z using ULift.rec with
    | up bl => cases bl <;> simp [coalg, heq]
  intro R hR x y hxy
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [hset x, Set.mem_singleton_iff] at hp; subst hp
    exact ⟨(b.cT, y), by rw [hset y]; exact Set.mem_singleton _, rfl, hxy⟩
  · intro q hq
    rw [hset y, Set.mem_singleton_iff] at hq; subst hq
    exact ⟨(b.cT, x), by rw [hset x]; exact Set.mem_singleton _, rfl, hxy⟩

/-! ## DUAL (carriers with a second hold): the defect up to `≈` -/

/-- **THE DEFECT (up to `≈`).** `outWit` fails `Recoverable` (an import) and is `≈` NO mint: order-equivalence
forces `residue insp h₀` and `insp h₀ h₀` both true, contradicting the diagonal link. The theorem LOCATES an
out-of-image import at the honest resolution; it never classifies it.

DOMAIN (`series-review-1.md` SR1-3, charter discrepancy CD-1): the first conjunct `¬ Recoverable (coalg …)`
is a genuine COALGEBRA fact (an import in the labelled-coalgebra sense); the second is non-mintability up to
`labEquiv` over the two-region self-loop coalgebras represented by `Lab`, NOT over all labelled coalgebras
over `dest`. The narrowing is disclosed in `charter-status.md` CD-1 and bounded further by the flat-layer
scope (WS5). -/
theorem ws4_mint_not_surjective {X : Type u} {dest : X → PkObj κ X} (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) :
    ¬ Recoverable (coalg hinf (outWit h₀ h₁))
  ∧ ¬ ∃ insp : Insp dest, labEquiv h₀ (mintL h₀ insp) (outWit h₀ h₁) := by
  refine ⟨?_, ?_⟩
  · -- ¬ Recoverable : ⊤ plain-bisim, not label-bisim (cT ≠ cF at h₁)
    intro hrec
    have hlab := hrec _ (coalg_plain_true_bisim hinf (outWit h₀ h₁))
    obtain ⟨hf, _⟩ := hlab ⟨true⟩ ⟨false⟩ trivial
    obtain ⟨q, hq, hfst, _⟩ := hf ((outWit h₀ h₁).cT, ⟨true⟩) (by rw [coalg_true]; exact Set.mem_singleton _)
    rw [coalg_false, Set.mem_singleton_iff] at hq; subst hq
    have := congrFun hfst h₁
    simp only [outWit] at this
    exact absurd this (by simp)
  · -- ≈ no mint : the diagonal link
    rintro ⟨insp, hle₁, hle₂⟩
    have hresT : residue insp h₀ := hle₂.1 h₀ trivial
    have hcFh0 : (outWit h₀ h₁).cF h₀ := hne.symm
    have hself : insp h₀ h₀ := hle₁.2 hcFh0
    exact absurd hself hresT

/-- **THE LINK SURVIVES `≈`.** `≈` preserves the diagonal-link data (`cT` fully, `cF` at `h₀`); every mint is
ON the link (`cT h₀ = ¬ cF h₀`); `outWit` is OFF it. So the exclusion is structural, not a literal-equality
accident. -/
theorem ws4_exclusion_structural {X : Type u} {dest : X → PkObj κ X} (h₀ h₁ : Hold dest) (hne : h₁ ≠ h₀)
    (hinf : ℵ₀ ≤ κ) :
    (∀ b b' : Lab dest h₀, labEquiv h₀ b b' → (b.cT = b'.cT) ∧ (b.cF h₀ ↔ b'.cF h₀))
  ∧ (∀ insp : Insp dest, (mintL h₀ insp).cT h₀ = ¬ (mintL h₀ insp).cF h₀)
  ∧ ((outWit h₀ h₁).cT h₀ = (outWit h₀ h₁).cF h₀) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro b b' ⟨⟨hcT1, hcF1⟩, ⟨hcT2, hcF2⟩⟩
    refine ⟨funext fun h => propext ⟨hcT1 h, hcT2 h⟩, ⟨hcF2, hcF1⟩⟩
  · intro insp; rfl
  · show True = (h₀ ≠ h₁)
    exact propext ⟨fun _ => hne.symm, fun _ => trivial⟩

/-! ## TOTAL (degenerate single-hold carrier), at the flat layer -/

/-- **TOTAL, degenerate, at the flat layer.** On a single-hold carrier every `¬ Recoverable` coalgebra sits
on the diagonal link, hence is `≈` some mint. The mint is essentially surjective over FLAT imports; the tower
is unexamined (WS5, the layer-stability open). Reported honestly as degenerate and bounded. -/
theorem ws4_mint_essentially_surjective_degenerate {X : Type u} {dest : X → PkObj κ X} (h₀ : Hold dest)
    (hone : ∀ h : Hold dest, h = h₀) (hinf : ℵ₀ ≤ κ) :
    ∀ b : Lab dest h₀, (¬ Recoverable (coalg hinf b)) → ∃ insp, labEquiv h₀ (mintL h₀ insp) b := by
  intro b hb
  have hneCTF : b.cT ≠ b.cF := fun heq => hb (coalg_recoverable_of_eq hinf heq)
  have hne0 : b.cT h₀ ≠ b.cF h₀ := by
    intro heq0; apply hneCTF; funext h; rw [hone h]; exact heq0
  have hlink2 : ¬ b.cT h₀ ↔ b.cF h₀ := by
    constructor
    · intro hncT0; by_contra hncF0
      exact hne0 (propext ⟨fun h => absurd h hncT0, fun h => absurd h hncF0⟩)
    · intro hcF0 hcT0
      exact hne0 (propext ⟨fun _ => hcF0, fun _ => hcT0⟩)
  refine ⟨realizeAsResidue b.cT, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- (mintL ...).cT ⊑c b.cT
    rw [mintL_cT, residue_realizeAsResidue]; exact leC_refl _
  · -- b.cF h₀ → (mintL ...).cF h₀   (= ¬ b.cT h₀)
    intro hcF0; show ¬ b.cT h₀; exact hlink2.mpr hcF0
  · -- b.cT ⊑c (mintL ...).cT
    rw [mintL_cT, residue_realizeAsResidue]; exact leC_refl _
  · -- (mintL ...).cF h₀ (= ¬ b.cT h₀) → b.cF h₀
    intro hh; exact hlink2.mp hh

end Series13.WS4
