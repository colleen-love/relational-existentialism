/-
`series-03/formal/ws14.lean`

WS14 (`series-03/spec/ws14/02-design.md`): **the graded carrier defeats the
collapse.** On the *unweighted* carrier `νP_κ`, any two hereditarily-nonempty
states are equal (WS10's `ws10_unlabeled_atomless_collapses`: atomless ∧ plural is
unsatisfiable). This workstream shows weighting breaks that collapse:

* **loops at every weight (G1, G2).** For each quantale weight `q` there is a
  self-loop state `loopState q` whose only successor is itself, with weight `q`
  (`loop_str_self`). Distinct weights give distinct loops (`ws14_loop_ne`) —
  distinguishable by the *weight* of the loop, which an Aczel–Mendler `WQBisim` must
  preserve (`ws14_loops_not_bisim`).
* **loops are hereditarily supported (G3).** A `q ≠ ⊥` loop reaches only itself, and
  its support is nonempty (`loop_hereditary`).
* **the headline (G4).** Hence the weighted carrier carries a *plural,
  hereditarily-supported* subclass (`ws14_graded_core_plural`) — the direct
  weighted counterpart, with opposite verdict, of the plain-carrier collapse.

Bundle `ws14_graded_core`. The composition-closure fork (G5), weighted standpoints
(G8), the infinite Lawvere witness (G9), and the weak-law uniqueness class (G6,
`ℵ₀`-gated) remain open remarks routed to later waves. Axiom-clean beyond Mathlib's
standard three, `sorry`-free.

Built on `ws4` (the weighted stack) and `ws10` (the plain-carrier collapse contrast).
-/
import ws4
import ws10

universe u

open Cardinal Series03.WS4

namespace Series03.WS14

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [GoodQuantale Q] {κ : Cardinal.{u}}

/-! ## Block 1 — loops (G1, G2) -/

/-- The one-point coalgebra with a self-loop of weight `q`. -/
noncomputable def loopCoalg (q : Q) (hinf : ℵ₀ ≤ κ) : WQCoalg Q κ where
  X := PUnit.{u+1}
  str := fun _ => ⟨fun _ => q, by
    haveI : Finite ↥(Qsupp (fun _ : PUnit.{u+1} => q)) := (Set.toFinite _).to_subtype
    exact lt_of_lt_of_le (Cardinal.mk_lt_aleph0_iff.mpr ‹_›) hinf⟩

/-- The unique morphism from the loop coalgebra into the terminal weighted carrier. -/
noncomputable def loopHom (q : Q) (hinf : ℵ₀ ≤ κ) : PUnit.{u+1} → (νWQ Q κ).X :=
  (νWQ_terminal Q κ (loopCoalg q hinf)).choose

lemma loopHom_nat (q : Q) (hinf : ℵ₀ ≤ κ) (x : PUnit.{u+1}) :
    (νWQ Q κ).str (loopHom q hinf x) = WQMap (loopHom q hinf) ((loopCoalg q hinf).str x) :=
  (νWQ_terminal Q κ (loopCoalg q hinf)).choose_spec.1 x

/-- The self-loop state at weight `q`. -/
noncomputable def loopState (q : Q) (hinf : ℵ₀ ≤ κ) : (νWQ Q κ).X :=
  loopHom q hinf PUnit.unit

lemma str_loop_eq (q : Q) (hinf : ℵ₀ ≤ κ) :
    ((νWQ Q κ).str (loopState q hinf)).1 = pushQ (fun _ : PUnit.{u+1} => q) (loopHom q hinf) := by
  rw [loopState, loopHom_nat q hinf PUnit.unit]; rfl

/-- The loop's unfolding: weight `q` at the loop itself, `⊥` everywhere else. -/
lemma str_loop_apply (q : Q) (hinf : ℵ₀ ≤ κ) (y : (νWQ Q κ).X) :
    ((νWQ Q κ).str (loopState q hinf)).1 y = if y = loopState q hinf then q else ⊥ := by
  rw [str_loop_eq]
  show (⨆ x : PUnit.{u+1}, ⨆ (_ : loopHom q hinf x = y), q) = if y = loopState q hinf then q else ⊥
  rw [iSup_unique]
  by_cases hy : y = loopState q hinf
  · rw [if_pos hy]; exact iSup_pos hy.symm
  · rw [if_neg hy]; exact iSup_neg (fun hc => hy hc.symm)

/-- **G1.** The loop's own weight is `q`. -/
lemma loop_str_self (q : Q) (hinf : ℵ₀ ≤ κ) :
    ((νWQ Q κ).str (loopState q hinf)).1 (loopState q hinf) = q := by
  rw [str_loop_apply]; simp

/-- **G2.** Distinct weights give distinct loops — the plain-carrier collapse fails
on the weighted carrier. -/
theorem ws14_loop_ne (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    loopState q₁ hinf ≠ loopState q₂ hinf := by
  intro he
  apply hne
  have h1 : ((νWQ Q κ).str (loopState q₁ hinf)).1 (loopState q₁ hinf) = q₁ := loop_str_self q₁ hinf
  rw [he, loop_str_self q₂ hinf] at h1
  exact h1.symm

/-- The blocked-collapse mechanism, machine-checked: distinct-weight loops are not
bisimilar (equality *is* bisimilarity on the terminal carrier). -/
theorem ws14_loops_not_bisim (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ¬ (∃ R, Nonempty (WQBisim (νWQ Q κ) R) ∧ R (loopState q₁ hinf) (loopState q₂ hinf)) := by
  rw [wq_bisim_behavioural (νWQ_terminal Q κ)]
  exact ws14_loop_ne hinf hne

/-! ## Block 2 — weighted reachability and hereditary support (G3) -/

/-- Weighted reachability: the reflexive-transitive closure of the nonzero-weight
successor relation. -/
def WReaches (x y : (νWQ Q κ).X) : Prop :=
  Relation.ReflTransGen (fun a b => ((νWQ Q κ).str a).1 b ≠ ⊥) x y

/-- A state is hereditarily supported if every weighted-reachable state has nonempty
support. -/
def HereditarilySupported (x : (νWQ Q κ).X) : Prop :=
  ∀ y, WReaches x y → (Qsupp ((νWQ Q κ).str y).1).Nonempty

/-- A loop reaches only itself (its only nonzero successor is itself). -/
lemma wreaches_loop (q : Q) (hinf : ℵ₀ ≤ κ) :
    ∀ y, WReaches (loopState q hinf) y → y = loopState q hinf := by
  intro y h
  induction h with
  | refl => rfl
  | tail hab hstep ih =>
      subst ih
      by_contra hc
      rw [str_loop_apply, if_neg hc] at hstep
      exact hstep rfl

/-- **G3.** A `q ≠ ⊥` loop is hereditarily supported. -/
theorem loop_hereditary (q : Q) (hinf : ℵ₀ ≤ κ) (hq : q ≠ ⊥) :
    HereditarilySupported (loopState q hinf) := by
  intro y hy
  have hyeq : y = loopState q hinf := wreaches_loop q hinf y hy
  subst hyeq
  refine ⟨loopState q hinf, ?_⟩
  show ((νWQ Q κ).str (loopState q hinf)).1 (loopState q hinf) ≠ ⊥
  rw [loop_str_self]; exact hq

/-! ## Block 3 — the weighted carrier cardinality bound (G7) -/

/-- **G7.** The weighted carrier is at least `κ` (Lambek–Cantor transfer): if it
were smaller, every weighting would be legal, so `X ≃ (X → Q)`, contradicting
Cantor for `#Q ≥ 2`. Unlocks weighted analogues of the observer/standpoint
properness results. -/
theorem ws14_wq_card_ge (hQ : ∃ q : Q, q ≠ (⊥ : Q)) :
    κ ≤ Cardinal.mk (νWQ Q κ).X := by
  by_contra hlt
  rw [not_le] at hlt
  have hconstraint : ∀ ρ : (νWQ Q κ).X → Q, Cardinal.mk ↥(Qsupp ρ) < κ := fun ρ =>
    lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset (Set.subset_univ _))
      (le_of_eq Cardinal.mk_univ)) hlt
  have e1 : (νWQ Q κ).X ≃ WQObj Q κ (νWQ Q κ).X :=
    Equiv.ofBijective _ (wqLambek (νWQ_terminal Q κ))
  have e2 : WQObj Q κ (νWQ Q κ).X ≃ ((νWQ Q κ).X → Q) := Equiv.subtypeUnivEquiv hconstraint
  have e : (νWQ Q κ).X ≃ ((νWQ Q κ).X → Q) := e1.trans e2
  have hcard : Cardinal.mk Q ^ Cardinal.mk (νWQ Q κ).X = Cardinal.mk (νWQ Q κ).X := by
    rw [Cardinal.power_def]; exact (Cardinal.mk_congr e).symm
  obtain ⟨q, hq⟩ := hQ
  have h2 : (2 : Cardinal) ≤ Cardinal.mk Q := Cardinal.two_le_iff.mpr ⟨⊥, q, fun h => hq h.symm⟩
  have hle : (2 : Cardinal) ^ Cardinal.mk (νWQ Q κ).X ≤ Cardinal.mk Q ^ Cardinal.mk (νWQ Q κ).X :=
    Cardinal.power_le_power_right h2
  rw [hcard] at hle
  exact absurd (lt_of_lt_of_le (Cardinal.cantor _) hle) (lt_irrefl _)

/-! ## Block 4 — the headline (G4) and the bundle -/

/-- **G4.** The weighted carrier carries a plural, hereditarily-supported subclass —
the opposite-verdict weighted counterpart of the plain-carrier collapse
(`ws10_unlabeled_atomless_collapses`). -/
theorem ws14_graded_core_plural (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q}
    (h₁ : q₁ ≠ ⊥) (h₂ : q₂ ≠ ⊥) (hne : q₁ ≠ q₂) :
    ∃ x y : (νWQ Q κ).X, x ≠ y ∧
      HereditarilySupported x ∧ HereditarilySupported y :=
  ⟨loopState q₁ hinf, loopState q₂ hinf, ws14_loop_ne hinf hne,
   loop_hereditary q₁ hinf h₁, loop_hereditary q₂ hinf h₂⟩

/-- The WS14 graded-core deliverable: weighting realizes what the plain carrier
forbids. Named for the verdict it records, not `ws14_resolved`. -/
structure WS14GradedCore (Q : Type u) [GoodQuantale Q] (κ : Cardinal.{u}) where
  hinf : ℵ₀ ≤ κ
  plural : ∀ {q₁ q₂ : Q}, q₁ ≠ ⊥ → q₂ ≠ ⊥ → q₁ ≠ q₂ →
    ∃ x y : (νWQ Q κ).X, x ≠ y ∧
      HereditarilySupported x ∧ HereditarilySupported y

/-- **The WS14 deliverable.** -/
theorem ws14_graded_core (hinf : ℵ₀ ≤ κ) : WS14GradedCore Q κ where
  hinf := hinf
  plural := fun h₁ h₂ hne => ws14_graded_core_plural hinf h₁ h₂ hne

/-- The `Łₙ` (`n ≥ 2`) instantiation: weights `⊥ < 1 ⊗-unit`, so two distinct
non-`⊥` weights exist and the graded core is inhabited concretely. -/
theorem ws14_graded_core_Luk {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y : (νWQ (Luk n) κ).X, x ≠ y ∧
      HereditarilySupported x ∧ HereditarilySupported y := by
  -- weights `1 = ⊤ = n` and `n-1`, both `≠ ⊥ = 0`, and distinct for `n ≥ 2`
  refine ws14_graded_core_plural hinf (q₁ := (1 : Luk n)) (q₂ := ⟨n - 1, by omega⟩) ?_ ?_ ?_
  · intro h; have := congrArg Fin.val h; simp only [Luk.one_val, Luk.bot_val] at this; omega
  · intro h; have := congrArg Fin.val h; simp only [Luk.bot_val] at this; omega
  · intro h; have := congrArg Fin.val h; simp only [Luk.one_val] at this; omega

end Series03.WS14
