/-
`series-3/formal/ws4.lean`  (WIP — Tier 1: class hierarchy + the Łₙ witness)
-/
import ws3

universe u
open Cardinal

namespace Series3.WS4

/-! ## §2 The quantale class hierarchy (design §2.1–2.2) -/

/-- A "good quantale": a commutative-monoid + complete-lattice with `⊗` distributing
over joins and `⊥` a `⊗`-annihilator. `1` is the `⊗`-unit (not necessarily `⊤`). -/
class GoodQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  tensor_sSup : ∀ (a : Q) (s : Set Q), a * sSup s = ⨆ b ∈ s, a * b
  bot_tensor  : ∀ a : Q, (⊥ : Q) * a = ⊥

/-- The preservation extension: a residuation/divisibility law (MV-style). Weak-
pullback preservation and the graded law are proved for this class. -/
class DivisibleQuantale (Q : Type u) extends GoodQuantale Q where
  tensor_section : ∀ (a w : Q), w ≤ a * ⊤ → a * (sSup {b | a * b ≤ w}) = w

/-! ## §2.3 The concrete non-idempotent witness `Łₙ` (Łukasiewicz MV-chain) -/

/-- The `(n+1)`-element Łukasiewicz chain, a type synonym for `Fin (n+1)` carrying
the truncated-addition `⊗` (strong conjunction) with unit `n = ⊤`. -/
def Luk (n : ℕ) : Type := Fin (n + 1)

namespace Luk
variable {n : ℕ}

instance : NeZero (n + 1) := ⟨n.succ_ne_zero⟩
noncomputable instance : CompleteLinearOrder (Luk n) := Fin.completeLinearOrder
instance : Fintype (Luk n) := Fin.fintype _

/-- `a ⊗ b = a + b − n` (truncated), the Łukasiewicz strong conjunction. -/
instance : CommMonoid (Luk n) where
  mul a b := ⟨a.1 + b.1 - n, by omega⟩
  one := ⟨n, by omega⟩
  mul_assoc a b c := by apply Fin.ext; show a.1 + b.1 - n + c.1 - n = a.1 + (b.1 + c.1 - n) - n; omega
  one_mul a := by apply Fin.ext; show n + a.1 - n = a.1; omega
  mul_one a := by apply Fin.ext; show a.1 + n - n = a.1; omega
  mul_comm a b := by apply Fin.ext; show a.1 + b.1 - n = b.1 + a.1 - n; omega

@[simp] lemma mul_val (a b : Luk n) : (a * b).1 = a.1 + b.1 - n := rfl
@[simp] lemma one_val : (1 : Luk n).1 = n := rfl
@[simp] lemma bot_val : (⊥ : Luk n).1 = 0 := rfl
@[simp] lemma top_val : (⊤ : Luk n).1 = n := rfl

/-- `⊗` is monotone in its second argument. -/
lemma mul_mono_right (a : Luk n) {b c : Luk n} (h : b ≤ c) : a * b ≤ a * c := by
  rw [Fin.le_def] at h ⊢; simp only [mul_val]; omega

/-- `⊥` is a `⊗`-annihilator (on either side, since `⊗` is commutative). -/
@[simp] lemma mul_bot (a : Luk n) : a * ⊥ = ⊥ := by
  apply Fin.ext; have := a.2; simp only [mul_val, bot_val]; omega

noncomputable instance : GoodQuantale (Luk n) where
  tensor_sSup a s := by
    apply le_antisymm
    · -- a * sSup s ≤ ⨆ b∈s, a*b
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hmem : sSup s ∈ s := hne.csSup_mem s.toFinite
        exact le_iSup₂_of_le (sSup s) hmem le_rfl
    · -- ⨆ b∈s, a*b ≤ a * sSup s
      refine iSup₂_le fun b hb => mul_mono_right a (le_sSup hb)
  bot_tensor a := by rw [mul_comm]; exact mul_bot a

noncomputable instance : DivisibleQuantale (Luk n) where
  tensor_section a w hw := by
    -- w ≤ a * ⊤ = a; residual b* = min(n, w + n − a); a ⊗ b* = w
    have hwa : w.1 ≤ a.1 := by
      have : (w : Luk n) ≤ a * ⊤ := hw
      rw [Fin.le_def] at this; simp only [mul_val, top_val] at this; omega
    have hres : sSup {b : Luk n | a * b ≤ w} = ⟨min n (w.1 + n - a.1), by omega⟩ := by
      apply le_antisymm
      · refine csSup_le ⟨⊥, by simp⟩ ?_
        intro b hb; rw [Set.mem_setOf_eq, Fin.le_def, mul_val] at hb
        rw [Fin.le_def]; simp only; omega
      · refine le_csSup (Set.toFinite _).bddAbove ?_
        rw [Set.mem_setOf_eq, Fin.le_def, mul_val]; simp only; omega
    apply Fin.ext
    rw [mul_val, hres]; simp only; omega

/-- **The quantitative tripwire (step 19):** `Łₙ` is non-idempotent for `n ≥ 2`,
so §3.5 grading is genuinely quantitative — not a qualitative frame in disguise. -/
theorem ws4_quantitative_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Luk n, a * a ≠ a := by
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  intro h
  have := congrArg Fin.val h
  simp only [mul_val] at this; omega

end Luk

/-! ## §3 The `Q`-weighted `<κ`-supported functor `W_Q` (design §1, §3, Layer A)

Everything here needs only `[CompleteLattice Q]` (design §2.2: "existence /
functoriality / bisim / bound need only `GoodQuantale`"; in fact the lattice
alone suffices). `W_Q κ X = { ρ : X → Q // supp ρ is < κ-sized }`, with the
functorial action the **`Q`-sup pushforward over fibres** (lattice joins only,
no `⊗` — design §3, P2/P4 fixes). It is a QPF (shapes `Σ a, positions a → Q`),
so `Cofix (W_Q)` is its terminal coalgebra by the same `ws1`/`ws2` route. -/

section Functor
open Ordinal Set QPF Functor
variable {Q : Type u} [CompleteLattice Q] {κ : Cardinal.{u}}

/-- Support of a `Q`-weighting: the points carrying non-`⊥` weight. -/
def Qsupp {X : Type u} (ρ : X → Q) : Set X := {x | ρ x ≠ ⊥}

/-- Pushforward of a `Q`-weighting along `f`: the join over each fibre. This is the
functorial action of `W_Q` and, simultaneously, the QPF quotient map `abs`. -/
def pushQ {X Y : Type u} (ρ : X → Q) (f : X → Y) : Y → Q :=
  fun y => ⨆ x, ⨆ (_ : f x = y), ρ x

/-- Functoriality — identity. -/
lemma pushQ_id {X : Type u} (ρ : X → Q) : pushQ ρ id = ρ := by
  funext y
  apply le_antisymm
  · exact iSup_le fun x => iSup_le fun h => le_of_eq (by rw [show x = y from h])
  · exact le_iSup_of_le y (le_iSup_of_le rfl le_rfl)

/-- Functoriality — composition (the single sup-reindexing identity on which
`WQMap_comp` and the QPF `abs_map` both rest). -/
lemma pushQ_comp {X Y Z : Type u} (ρ : X → Q) (f : X → Y) (g : Y → Z) :
    pushQ ρ (g ∘ f) = pushQ (pushQ ρ f) g := by
  funext z
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le (f x) (le_iSup_of_le hx (le_iSup_of_le x (le_iSup_of_le rfl le_rfl)))
  · refine iSup_le fun y => iSup_le fun hy => iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le x (le_iSup_of_le (show g (f x) = z by rw [hx]; exact hy) le_rfl)

/-- The pushforward's support lands in the image of the source support — the bound
that makes `WQMap` and `abs` respect the `< κ` cap. -/
lemma Qsupp_pushQ_subset {X Y : Type u} (ρ : X → Q) (f : X → Y) :
    Qsupp (pushQ ρ f) ⊆ f '' Qsupp ρ := by
  intro y hy
  by_contra hcon
  apply hy
  show pushQ ρ f y = ⊥
  simp only [pushQ, iSup_eq_bot]
  intro x hx
  by_contra hb
  exact hcon ⟨x, hb, hx⟩

/-- `W_Q κ X` — `Q`-weightings of `X` with `< κ`-sized support (design §1). -/
def WQObj (Q : Type u) [CompleteLattice Q] (κ : Cardinal.{u}) (X : Type u) : Type u :=
  {ρ : X → Q // Cardinal.mk (↥(Qsupp ρ)) < κ}

/-- The functorial action `W_Q.map` — pushforward (design §3, `WQMap`). -/
def WQMap {X Y : Type u} (f : X → Y) (s : WQObj Q κ X) : WQObj Q κ Y :=
  ⟨pushQ s.1 f, lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset (Qsupp_pushQ_subset s.1 f))
    Cardinal.mk_image_le) s.2⟩

@[simp] lemma WQMap_val {X Y : Type u} (f : X → Y) (s : WQObj Q κ X) :
    (WQMap f s).1 = pushQ s.1 f := rfl

lemma WQMap_id {X : Type u} (s : WQObj Q κ X) : WQMap (id : X → X) s = s := by
  apply Subtype.ext; exact pushQ_id s.1

lemma WQMap_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) (s : WQObj Q κ X) :
    WQMap (g ∘ f) s = WQMap g (WQMap f s) := by
  apply Subtype.ext; exact pushQ_comp s.1 f g

/-! ### §3.2 `W_Q` is a QPF; `Cofix (W_Q)` is its terminal coalgebra (Layer A steps 2–3)

The polynomial functor `WQP` has shapes `Σ a : κ.ord.toType, (positions a → Q)` —
an ordinal bound `a` **together with a weight profile** on its positions — and
positions `{b // b < a}`. `abs` reads off the pushforward `pushQ w g`; `repr`
enumerates the support by the ordinal segment of order-type `(#supp).ord` and reads
its weights. At `Q = Łₙ` the weight profile ranges over the finite `Fin (n+1)`, so
the shape count is `< κ` outright (design §3 [S1]: `hQsmall` is vacuous). -/

/-- The polynomial functor of which `W_Q` is a quotient. -/
def WQP (Q : Type u) (κ : Cardinal.{u}) : PFunctor.{u} where
  A := Σ a : κ.ord.toType, ({b : κ.ord.toType // b < a} → Q)
  B := fun a => {b : κ.ord.toType // b < a.1}

/-- `abs ⟨⟨a, w⟩, g⟩ := pushQ w g` — the weighted set with support `⊆ range g`. -/
def absWQ {α : Type u} (p : (WQP Q κ).Obj α) : WQObj Q κ α :=
  ⟨pushQ p.1.2 p.2, by
    refine lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset (Qsupp_pushQ_subset p.1.2 p.2))
      (le_trans Cardinal.mk_image_le (Cardinal.mk_subtype_le _))) (card_typein_toType_lt κ p.1.1)⟩

/-- `repr` of a weighted set `s`: enumerate `supp s` by the initial segment of
order-type `(#supp).ord`, read weights `w i = s (e i)`, positions `g i = e i`. The
bundled `abs (repr s) = s` is proved here (support-exact reconstruction). -/
noncomputable def reprWQ {α : Type u} (s : WQObj Q κ α) :
    { p : (WQP Q κ).Obj α // absWQ p = s } := by
  have ho' : (Cardinal.mk (↥(Qsupp s.1))).ord < type (α := κ.ord.toType) (· < ·) := by
    rw [type_toType]; exact Cardinal.ord_lt_ord.mpr s.2
  set a : κ.ord.toType := enum (α := κ.ord.toType) (· < ·) ⟨(Cardinal.mk (↥(Qsupp s.1))).ord, ho'⟩
    with ha
  have hcard : Cardinal.mk ({b : κ.ord.toType // b < a}) = Cardinal.mk (↥(Qsupp s.1)) := by
    have h1 : Cardinal.mk ({b : κ.ord.toType // b < a})
        = (typein (α := κ.ord.toType) (· < ·) a).card := card_typein a
    rw [h1, ha, typein_enum, Cardinal.card_ord]
  let e : {b : κ.ord.toType // b < a} ≃ ↥(Qsupp s.1) := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨⟨⟨a, fun i => s.1 (e i : α)⟩, fun i => (e i : α)⟩, ?_⟩
  apply Subtype.ext
  show pushQ (fun i => s.1 (e i : α)) (fun i => (e i : α)) = s.1
  funext y
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun h => le_of_eq (by
      show s.1 (e i : α) = s.1 y; rw [show (e i : α) = y from h])
  · by_cases hy : s.1 y = ⊥
    · rw [hy]; exact bot_le
    · have hymem : y ∈ Qsupp s.1 := hy
      have hei : (e (e.symm ⟨y, hymem⟩) : α) = y := by rw [Equiv.apply_symm_apply]
      calc s.1 y = s.1 (e (e.symm ⟨y, hymem⟩) : α) := by rw [hei]
        _ ≤ pushQ (fun i => s.1 (e i : α)) (fun i => (e i : α)) y :=
            le_iSup₂_of_le (e.symm ⟨y, hymem⟩) hei le_rfl

/-- `W_Q` is a quotient of the polynomial functor `WQP` — a QPF. -/
noncomputable instance qpfWQ : QPF (WQObj Q κ) where
  map f s := WQMap f s
  P := WQP Q κ
  abs := absWQ
  repr s := (reprWQ s).1
  abs_repr s := (reprWQ s).2
  abs_map f p := by
    apply Subtype.ext
    show pushQ p.1.2 (f ∘ p.2) = pushQ (pushQ p.1.2 p.2) f
    exact pushQ_comp p.1.2 p.2 f

/-! ## §4 Coalgebras, terminality, Lambek, bisimulation (Layer A step 3, Layer B) -/

/-- A `W_Q`-coalgebra. -/
structure WQCoalg (Q : Type u) [CompleteLattice Q] (κ : Cardinal.{u}) where
  X : Type u
  str : X → WQObj Q κ X

/-- Terminality in `Coalg (W_Q)`. -/
def IsTerminalWQ (U : WQCoalg Q κ) : Prop :=
  ∀ C : WQCoalg Q κ, ∃! h : C.X → U.X, ∀ x, U.str (h x) = WQMap h (C.str x)

/-- The concrete carrier `νW_Q = Cofix (W_Q)`. -/
noncomputable def νWQ (Q : Type u) [CompleteLattice Q] (κ : Cardinal.{u}) : WQCoalg Q κ :=
  ⟨Cofix (WQObj Q κ), Cofix.dest⟩

/-- **Existence of the enriched carrier (step 3).** `νW_Q` is terminal, via the
`Cofix` universal property — the same axiom-free route as `ws1`/`ws2`. -/
theorem νWQ_terminal (Q : Type u) [CompleteLattice Q] (κ : Cardinal.{u}) :
    IsTerminalWQ (νWQ Q κ) := by
  intro C
  refine ⟨Cofix.corec C.str, fun x => Cofix.dest_corec C.str x, ?_⟩
  intro h hh
  funext x
  refine Cofix.bisim' (fun _ => True) h (Cofix.corec C.str) ?_ x trivial
  intro y _
  refine ⟨(QPF.repr (C.str y)).1,
          (fun i => h ((QPF.repr (C.str y)).2 i)),
          (fun i => Cofix.corec C.str ((QPF.repr (C.str y)).2 i)), ?_, ?_, ?_⟩
  · calc Cofix.dest (h y)
        = WQMap h (C.str y) := hh y
      _ = h <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]; rfl
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst, fun i => h ((QPF.repr (C.str y)).snd i)⟩ := by
            rw [← QPF.abs_map]; rfl
  · calc Cofix.dest (Cofix.corec C.str y)
        = Cofix.corec C.str <$> C.str y := Cofix.dest_corec C.str y
      _ = Cofix.corec C.str <$> QPF.abs (QPF.repr (C.str y)) := by rw [QPF.abs_repr]
      _ = QPF.abs ⟨(QPF.repr (C.str y)).fst,
            fun i => Cofix.corec C.str ((QPF.repr (C.str y)).snd i)⟩ := by rw [← QPF.abs_map]; rfl
  · intro i
    exact ⟨(QPF.repr (C.str y)).2 i, trivial, rfl, rfl⟩

/-- Uniqueness clause of terminality, reused below. -/
lemma wq_hom_unique {U : WQCoalg Q κ} (hU : IsTerminalWQ U) (C : WQCoalg Q κ)
    {h₁ h₂ : C.X → U.X}
    (n₁ : ∀ x, U.str (h₁ x) = WQMap h₁ (C.str x))
    (n₂ : ∀ x, U.str (h₂ x) = WQMap h₂ (C.str x)) : h₁ = h₂ :=
  (hU C).unique n₁ n₂

/-- The unique coalgebra endomorphism of a terminal coalgebra is the identity. -/
lemma wq_endo_eq_id {U : WQCoalg Q κ} (hU : IsTerminalWQ U) (h : U.X → U.X)
    (hh : ∀ x, U.str (h x) = WQMap h (U.str x)) : h = id :=
  wq_hom_unique hU U hh (fun x => by show U.str x = WQMap id (U.str x); rw [WQMap_id])

/-- **Lambek (step 4).** The structure map of a terminal `W_Q`-coalgebra is a
bijection. -/
theorem wqLambek {U : WQCoalg Q κ} (hU : IsTerminalWQ U) : Function.Bijective U.str := by
  obtain ⟨g, hg, -⟩ := hU ⟨WQObj Q κ U.X, WQMap U.str⟩
  have hgU : (fun x => g (U.str x)) = id := by
    apply wq_endo_eq_id hU
    intro x
    calc U.str ((fun x => g (U.str x)) x)
        = WQMap g (WQMap U.str (U.str x)) := hg (U.str x)
      _ = WQMap (fun x => g (U.str x)) (U.str x) := (WQMap_comp g U.str (U.str x)).symm
  have left : Function.LeftInverse g U.str := fun x => congrFun hgU x
  have right : Function.RightInverse g U.str := by
    intro y
    calc U.str (g y)
        = WQMap g (WQMap U.str y) := hg y
      _ = WQMap (fun x => g (U.str x)) y := (WQMap_comp g U.str y).symm
      _ = WQMap id y := by rw [hgU]
      _ = y := WQMap_id y
  exact ⟨left.injective, right.surjective⟩

/-- A `W_Q`-bisimulation. -/
structure WQBisim (C : WQCoalg Q κ) (R : C.X → C.X → Prop) where
  ζ : {p : C.X × C.X // R p.1 p.2} → WQObj Q κ {p : C.X × C.X // R p.1 p.2}
  nat_fst : ∀ p, C.str p.1.1 = WQMap (fun q => q.1.1) (ζ p)
  nat_snd : ∀ p, C.str p.1.2 = WQMap (fun q => q.1.2) (ζ p)

/-- **Bisimulation = identity (step 5).** In a terminal `W_Q`-coalgebra every
bisimulation is contained in the diagonal. -/
theorem wq_bisim_eq {U : WQCoalg Q κ} (hU : IsTerminalWQ U)
    (R : U.X → U.X → Prop) (hR : WQBisim U R) : ∀ x y, R x y → x = y := by
  intro x y hxy
  have h := wq_hom_unique hU ⟨{p : U.X × U.X // R p.1 p.2}, hR.ζ⟩
    (h₁ := fun q => q.1.1) (h₂ := fun q => q.1.2) hR.nat_fst hR.nat_snd
  exact congrFun h ⟨(x, y), hxy⟩

/-- The diagonal is a bisimulation (⇐ half of behavioural equivalence). -/
def wqDiagBisim (U : WQCoalg Q κ) : WQBisim U (fun a b => a = b) where
  ζ := fun p => WQMap (fun z => (⟨(z, z), rfl⟩ : {q : U.X × U.X // q.1 = q.2})) (U.str p.1.1)
  nat_fst := fun p => by
    rw [← WQMap_comp]; exact (WQMap_id _).symm
  nat_snd := fun p => by
    have hp : p.1.1 = p.1.2 := p.2
    rw [← WQMap_comp, ← hp]; exact (WQMap_id _).symm

/-- **Behavioural equivalence = identity** on the terminal enriched carrier. -/
theorem wq_bisim_behavioural {U : WQCoalg Q κ} (hU : IsTerminalWQ U) (x y : U.X) :
    (∃ R, Nonempty (WQBisim U R) ∧ R x y) ↔ x = y := by
  constructor
  · rintro ⟨R, ⟨hR⟩, hxy⟩
    exact wq_bisim_eq hU R hR x y hxy
  · rintro rfl
    exact ⟨(fun a b => a = b), ⟨wqDiagBisim U⟩, rfl⟩

end Functor

end Series3.WS4
