/-
`series-3/formal/ws1.lean`

Formalization of the WS1 design document
(`series-3/spec/ws1/4-charter-design-review.md`): **the Groundless Carrier** —
the terminal coalgebra of the κ-bounded powerset functor `P_κ`, its Lambek iso,
the bisimulation = identity theorem, the canonical self-membered inhabitant
`Ω = {Ω}`, and the C2 solution lemma built on top of it.

## What is proved vs. what is assumed

The design is explicit (§2.1–§2.2, §7 item 1) that existence of the terminal
`P_κ`-coalgebra rests on ONE external black box — the Worrell / Adámek–Koubek
stabilization theorem — which the design itself carries as `axiom
stabilization_theorem`, calling it "the single most expensive sub-formalization
in WS1" and leaving it axiomatic with a TODO. We mirror exactly that one
sanctioned concession here as `exists_terminal_coalg`, and prove EVERYTHING
downstream of it sorry-free:

* Lemma 1.1  functoriality of `P_κ`               (`PkMap_id`, `PkMap_comp`)
* Lemma 2.3  Lambek's lemma (`struct` is an iso)  (`lambek`)
* Theorem 3.2 bisimulation = equality             (`bisim_eq`)
* §3.3       non-degeneracy (`∃ a b, a ≠ b`)      (inside `ws1_C1`)
* Theorem 4.1 `Ω = {Ω}`                            (`omega_selfsingleton` field)
* §5         the assembled `GroundlessCarrier`     (`ws1_C1`)
* Theorem 6.2/6.3 the solution lemma               (`ws1_C2`)
* Lemma 6.4  Ω-consistency of the two Ω routes     (`omega_consistency`)

## Standing hypothesis (§0.1, §1.1)

Everything is stated for the *bounded* functor `P_κ` — the declared WS1↔WS7
drift away from charter §3.1's full-powerset carrier — under the standing
hypothesis that `κ` is an infinite regular cardinal. Regularity (`hreg`) feeds
ONLY the existence axiom (its true job, §1.2/§2); every downstream cardinality
bound uses only `ℵ₀ ≤ κ` ("κ infinite", the `hκ_inf` of §1.1), exactly as the
revision's note demands.
-/
import Mathlib

universe u

namespace Series3.WS1

open Cardinal

variable {κ : Cardinal.{u}}

/-! ## §1.1 The κ-bounded powerset functor `P_κ` -/

/-- `PkObj κ X` — the subsets of `X` of cardinality `< κ` (§1.1, `P_κ.obj X`). -/
def PkObj (κ : Cardinal.{u}) (X : Type u) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}

/-- The functorial action of `P_κ` on maps (§1.1, `P_κ.map`). Well-defined because
the image of a `< κ`-sized set is `< κ`-sized — the design's `image_card_lt`. -/
def PkMap (κ : Cardinal.{u}) {X Y : Type u} (f : X → Y) (s : PkObj κ X) : PkObj κ Y :=
  ⟨f '' s.1, lt_of_le_of_lt Cardinal.mk_image_le s.2⟩

@[simp] lemma PkMap_val {X Y : Type u} (f : X → Y) (s : PkObj κ X) :
    (PkMap κ f s).1 = f '' s.1 := rfl

/-- Lemma 1.1 (functoriality) — identity. -/
@[simp] lemma PkMap_id {X : Type u} (s : PkObj κ X) : PkMap κ (id : X → X) s = s := by
  apply Subtype.ext; simp [PkMap]

/-- Lemma 1.1 (functoriality) — composition. -/
lemma PkMap_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) (s : PkObj κ X) :
    PkMap κ (g ∘ f) s = PkMap κ g (PkMap κ f s) := by
  apply Subtype.ext
  show (g ∘ f) '' s.1 = g '' (f '' s.1)
  exact Set.image_comp g f s.1

/-- `∅` is a legal `P_κ`-element (needs only `0 < κ`, from `ℵ₀ ≤ κ`). -/
lemma mk_empty_lt {α : Type u} (hinf : ℵ₀ ≤ κ) : Cardinal.mk (↥(∅ : Set α)) < κ := by
  haveI : IsEmpty (↥(∅ : Set α)) := ⟨fun x => (Set.mem_empty_iff_false _).mp x.2⟩
  rw [Cardinal.mk_eq_zero]
  exact lt_of_lt_of_le Cardinal.aleph0_pos hinf

/-- A singleton is a legal `P_κ`-element (needs `1 < κ`, i.e. `κ` infinite — the
`hκ_inf` justification the design pins at §1.1 and §4). -/
lemma mk_singleton_lt {α : Type u} (hinf : ℵ₀ ≤ κ) (a : α) :
    Cardinal.mk (↥({a} : Set α)) < κ := by
  rw [Cardinal.mk_singleton]
  exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf

/-! ## §1.2 Coalgebras and terminality -/

/-- A `P_κ`-coalgebra: a carrier `X` with a structure map `X → P_κ X` (§1.2). -/
structure Coalg (κ : Cardinal.{u}) where
  X : Type u
  str : X → PkObj κ X

/-- `U` is **terminal** in `Coalg P_κ` (Lemma 1.3 / §2.2): from every coalgebra
there is a unique coalgebra morphism into `U`. A function `h : C.X → U.X` is a
coalgebra morphism `C → U` exactly when it commutes with the structure maps. -/
def IsTerminalCoalg (U : Coalg κ) : Prop :=
  ∀ C : Coalg κ, ∃! h : C.X → U.X, ∀ x, U.str (h x) = PkMap κ h (C.str x)

/-- Any two coalgebra morphisms into a terminal coalgebra coincide (the
uniqueness half of the universal property, used everywhere below). -/
lemma hom_unique {U : Coalg κ} (hU : IsTerminalCoalg U) (C : Coalg κ)
    {h₁ h₂ : C.X → U.X}
    (n₁ : ∀ x, U.str (h₁ x) = PkMap κ h₁ (C.str x))
    (n₂ : ∀ x, U.str (h₂ x) = PkMap κ h₂ (C.str x)) : h₁ = h₂ :=
  (hU C).unique n₁ n₂

/-- The unique coalgebra endomorphism of a terminal coalgebra is the identity —
the terminal-endomorphism fact reused in Lambek (§2.3) and Lemma 6.1a. -/
lemma endo_eq_id {U : Coalg κ} (hU : IsTerminalCoalg U) (h : U.X → U.X)
    (hh : ∀ x, U.str (h x) = PkMap κ h (U.str x)) : h = id :=
  hom_unique hU U hh (fun x => by simp)

/-! ## §2.3 Lambek's lemma -/

/-- Lemma 2.3 (Lambek). The structure map of a terminal coalgebra is a bijection
(the iso `U ≃ P_κ U`). This also discharges failure mode (iii) as a corollary
(§3.4: surjectivity of `struct` is free once Lambek is in hand). -/
theorem lambek {U : Coalg κ} (hU : IsTerminalCoalg U) : Function.Bijective U.str := by
  -- `g` is the unique coalgebra morphism out of `(P_κ U, P_κ struct)`.
  obtain ⟨g, hg, -⟩ := hU ⟨PkObj κ U.X, PkMap κ U.str⟩
  -- `g ∘ struct` is a coalgebra endomorphism of `U`, hence the identity.
  have hgU : (fun x => g (U.str x)) = id := by
    apply endo_eq_id hU
    intro x
    calc U.str ((fun x => g (U.str x)) x)
        = U.str (g (U.str x)) := rfl
      _ = PkMap κ g (PkMap κ U.str (U.str x)) := hg (U.str x)
      _ = PkMap κ (fun x => g (U.str x)) (U.str x) := (PkMap_comp g U.str (U.str x)).symm
  have left : Function.LeftInverse g U.str := fun x => congrFun hgU x
  -- `struct ∘ g = P_κ (g ∘ struct) = P_κ id = id`, so `g` is also a right inverse.
  have right : Function.RightInverse g U.str := by
    intro y
    calc U.str (g y)
        = PkMap κ g (PkMap κ U.str y) := hg y
      _ = PkMap κ (fun x => g (U.str x)) y := (PkMap_comp g U.str y).symm
      _ = PkMap κ id y := by rw [hgU]
      _ = y := PkMap_id y
  exact ⟨left.injective, right.surjective⟩

/-! ## §3 Identity: bisimulation = equality -/

/-- An `F`-bisimulation on a coalgebra `C` (§3.1): a coalgebra structure on the
graph of `R` making both projections coalgebra morphisms. -/
structure Bisim (C : Coalg κ) (R : C.X → C.X → Prop) where
  ζ : {p : C.X × C.X // R p.1 p.2} → PkObj κ {p : C.X × C.X // R p.1 p.2}
  nat_fst : ∀ p, C.str p.1.1 = PkMap κ (fun q => q.1.1) (ζ p)
  nat_snd : ∀ p, C.str p.1.2 = PkMap κ (fun q => q.1.2) (ζ p)

/-- Theorem 3.2 (`bisim_eq`). In a terminal coalgebra every bisimulation is
contained in the diagonal — bisimilarity IS equality. Terminality does all the
work: the two graph projections are coalgebra morphisms into `U`, hence equal. -/
theorem bisim_eq {U : Coalg κ} (hU : IsTerminalCoalg U)
    (R : U.X → U.X → Prop) (hR : Bisim U R) : ∀ x y, R x y → x = y := by
  intro x y hxy
  have h := hom_unique hU ⟨{p : U.X × U.X // R p.1 p.2}, hR.ζ⟩
    (h₁ := fun q => q.1.1) (h₂ := fun q => q.1.2) hR.nat_fst hR.nat_snd
  exact congrFun h ⟨(x, y), hxy⟩

/-! ## §4 The canonical inhabitant Ω, and §3.3 non-degeneracy witnesses -/

/-- Ω's defining coalgebra (§4): the one-node self-loop `∗ ↦ {∗}`. -/
def omegaCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨PUnit, fun _ => ⟨{PUnit.unit}, mk_singleton_lt hinf _⟩⟩

/-- The one-node graph with the empty relation, `∗ ↦ ∅` (§3.3, coalgebra `A`). -/
def emptyCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ :=
  ⟨PUnit, fun _ => ⟨∅, mk_empty_lt hinf⟩⟩

/-! ## §2 Existence of the carrier — the one sanctioned black box

The design derives existence of the terminal `P_κ`-coalgebra from the
stabilization theorem, which it carries as `axiom stabilization_theorem`
(§2.1–§2.2, §7 item 1: "the single most expensive sub-formalization", left
axiomatic with a TODO). We mirror exactly that concession: for an infinite
regular `κ`, a terminal coalgebra exists. Nothing else below is axiomatic. -/
axiom exists_terminal_coalg (κ : Cardinal.{u}) (hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ) :
    ∃ U : Coalg κ, IsTerminalCoalg U

/-! ## §5 The target structure `GroundlessCarrier` and `ws1_C1` -/

/-- C1's target (§5). Bundles: terminality (`final`), the Lambek iso (`lambek`),
bisimulation = identity (`bisim_eq`), non-degeneracy (`nondegenerate`, the [NEW]
field this revision folds in), and the canonical self-membered `omega` together
with `omega_selfsingleton`. -/
structure GroundlessCarrier (κ : Cardinal.{u}) where
  carrier : Coalg κ
  final : IsTerminalCoalg carrier
  lambek : Function.Bijective carrier.str
  bisim_eq : ∀ R : carrier.X → carrier.X → Prop, Bisim carrier R → ∀ x y, R x y → x = y
  nondegenerate : ∃ a b : carrier.X, a ≠ b
  omega : carrier.X
  omega_selfsingleton : (carrier.str omega).1 = {omega}

/-- Theorem `ws1_C1` (§5): a `GroundlessCarrier` exists for every infinite regular
`κ`. Conditional on `exists_terminal_coalg` (the design's `stabilization_theorem`)
and stated against the bounded reading of Commitment 1 (§0.1), exactly as §5's
[DRIFT NOTE] instructs it be reported. -/
theorem ws1_C1 (hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ) :
    Nonempty (GroundlessCarrier κ) := by
  obtain ⟨U, hU⟩ := exists_terminal_coalg κ hreg hinf
  -- the unique morphisms out of the Ω-coalgebra and the empty coalgebra
  obtain ⟨hΩ, hΩnat, -⟩ := hU (omegaCoalg hinf)
  obtain ⟨hE, hEnat, -⟩ := hU (emptyCoalg hinf)
  -- Theorem 4.1: `Ω = {Ω}`.
  have hsω : (U.str (hΩ PUnit.unit)).1 = {hΩ PUnit.unit} := by
    rw [hΩnat PUnit.unit]; simp [PkMap, omegaCoalg]
  -- the empty coalgebra maps to an atom with empty structure
  have hsE : (U.str (hE PUnit.unit)).1 = (∅ : Set U.X) := by
    rw [hEnat PUnit.unit]; simp [PkMap, emptyCoalg]
  -- §3.3 non-degeneracy: the two images differ (∅ ≠ a nonempty singleton).
  have hne : hE PUnit.unit ≠ hΩ PUnit.unit := by
    intro heq
    have hcontra : (U.str (hE PUnit.unit)).1 = {hΩ PUnit.unit} := by rw [heq]; exact hsω
    rw [hsE] at hcontra
    have hmem : hΩ PUnit.unit ∈ (∅ : Set U.X) := by rw [hcontra]; rfl
    exact Set.not_mem_empty _ hmem
  exact ⟨{ carrier := U
         , final := hU
         , lambek := lambek hU
         , bisim_eq := fun R hR => bisim_eq hU R hR
         , nondegenerate := ⟨hE PUnit.unit, hΩ PUnit.unit, hne⟩
         , omega := hΩ PUnit.unit
         , omega_selfsingleton := hsω }⟩

/-! ## §6 C2: the solution lemma -/

/-- §6.1 The system coalgebra on `I ⊕ U` for a system `e : I → P_κ (I ⊕ U)`. The
`inl` branch is `e` directly (the [REVISED] correction — no reindexing map); the
`inr` branch pushes `U`'s own structure along `inr`. -/
def systemCoalg {U : Coalg κ} (I : Type u) (e : I → PkObj κ (I ⊕ U.X)) : Coalg κ :=
  ⟨I ⊕ U.X, Sum.elim e (fun u => PkMap κ Sum.inr (U.str u))⟩

/-- Theorem 6.2 + 6.3 (`ws1_C2_solutionLemma`): every system `e` has a UNIQUE
solution `sol`. Existence reuses terminality's cone map; uniqueness is
terminality's uniqueness clause verbatim — the payoff of having secured
*terminality* rather than a mere fixed point (§6). -/
theorem ws1_C2 {U : Coalg κ} (hU : IsTerminalCoalg U)
    (I : Type u) (e : I → PkObj κ (I ⊕ U.X)) :
    ∃! sol : I → U.X, ∀ i, (U.str (sol i)).1 = Sum.elim sol id '' (e i).1 := by
  obtain ⟨h, hnat, -⟩ := hU (systemCoalg I e)
  -- Lemma 6.1a: `inr` is a coalgebra morphism, so `h ∘ inr = id`.
  have hinr : (fun u => h (Sum.inr u)) = id := by
    apply endo_eq_id hU
    intro u
    calc U.str ((fun u => h (Sum.inr u)) u)
        = U.str (h (Sum.inr u)) := rfl
      _ = PkMap κ h (PkMap κ Sum.inr (U.str u)) := hnat (Sum.inr u)
      _ = PkMap κ (fun u => h (Sum.inr u)) (U.str u) := (PkMap_comp h Sum.inr (U.str u)).symm
  set sol : I → U.X := fun i => h (Sum.inl i) with hsoldef
  -- `h` agrees with `Sum.elim sol id` (inl by definition of `sol`, inr by 6.1a).
  have hSplit : h = Sum.elim sol id := by
    funext z
    cases z with
    | inl i => rfl
    | inr u => exact congrFun hinr u
  refine ⟨sol, ?_, ?_⟩
  · -- existence (Theorem 6.2)
    intro i
    calc (U.str (sol i)).1
        = (PkMap κ h (e i)).1 := by rw [show U.str (sol i) = PkMap κ h (e i) from hnat (Sum.inl i)]
      _ = h '' (e i).1 := rfl
      _ = Sum.elim sol id '' (e i).1 := by rw [hSplit]
  · -- uniqueness (Theorem 6.3)
    intro sol' hsol'
    have hmor : ∀ z, U.str (Sum.elim sol' id z)
        = PkMap κ (Sum.elim sol' id) ((systemCoalg I e).str z) := by
      intro z
      cases z with
      | inl i =>
        apply Subtype.ext
        show (U.str (sol' i)).1 = Sum.elim sol' id '' (e i).1
        exact hsol' i
      | inr u =>
        show U.str u = PkMap κ (Sum.elim sol' id) (PkMap κ Sum.inr (U.str u))
        rw [← PkMap_comp]
        have hcomp : (Sum.elim sol' id) ∘ Sum.inr = id := by funext u; rfl
        rw [hcomp, PkMap_id]
    have heq := hom_unique hU (systemCoalg I e) hmor hnat
    funext i
    exact congrFun heq (Sum.inl i)

/-- Lemma 6.4 (Ω-consistency, §6.3). Specialising the system lemma to `I = PUnit`,
`e ∗ = {inl ∗}`, its solution at `∗` is exactly the `Ω` built in §4. The design
flags this as *not* free: it is the explicit gluing of the two morphisms
(`sol` out of `Unit ⊕ U`, `hΩ` out of `PUnit`), and it uses terminal uniqueness
exactly once. -/
theorem omega_consistency {U : Coalg κ} (hU : IsTerminalCoalg U) (hinf : ℵ₀ ≤ κ)
    (sol : PUnit.{u+1} → U.X)
    (hsoleq : ∀ i, (U.str (sol i)).1
      = Sum.elim sol id '' ({Sum.inl PUnit.unit} : Set (PUnit.{u+1} ⊕ U.X)))
    (hΩ : PUnit.{u+1} → U.X)
    (hΩnat : ∀ x, U.str (hΩ x) = PkMap κ hΩ ((omegaCoalg hinf).str x)) :
    sol PUnit.unit = hΩ PUnit.unit := by
  -- `sol` is itself a coalgebra morphism `omegaCoalg → U`, because its defining
  -- equation says `struct (sol ∗) = {sol ∗}` — the naturality square for Ω.
  have hmor : ∀ x, U.str (sol x) = PkMap κ sol ((omegaCoalg hinf).str x) := by
    intro x
    have hx : x = PUnit.unit := Subsingleton.elim x PUnit.unit
    subst hx
    apply Subtype.ext
    show (U.str (sol PUnit.unit)).1 = sol '' ({PUnit.unit} : Set PUnit.{u+1})
    rw [hsoleq PUnit.unit]
    simp
  -- terminal uniqueness forces `sol = hΩ`.
  have heq := hom_unique hU (omegaCoalg hinf) hmor hΩnat
  exact congrFun heq PUnit.unit

end Series3.WS1
