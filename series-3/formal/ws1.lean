/-
`series-3/formal/ws1.lean`

Formalization of the WS1 design document
(`series-3/spec/ws1/4-charter-design-review.md`): **the Groundless Carrier** —
the terminal coalgebra of the κ-bounded powerset functor `P_κ`, its Lambek iso,
the bisimulation = identity theorem, the canonical self-membered inhabitant
`Ω = {Ω}`, and the C2 solution lemma built on top of it.

## Outcome status — the WS1 existence obligation IS discharged, with NO axioms

The charter's WS1 deliverable (§4, §6 deliverable 2) is an existence/uniqueness
theorem for the carrier. This file PROVES it: `exists_terminal_coalg` is a
theorem (not an axiom), and the whole file is free of custom axioms — every result
rests only on Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`
(verify with `#print axioms ws1_C1`).

Existence is obtained NOT by the design's transfinite terminal-sequence route
(§2.1–§2.2, which keeps `stabilization_theorem` a permanent axiom) but by a
cleaner one that removes the black box entirely: bounded powerset over a FIXED `κ`
is a **quotient of a polynomial functor** (a `QPF`), so Mathlib's `Cofix` machinery
returns its terminal coalgebra directly. Details are at `§2` below. Consequences:

* `ws1_C1` may be cited by downstream workstreams as genuinely establishing that
  the carrier EXISTS (with all bundled properties: Lambek iso, bisim = identity,
  non-degeneracy, Ω) — no conditionality, no assumed terminality.
* Existence needs NO hypothesis on `κ`; `hreg`/`hinf` are used only downstream, for
  the `Ω = {Ω}` singleton and non-degeneracy witnesses.
* The one remaining charter caveat is the DECLARED WS1↔WS7 bounded-carrier drift
  (§0.1, §8): Commitment 1 is realized against bounded `P_κ`, not charter §3.1's
  full-powerset / AFA carrier. That is an openly declared modeling choice, not an
  unproved proof obligation, and is unaffected by the above.

Historical note: earlier revisions of this file carried an `exists_terminal_coalg`
AXIOM (asserting terminality of `P_κ` outright), which — as review correctly
flagged — sat strictly downstream of the design's sanctioned `stabilization_theorem`
boundary and left the WS1 existence obligation assumed rather than derived. That
axiom has now been discharged via the QPF/`Cofix` route below and deleted.

## What is proved sorry-free (all axiom-free beyond Mathlib's standard three)

* §2         existence: `Cofix (P_κ)` is terminal          (`exists_terminal_coalg`)
             via the QPF instance `qpfPk` (`PkP`, `absPk`, `reprPk`)
* Lemma 1.1  functoriality of `P_κ`               (`PkMap_id`, `PkMap_comp`)
* Lemma 2.3  Lambek's lemma (`struct` is an iso)  (`lambek`)
* Theorem 3.2 bisimulation = equality             (`bisim_eq`)
* §3.3       non-degeneracy (`∃ a b, a ≠ b`)      (inside `ws1_C1`)
* Theorem 4.1 `Ω = {Ω}`                            (`omega_selfsingleton` field)
* §5         the assembled `GroundlessCarrier`     (`ws1_C1`)
* Theorem 6.2/6.3 the solution lemma               (`ws1_C2`)
* Lemma 6.4  Ω-consistency of the two Ω routes     (`omega_consistency`)

## A registered dependency that does NOT appear here (Lemma 3.1a)

The `bisim_eq` field proves Theorem 3.2 exactly — "every bisimulation ⊆ the
diagonal" — which follows from terminality alone. The design's Lemma 3.1a
(`P_κ` preserves weak pullbacks) and Lemma 3.1 (`bisimEquiv` is an equivalence
relation, transitivity via 3.1a) are needed only for the *greatest-bisimulation*
packaging, which the `GroundlessCarrier` signature does not use; they are neither
needed nor formalized here. This matches Theorem 3.2's registered signature and is
not a weakening of it, but is flagged so nobody expects 3.1a in this file.

## Standing hypothesis (§0.1, §1.1)

Everything is stated for the *bounded* functor `P_κ` — the declared WS1↔WS7
drift away from charter §3.1's full-powerset carrier. `ws1_C1` carries the
charter's "infinite regular `κ`" hypotheses (`hreg`, `hinf`), but note that
EXISTENCE (`exists_terminal_coalg`) needs neither: the QPF/`Cofix` construction
works for any `κ`. The hypotheses are consumed only downstream — `ℵ₀ ≤ κ` for the
`Ω = {Ω}` singleton and non-degeneracy witnesses (`hκ_inf` of §1.1); regularity
is not needed anywhere on this route (it was the design's tool for the
stabilization/accessibility argument, which this route bypasses).
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

/-! ## §2 Existence of the carrier — PROVED (no axiom)

The design's §2.1–§2.2 route to existence (build the transfinite terminal
sequence `finalSeq`, then derive terminality from the `stabilization_theorem`
black box via the Corollary 2.2 inductions) keeps one permanent axiom. We take a
different, axiom-free route and DISCHARGE existence outright:

**`P_κ` (bounded powerset over a FIXED `κ`) is a quotient of a polynomial functor
— a `QPF` — so Mathlib's `Cofix` gives its terminal coalgebra directly.** The
polynomial functor `PkP κ` has shapes `κ.ord.toType` and, over a shape `a`, the
position type `{b // b < a}` (the initial segment below `a`); each such segment
has cardinality `< κ` precisely because `κ.ord` is the LEAST ordinal of
cardinality `κ` (`Ordinal.card_typein_toType_lt`). The quotient map `abs` is
`Set.range`, and `repr` enumerates a `< κ`-set `s` by the initial segment of
order-type `(#s).ord` (which lands in `κ.ord.toType` since `(#s).ord < κ.ord`).
`Cofix (P_κ)` is then a terminal `P_κ`-coalgebra by `Cofix.corec`/`Cofix.dest_corec`
(the unique cone map) and `Cofix.bisim'` (its uniqueness).

Consequences: `exists_terminal_coalg` is a THEOREM, not an axiom; the whole file
is free of custom axioms (only Mathlib's standard `propext`/`Classical.choice`/
`Quot.sound`); existence needs NO hypothesis on `κ` at all (regularity/infiniteness
are used only downstream, for the `Ω = {Ω}` singleton and non-degeneracy). The
former (L1.2)/(C2.∃)/(C2.!) ledger is discharged: none of stabilization,
κ-accessibility, or the transfinite inductions is needed on this route. -/
section Existence
open Ordinal Set QPF Functor

/-- The polynomial functor of which `P_κ` is a quotient: shapes `κ.ord.toType`,
positions the initial segments `{b // b < a}` (each of cardinality `< κ`). -/
def PkP (κ : Cardinal.{u}) : PFunctor.{u} where
  A := κ.ord.toType
  B a := {b : κ.ord.toType // b < a}

/-- `abs ⟨a, f⟩ := range f` — a `< κ`-sized subset (bound: image of a `< κ`
position type). -/
def absPk {α : Type u} (p : (PkP κ).Obj α) : PkObj κ α :=
  ⟨Set.range p.2, lt_of_le_of_lt Cardinal.mk_range_le (card_typein_toType_lt κ p.1)⟩

/-- `repr` of a `< κ`-set `s`: enumerate it by the initial segment of order-type
`(#s).ord`, available in `κ.ord.toType` because `(#s).ord < κ.ord`. The bundled
`range = s` proof is what makes `abs_repr` immediate. -/
noncomputable def reprPk {α : Type u} (s : PkObj κ α) :
    { p : (PkP κ).Obj α // Set.range p.2 = s.1 } := by
  have ho' : (Cardinal.mk (↥s.1)).ord < type (α := κ.ord.toType) (· < ·) := by
    rw [type_toType]; exact Cardinal.ord_lt_ord.mpr s.2
  set a : κ.ord.toType := enum (α := κ.ord.toType) (· < ·) ⟨(Cardinal.mk (↥s.1)).ord, ho'⟩ with ha
  have hcard : Cardinal.mk ((PkP κ).B a) = Cardinal.mk (↥s.1) := by
    have h1 : Cardinal.mk ((PkP κ).B a) = (typein (α := κ.ord.toType) (· < ·) a).card :=
      card_typein a
    rw [h1, ha, typein_enum, Cardinal.card_ord]
  let e : (PkP κ).B a ≃ ↥s.1 := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨⟨a, fun i => (e i : α)⟩, ?_⟩
  show Set.range (Subtype.val ∘ e) = s.1
  rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]

/-- `P_κ` is a quotient of the polynomial functor `PkP κ`. -/
noncomputable instance qpfPk : QPF (PkObj κ) where
  map f s := PkMap κ f s
  P := PkP κ
  abs := absPk
  repr s := (reprPk s).1
  abs_repr s := by
    apply Subtype.ext
    show Set.range (reprPk s).1.2 = s.1
    exact (reprPk s).2
  abs_map f p := by
    apply Subtype.ext
    show Set.range (f ∘ p.2) = f '' Set.range p.2
    exact Set.range_comp f p.2

/-- **Existence of the groundless carrier — the WS1 obligation, DISCHARGED.**
`Cofix (P_κ)` (with structure map `Cofix.dest`) is a terminal `P_κ`-coalgebra, for
every `κ`, with no axiom. Existence half of the cone map is `Cofix.corec`
(`Cofix.dest_corec` witnesses the morphism square); uniqueness is `Cofix.bisim'`,
with `repr (C.str y)` supplying the common shape. Replaces the former axiom. -/
theorem exists_terminal_coalg (κ : Cardinal.{u}) : ∃ U : Coalg κ, IsTerminalCoalg U := by
  refine ⟨⟨Cofix (PkObj κ), Cofix.dest⟩, ?_⟩
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
        = PkMap κ h (C.str y) := hh y
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

end Existence

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
`κ`, UNCONDITIONALLY — existence now rests on the proved `exists_terminal_coalg`
(the `Cofix (P_κ)` terminal coalgebra), not an axiom. `#print axioms ws1_C1` shows
only Mathlib's standard axioms. `hreg`/`hinf` are consumed only downstream, for the
`Ω = {Ω}` singleton and non-degeneracy — not for existence. The one remaining
charter caveat is the DECLARED WS1↔WS7 bounded-carrier drift (§0.1): Commitment 1
is realized against bounded `P_κ`, a modeling choice, not an unproved obligation. -/
theorem ws1_C1 (_hreg : κ.IsRegular) (hinf : ℵ₀ ≤ κ) :
    Nonempty (GroundlessCarrier κ) := by
  obtain ⟨U, hU⟩ := exists_terminal_coalg κ
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
