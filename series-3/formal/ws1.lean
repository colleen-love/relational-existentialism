/-
`series-3/formal/ws1.lean`

Formalization of the WS1 design document
(`series-3/spec/ws1/4-charter-design-review.md`): **the Groundless Carrier** —
the terminal coalgebra of the κ-bounded powerset functor `P_κ`, its Lambek iso,
the bisimulation = identity theorem, the canonical self-membered inhabitant
`Ω = {Ω}`, and the C2 solution lemma built on top of it.

## Outcome status — the WS1 existence obligation is NOT discharged here

Read this first. The charter's WS1 deliverable (§4, §6 deliverable 2) is an
EXISTENCE/uniqueness theorem for the carrier. This file does NOT prove it: the
existence of the carrier is ASSUMED, via `exists_terminal_coalg`, not derived. So
against the charter obligation this artifact is a CONDITIONAL result, not a
discharge — everything here holds "*given* terminality of `P_κ`". Concretely:

* Downstream consumers MUST NOT cite `ws1_C1` as establishing that the carrier
  exists. It may be cited only as: "*given* terminality of `P_κ`, the carrier has
  these bundled properties (Lambek iso, bisim = identity, non-degeneracy, Ω)."
* The WS1↔WS7 boundedness drift (Commitment 1 realized against bounded `P_κ`, not
  charter §3.1's full-powerset/AFA carrier — §0.1, §8) is a separate, openly
  declared concession and remains open regardless of the above.

Everything BELOW terminality is genuine, unconditional-given-terminality,
sorry-free mathematics (see the axiom accounting next). The critical path to
actually discharging existence is recorded at the end of this header.

## What is proved sorry-free

This file has NO `sorry` and exactly ONE `axiom` (`exists_terminal_coalg`).
Everything below is proved from it (and Mathlib's standard axioms):

* Lemma 1.1  functoriality of `P_κ`               (`PkMap_id`, `PkMap_comp`)
* Lemma 2.3  Lambek's lemma (`struct` is an iso)  (`lambek`)
* Theorem 3.2 bisimulation = equality             (`bisim_eq`)
* §3.3       non-degeneracy (`∃ a b, a ≠ b`)      (inside `ws1_C1`)
* Theorem 4.1 `Ω = {Ω}`                            (`omega_selfsingleton` field)
* §5         the assembled `GroundlessCarrier`     (`ws1_C1`)
* Theorem 6.2/6.3 the solution lemma               (`ws1_C2`)
* Lemma 6.4  Ω-consistency of the two Ω routes     (`omega_consistency`)

## Where the axiom boundary sits — and how it differs from the design's

An earlier revision of this header claimed to "mirror exactly" the design's one
sanctioned black box. That was inaccurate: `exists_terminal_coalg` assumes
STRICTLY MORE than the sanctioned axiom, and the difference is material. The
honest accounting:

* The design (§2.2, §7 item 1) sanctions ONE external black box, the
  Worrell / Adámek–Koubek **`stabilization_theorem`**. Its REGISTERED signature
  is stated for a general functor `F` under `hacc` (κ-accessibility = Lemma 1.2)
  and `hbdd` (κ-boundedness), and it concludes ONLY a stabilizing ordinal — an
  iso on a connecting map of the terminal sequence — NOT terminality:

      axiom stabilization_theorem (F) (κ) (hκ_reg) (hκ_inf) (hacc) (hbdd) :
        ∃ α : Ordinal, α ≤ κ.ord ∧ IsIso (finalSeq.connectingMap F (α+1) α)

  From that iso the design *derives* terminality in **Corollary 2.2**, whose two
  transfinite arguments — cone-map existence (recursion) and cone-map uniqueness
  (induction) — §7 ranks as **tier-2 risk, co-equal with the stabilization
  theorem itself**. **Lemma 1.2** (κ-accessibility of `P_κ`, feeding `hacc`) is a
  further registered obligation ("probably a genuine new proof").

* `exists_terminal_coalg` below is DOWNSTREAM of that boundary: it asserts
  `∃ U, IsTerminalCoalg U` outright. Relative to the design's registered axiom it
  therefore ASSUMES rather than discharges three registered obligations, which
  stay on this open ledger:

      (L1.2)  Lemma 1.2      — κ-accessibility of `P_κ`         [assumed]
      (C2.∃)  Corollary 2.2  — cone-map existence  (recursion)  [assumed]
      (C2.!)  Corollary 2.2  — cone-map uniqueness (induction)  [assumed, §7 tier-2]

  So the HONEST status of `ws1_C1` is: *conditional on terminality-of-`P_κ` — a
  strictly stronger hypothesis than the sanctioned `stabilization_theorem` — and
  against the bounded reading of Commitment 1 (§0.1).* The downstream mathematics
  is nonetheless sound and independent of this: `#print axioms` shows
  `lambek` / `bisim_eq` / `ws1_C2` / `omega_consistency` use ONLY Mathlib's
  standard axioms; the existence axiom enters solely through `ws1_C1`.

* Closing the gap — TWO candidate routes; both are scoped, from-scratch
  developments, deliberately NOT attempted in this revision:

  ROUTE 1 (design-faithful, §2.1–§2.2; RELOCATES the axiom to the sanctioned
  boundary). Restate the axiom as the design's `stabilization_theorem` — a
  stabilizing iso on `finalSeq.connectingMap` under `hacc`/`hbdd` — construct
  `finalSeq` per §2.1, and PROVE `IsTerminalCoalg` from it via the Corollary 2.2
  inductions, moving (C2.∃)/(C2.!) from this ledger to theorems and leaving only
  (L1.2). PREREQUISITE (from §2.2, its own signed-off sub-task): pin the exact
  stabilization bound `α ≤ κ.ord` against Worrell / Adámek–Milius–Moss BEFORE any
  Lean work — a wrong bound would typecheck against a false external fact with no
  local proof to catch it. This is the design's "single most expensive
  sub-formalization" (simultaneous transfinite recursion of the sequence + its
  connecting maps; limit-stage uniqueness invariant).

  ROUTE 2 (Mathlib QPF; ELIMINATES the axiom entirely — no ordinals, no
  stabilization). Bounded powerset over a FIXED `κ` is a quotient of a polynomial
  functor: shapes `κ.ord.toType`, positions the initial segments below each shape
  (each of cardinality `< κ`, since `κ.ord` is the least ordinal of cardinality
  `κ`), `abs = Set.range`. Exhibiting that as a `Mathlib.Data.QPF.Univariate.QPF`
  instance yields `Cofix P_κ` with `Cofix.dest` (structure map), `Cofix.corec`
  (the cone map, giving existence + `Cofix.dest_corec`), and `Cofix.bisim`
  (bisimulation ⇒ equality, UNCONDITIONAL — no uniformity needed) — from which
  `IsTerminalCoalg (Cofix P_κ)` is a THEOREM and `exists_terminal_coalg` is
  deleted outright. Cost sits in the QPF instance (the `abs_repr` surjective
  enumeration; the `< κ` cardinality bookkeeping) and in bridging `Cofix`'s
  bisimulation API to `IsTerminalCoalg`'s uniqueness clause. (The earlier header
  claim that "M-types cover only polynomial functors, which bounded `P_κ` is not"
  was too quick: `P_κ` is not polynomial but IS a quotient of one — a QPF — which
  is exactly what Mathlib's `QPF`/`Cofix` machinery is built for.)

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

/-! ## §2 Existence of the carrier — the assumed hypothesis (see the header ledger)

`exists_terminal_coalg` asserts the CONCLUSION of the design's entire §2 —
stabilization AND the Corollary 2.2 terminality derivation — together with
Lemma 1.2 (κ-accessibility). It is therefore STRONGER than the design's one
sanctioned black box, the `stabilization_theorem` of §2.2, whose registered
signature concludes only a stabilizing iso on the terminal sequence, not
terminality. The three registered obligations this axiom folds in —

    (L1.2) Lemma 1.2,  (C2.∃) Corollary 2.2 existence,  (C2.!) Corollary 2.2 uniqueness

— are ASSUMED here, not discharged; they stay on the open-obligations ledger in
the file header. Nothing else in this file is axiomatic. See the header for the
registered-boundary statement and the (deliberately deferred) path to closing the
gap. -/
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
`κ`. HONEST STATUS (per the header ledger): conditional on `exists_terminal_coalg`,
i.e. on terminality-of-`P_κ` — a hypothesis strictly STRONGER than the design's
sanctioned `stabilization_theorem`, since it folds in Lemma 1.2 and both halves of
Corollary 2.2 (the §7 tier-2 transfinite inductions), left un-discharged — and
stated against the bounded reading of Commitment 1 (§0.1). Downstream of that
hypothesis the assembly is fully proved; the non-degeneracy, Lambek, bisim=identity
and Ω facts it bundles do not themselves depend on the axiom beyond terminality. -/
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
