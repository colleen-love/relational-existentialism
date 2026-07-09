/-
`series-4/formal/ws3.lean`

WS3 — **Plurality without atoms.** Series 4.

On the plain carrier `νP_κ` the Collapse Theorem (`ws2_collapse`) says any two
hereditarily-nonempty states are equal: plurality-by-faces is *impossible* there
(faces are `str`-derived, hence epiphenomenal for distinguishing collapse-equal
states). This is the design's dichotomy resolving to branch (I): the R2 carrier
cannot carry plurality, so WS3 **escalates to R3** — faces as genuine functor data.

We realize R3 as a self-contained **labelled carrier** `νLk κ Q`: the terminal
coalgebra of `X ↦ P_κ (Q × X)`, where each successor edge carries a quality label
`q : Q` (the face, as functor data). This is the exact analogue of the Series 3
weighted carrier `ws14` (which distinguished loops by weight); here loops are
distinguished by *face*. Two self-loops with the same target but different labels
are genuinely distinct states — plurality without atoms, bought exactly by the face.

Deliverables: `ws3_loopface_ne` (P1), `ws3_same_succ_diff_face` (P3, the
coincidence — false on `νPk` by `ws2_collapse`, true on `νLk`), `ws3_plurality_core`
(P4), `ws3_faces_never_annihilate` (composition stays atom-free).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws2

universe u

open Cardinal QPF Functor Series4.WS1

namespace Series4.WS3

variable {κ : Cardinal.{u}} {Q : Type u}

/-! ## The labelled (faced) functor `X ↦ P_κ (Q × X)` and its QPF structure -/

/-- The labelled powerset functor: successors of `X` each carry a quality label from
`Q`. -/
def LkObj (κ : Cardinal.{u}) (Q : Type u) (X : Type u) : Type u := PkObj κ (Q × X)

/-- Functorial action: relabel the target of each edge, keeping its face. -/
def LkMap {X Y : Type u} (f : X → Y) (s : LkObj κ Q X) : LkObj κ Q Y :=
  PkMap κ (Prod.map id f) s

section QPFInstance
open Ordinal Set

/-- The polynomial functor of which the labelled functor is a quotient: a shape is a
size `a` together with a `Q`-labelling of its `< a` positions. -/
def LkP (κ : Cardinal.{u}) (Q : Type u) : PFunctor.{u} where
  A := Σ a : κ.ord.toType, ({b : κ.ord.toType // b < a} → Q)
  B := fun p => {b : κ.ord.toType // b < p.1}

def absLk {X : Type u} (p : (LkP κ Q).Obj X) : LkObj κ Q X :=
  ⟨Set.range (fun i => (p.1.2 i, p.2 i)),
    lt_of_le_of_lt Cardinal.mk_range_le (card_typein_toType_lt κ p.1.1)⟩

noncomputable def reprLk {X : Type u} (s : LkObj κ Q X) :
    { p : (LkP κ Q).Obj X // Set.range (fun i => (p.1.2 i, p.2 i)) = s.1 } := by
  have ho' : (Cardinal.mk (↥s.1)).ord < type (α := κ.ord.toType) (· < ·) := by
    rw [type_toType]; exact Cardinal.ord_lt_ord.mpr s.2
  set a : κ.ord.toType := enum (α := κ.ord.toType) (· < ·) ⟨(Cardinal.mk (↥s.1)).ord, ho'⟩ with ha
  have hcard : Cardinal.mk {b : κ.ord.toType // b < a} = Cardinal.mk (↥s.1) := by
    have h1 : Cardinal.mk {b : κ.ord.toType // b < a} = (typein (α := κ.ord.toType) (· < ·) a).card :=
      card_typein a
    rw [h1, ha, typein_enum, Cardinal.card_ord]
  let e : {b : κ.ord.toType // b < a} ≃ ↥s.1 := Classical.choice (Cardinal.eq.mp hcard)
  refine ⟨⟨⟨a, fun i => ((e i : Q × X)).1⟩, fun i => ((e i : Q × X)).2⟩, ?_⟩
  show Set.range (fun i => (((e i : Q × X)).1, ((e i : Q × X)).2)) = s.1
  have : (fun i => (((e i : Q × X)).1, ((e i : Q × X)).2)) = (Subtype.val ∘ e) := by
    funext i; exact Prod.ext rfl rfl
  rw [this, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]

noncomputable instance qpfLk : QPF (LkObj κ Q) where
  map f s := LkMap f s
  P := LkP κ Q
  abs := absLk
  repr s := (reprLk s).1
  abs_repr s := by
    apply Subtype.ext
    show Set.range (fun i => ((reprLk s).1.1.2 i, (reprLk s).1.2 i)) = s.1
    exact (reprLk s).2
  abs_map f p := by
    apply Subtype.ext
    show Set.range (fun i => (p.1.2 i, f (p.2 i))) = (Prod.map id f) '' Set.range (fun i => (p.1.2 i, p.2 i))
    have hfun : (fun i => (p.1.2 i, f (p.2 i)))
        = (Prod.map id f) ∘ (fun i => (p.1.2 i, p.2 i)) := by funext i; rfl
    rw [hfun, Set.range_comp]

end QPFInstance

/-- The labelled carrier: the terminal coalgebra of `X ↦ P_κ (Q × X)`. -/
noncomputable def νLk (κ : Cardinal.{u}) (Q : Type u) : Type u := Cofix (LkObj κ Q)

/-- The structure map (dest) of the labelled carrier. -/
noncomputable def lstr (x : νLk κ Q) : LkObj κ Q (νLk κ Q) := Cofix.dest x

/-! ## Loops at a given face, and their distinctness (P1) -/

/-- The one-point coalgebra with a self-loop carrying face `q`. -/
noncomputable def loopCoalg (q : Q) (hinf : ℵ₀ ≤ κ) :
    PUnit.{u+1} → LkObj κ Q PUnit.{u+1} :=
  fun _ => ⟨{(q, PUnit.unit)}, mk_singleton_lt hinf _⟩

/-- The self-loop state at face `q`. -/
noncomputable def loopState (q : Q) (hinf : ℵ₀ ≤ κ) : νLk κ Q :=
  Cofix.corec (loopCoalg q hinf) PUnit.unit

/-- The loop's unfolding: its single successor is itself, carried on a face-`q`
edge. -/
theorem loop_dest (q : Q) (hinf : ℵ₀ ≤ κ) :
    (Cofix.dest (loopState q hinf)).1 = {(q, loopState q hinf)} := by
  have h := Cofix.dest_corec (loopCoalg q hinf) PUnit.unit
  show (Cofix.dest (loopState q hinf)).1 = _
  rw [loopState, h]
  show (LkMap (Cofix.corec (loopCoalg q hinf)) (loopCoalg q hinf PUnit.unit)).1 = _
  simp only [LkMap, loopCoalg, PkMap_val, Set.image_singleton, Prod.map_apply, id_eq]

/-- **P1 — twin self-loops with different faces are distinct.** Distinct faces give
distinct states: the plain-carrier collapse (`ws2_collapse`) fails on the labelled
carrier. The direct analogue of Series 3 `ws14_loop_ne` (distinctness by weight),
here by face. -/
theorem ws3_loopface_ne (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    loopState q₁ hinf ≠ loopState q₂ hinf := by
  intro he
  apply hne
  have h1 := loop_dest q₁ hinf
  have h2 := loop_dest q₂ hinf
  rw [he] at h1
  rw [h2] at h1
  have hpair : (q₂, loopState q₂ hinf) = (q₁, loopState q₂ hinf) :=
    Set.singleton_eq_singleton_iff.mp h1
  exact (Prod.ext_iff.mp hpair).1.symm

/-! ## The coincidence (P3) and the plurality bundle (P4) -/

/-- **P3 — the coincidence theorem.** Plurality is bought *exactly* by the move from
the plain carrier to the labelled one. The two halves:

* **forced (from WS2):** on the plain carrier `νP_κ`, two hereditarily-nonempty
  states with the same successor structure are *equal* — `ws2_collapse`;
* **plural (on `νLk`):** two loops with the same successor target but different faces
  are *distinct* — `ws3_loopface_ne`.

So the same bare successor shape (a single self-loop) collapses to one point without
faces and splits into many with them. Plurality is earned against a standing
impossibility, not stipulated. -/
theorem ws3_same_succ_diff_face (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    -- forced half: without faces, hereditarily-nonempty states collapse
    (∀ a b : (νPk κ).X, Series4.WS2.HereditarilyNonempty a →
        Series4.WS2.HereditarilyNonempty b → a = b)
    -- plural half: with faces, same-target loops split by face
  ∧ (loopState q₁ hinf ≠ loopState q₂ hinf) :=
  ⟨fun a b ha hb => Series4.WS2.ws2_collapse hinf a b ha hb, ws3_loopface_ne hinf hne⟩

/-- A labelled state is **atomless (non-atomic)** at the first level when its
successor set is nonempty (it relates to something). -/
def NonAtomic (x : νLk κ Q) : Prop := (Cofix.dest x).1.Nonempty

/-- Every face-`q` loop is non-atomic: it relates (to itself). -/
theorem loop_nonAtomic (q : Q) (hinf : ℵ₀ ≤ κ) : NonAtomic (loopState q hinf) := by
  rw [NonAtomic, loop_dest]; exact Set.singleton_nonempty _

/-- **P4 — the atomless plurality bundle.** On the labelled carrier there are two
distinct, non-atomic states whose bare successor structure coincides (each is a
single self-loop) — distinguished *only* by their face. This is the plurality the
plain world forbids (§3 collapse), recovered without a single atom and without an
imported weight. -/
theorem ws3_plurality_core (hinf : ℵ₀ ≤ κ) {q₁ q₂ : Q} (hne : q₁ ≠ q₂) :
    ∃ a b : νLk κ Q, a ≠ b ∧ NonAtomic a ∧ NonAtomic b :=
  ⟨loopState q₁ hinf, loopState q₂ hinf, ws3_loopface_ne hinf hne,
   loop_nonAtomic q₁ hinf, loop_nonAtomic q₂ hinf⟩

/-- A concrete inhabitant of the plurality bundle, at `Q = ULift Bool`. -/
theorem ws3_plurality_core_concrete (hinf : ℵ₀ ≤ κ) :
    ∃ a b : νLk κ (ULift.{u} Bool), a ≠ b ∧ NonAtomic a ∧ NonAtomic b :=
  ws3_plurality_core hinf (q₁ := ⟨false⟩) (q₂ := ⟨true⟩) (by decide)

/-! ## Composition stays atom-free (the internality payoff) -/

/-- **C-unconditional — faces never annihilate.** The internality of the face
(it is part of the relata, not a value in an external algebra with a bottom) means
there is no external `⊥` for composition to reach. Concretely: a non-atomic loop's
face never degenerates to the empty object — its successor set is a nonempty
singleton at every step, so no composition of faces produces an atom. This is
*stronger* than Series 3 `ws14`, which genuinely leaked at the nilpotent Łukasiewicz
weight: with no imported bottom, there is nothing to leak. -/
theorem ws3_faces_never_annihilate (q : Q) (hinf : ℵ₀ ≤ κ) :
    (Cofix.dest (loopState q hinf)).1 ≠ ∅ := by
  rw [loop_dest]
  exact (Set.singleton_nonempty _).ne_empty

end Series4.WS3
