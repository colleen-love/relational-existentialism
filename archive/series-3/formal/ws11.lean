/-
`series-3/formal/ws11.lean`

WS11 (`series-3/spec/ws11/02-design.md`): **the identity split** — where does
state identity live? On the terminal carrier, Lambek makes `str` a bijection, so
the *downward* data (the unfolding) already determines identity. This workstream
decides, at full generality, whether the *upward* data (the in-neighbourhood
`UpView`) can ever be load-bearing:

* **negative direction, schema-level (K2/K4).** Strong extensionality forces
  downward determination: on *any* coalgebra of `P_κ`, equality-of-unfoldings is a
  bisimulation, so a strongly extensional coalgebra cannot have upward-load-bearing
  identity (`ws11_no_upward_identity`). No terminality needed — the bisimulation
  argument is the whole content.
* **positive direction, by witness (K5).** Outside the strongly extensional class
  the property is coherent: an explicit three-state coalgebra has non-injective
  `str` that the joint (down + up) data separates (`ws11_upward_witness`).
* **the mechanism (K6).** The unique map into the terminal carrier identifies
  exactly the pair only upward data separated (`ws11_terminal_identifies`,
  `ws11_witness_collapsed`): the terminal quotient erases upward distinctions.

Bundle `ws11_identity_split`. Both admissible outcomes are in the deliverable by
construction (impossibility proved at schema level, possibility proved by witness),
so nothing in this workstream can force a reframe.

Built on `ws1`/`ws2` (imported as established, axiom-free): `Coalg`, `PkObj`,
`PkMap(_id/_comp)`, `Bisim`, `lambek`, `IsTerminalCoalg`, `mk_empty_lt`,
`mk_singleton_lt`, `νPk`, `νPk_terminal`. Everything here rests only on Mathlib's
standard `propext`/`Classical.choice`/`Quot.sound` — no custom axioms, `sorry`-free.
-/
import ws2

universe u

open Cardinal Series3.WS1 Series3.WS2

namespace Series3.WS11

variable {κ : Cardinal.{u}}

/-! ## Block 1 — the identity-locus vocabulary -/

/-- Downward data determines identity: `str` alone is injective. -/
def DownwardDetermined (C : Coalg κ) : Prop :=
  ∀ x y : C.X, C.str x = C.str y → x = y

/-- The upward data of a state: the set of states whose unfolding contains it
(its in-neighbourhood). -/
def UpView (C : Coalg κ) (x : C.X) : Set C.X := {z | x ∈ (C.str z).1}

/-- `C` is strongly extensional: every bisimulation is contained in the diagonal. -/
def StronglyExtensional (C : Coalg κ) : Prop :=
  ∀ R : C.X → C.X → Prop, Bisim C R → ∀ x y, R x y → x = y

/-- Downward + upward data jointly determine identity. -/
def JointlyDetermined (C : Coalg κ) : Prop :=
  ∀ x y : C.X, C.str x = C.str y → UpView C x = UpView C y → x = y

/-- Upward data is *load-bearing*: `str` alone fails to separate states, but the
joint data succeeds — identity genuinely depends on the in-neighbourhood. -/
def UpwardLoadBearing (C : Coalg κ) : Prop :=
  (¬ DownwardDetermined C) ∧ JointlyDetermined C

/-- `f : C.X → (νPk κ).X` is a coalgebra morphism into the terminal carrier. -/
def IsCoalgHom (C : Coalg κ) (f : C.X → (νPk κ).X) : Prop :=
  ∀ z, (νPk κ).str (f z) = PkMap κ f (C.str z)

/-! ## Block 2 — the schema (K2, K4, and corollaries K1, K3)

Equality of unfoldings is a bisimulation on *any* coalgebra: push the shared
successor set along the diagonal. Both projection laws hold because the diagonal
copy recovers the same successor set on either projection (the second up to the
`str`-equality that defines the related pair). This is the plain-carrier `diagBisim`
of ws2, generalized from `a = b` to `str a = str b`. -/

/-- Equality-of-unfoldings is a bisimulation on any `P_κ`-coalgebra. -/
def strEqBisim (C : Coalg κ) : Bisim C (fun a b => C.str a = C.str b) where
  ζ := fun p =>
    PkMap κ (fun v => (⟨(v, v), rfl⟩ : {q : C.X × C.X // C.str q.1 = C.str q.2}))
      (C.str p.1.1)
  nat_fst := fun p => by
    have h : PkMap κ (fun q : {q : C.X × C.X // C.str q.1 = C.str q.2} => q.1.1)
        (PkMap κ (fun v => (⟨(v, v), rfl⟩ : {q : C.X × C.X // C.str q.1 = C.str q.2}))
          (C.str p.1.1)) = C.str p.1.1 := by
      rw [← PkMap_comp]; exact PkMap_id _
    exact h.symm
  nat_snd := fun p => by
    have hp : C.str p.1.1 = C.str p.1.2 := p.2
    have h : PkMap κ (fun q : {q : C.X × C.X // C.str q.1 = C.str q.2} => q.1.2)
        (PkMap κ (fun v => (⟨(v, v), rfl⟩ : {q : C.X × C.X // C.str q.1 = C.str q.2}))
          (C.str p.1.1)) = C.str p.1.1 := by
      rw [← PkMap_comp]; exact PkMap_id _
    rw [← hp]; exact h.symm

/-- **K2.** Strong extensionality forces downward determination — on *any*
coalgebra of `P_κ`, not only the terminal one. -/
theorem ws11_extensional_downward (C : Coalg κ)
    (hext : StronglyExtensional C) : DownwardDetermined C :=
  fun x y h => hext _ (strEqBisim C) x y h

/-- **K4 (the impossibility).** Strong extensionality and load-bearing upward
identity are jointly unsatisfiable. -/
theorem ws11_no_upward_identity (C : Coalg κ)
    (hext : StronglyExtensional C) : ¬ UpwardLoadBearing C :=
  fun h => h.1 (ws11_extensional_downward C hext)

/-- **K1 (anchor corollary).** On the terminal carrier, downward data determines
identity outright (Lambek: `str` is injective). -/
theorem ws11_downward_determined :
    DownwardDetermined (νPk κ) :=
  fun _ _ h => (lambek (νPk_terminal κ)).injective h

/-- **K3 (redundancy corollary).** In a strongly extensional coalgebra the joint
hypothesis is redundant: downward data alone already determines identity. -/
theorem ws11_upward_redundant (C : Coalg κ)
    (hext : StronglyExtensional C) : JointlyDetermined C :=
  fun x y h _ => ws11_extensional_downward C hext x y h

/-! ## Block 3 — the witness (K5)

The three-state coalgebra `a, b, p` on `ULift (Fin 3)`:
`str a = ∅`, `str b = ∅`, `str p = {a}`. Then `str a = str b` with `a ≠ b`
(downward fails), while `UpView a = {p} ≠ ∅ = UpView b` separates the one bad pair
and `str` separates everything else — so the joint data determines identity. -/

/-- The three-state witness coalgebra. States `⟨0⟩ = a`, `⟨1⟩ = b`, `⟨2⟩ = p`. -/
def upCoalg (hinf : ℵ₀ ≤ κ) : Coalg κ where
  X := ULift (Fin 3)
  str := fun i =>
    if i.down = 2 then ⟨{(⟨0⟩ : ULift (Fin 3))}, mk_singleton_lt hinf _⟩
    else ⟨∅, mk_empty_lt hinf⟩

@[simp] lemma upCoalg_str_lt (hinf : ℵ₀ ≤ κ) (i : ULift (Fin 3)) (hi : i.down ≠ 2) :
    ((upCoalg hinf).str i).1 = (∅ : Set (ULift (Fin 3))) := by
  simp [upCoalg, hi]

@[simp] lemma upCoalg_str_p (hinf : ℵ₀ ≤ κ) :
    ((upCoalg hinf).str ⟨2⟩).1 = {(⟨0⟩ : ULift (Fin 3))} := by
  simp [upCoalg]

/-- `str a = str b` (both `∅`) — the downward collision at the heart of the witness. -/
lemma upCoalg_str_ab (hinf : ℵ₀ ≤ κ) :
    (upCoalg hinf).str (⟨0⟩ : ULift (Fin 3)) = (upCoalg hinf).str (⟨1⟩ : ULift (Fin 3)) := by
  apply Subtype.ext
  rw [upCoalg_str_lt hinf _ (by decide), upCoalg_str_lt hinf _ (by decide)]

/-- `str` separates `a` from `p` (`∅ ≠ {a}`). -/
lemma upCoalg_str_ap_ne (hinf : ℵ₀ ≤ κ) :
    (upCoalg hinf).str (⟨0⟩ : ULift (Fin 3)) ≠ (upCoalg hinf).str ⟨2⟩ := by
  intro h
  have hm : (⟨0⟩ : ULift (Fin 3)) ∈ ((upCoalg hinf).str ⟨0⟩).1 := by rw [h]; simp [upCoalg]
  simp [upCoalg] at hm

/-- `str` separates `b` from `p` (`∅ ≠ {a}`). -/
lemma upCoalg_str_bp_ne (hinf : ℵ₀ ≤ κ) :
    (upCoalg hinf).str (⟨1⟩ : ULift (Fin 3)) ≠ (upCoalg hinf).str ⟨2⟩ := by
  intro h
  have hm : (⟨0⟩ : ULift (Fin 3)) ∈ ((upCoalg hinf).str ⟨1⟩).1 := by rw [h]; simp [upCoalg]
  simp [upCoalg] at hm

/-- `UpView` separates `a` from `b`: `p` is in the in-neighbourhood of `a` but not
of `b`. This is the pair only upward data can tell apart. -/
lemma upCoalg_up_ab_ne (hinf : ℵ₀ ≤ κ) :
    UpView (upCoalg hinf) (⟨0⟩ : ULift (Fin 3)) ≠ UpView (upCoalg hinf) ⟨1⟩ := by
  intro h
  have hmem : (⟨2⟩ : ULift (Fin 3)) ∈ UpView (upCoalg hinf) (⟨0⟩ : ULift (Fin 3)) ↔
      (⟨2⟩ : ULift (Fin 3)) ∈ UpView (upCoalg hinf) ⟨1⟩ := by rw [h]
  simp [UpView, upCoalg] at hmem

/-- **K5 (the positive witness).** Upward-load-bearing identity is coherent: it is
realized by an explicit finite coalgebra (necessarily outside the strongly
extensional class, by K4). -/
theorem ws11_upward_witness (hinf : ℵ₀ ≤ κ) :
    ∃ C : Coalg κ, UpwardLoadBearing C := by
  refine ⟨upCoalg hinf, ?_, ?_⟩
  · -- downward determination fails: `a ≠ b` but `str a = str b`.
    intro hdd
    have h01 : (⟨0⟩ : ULift (Fin 3)) = ⟨1⟩ := hdd _ _ (upCoalg_str_ab hinf)
    exact absurd h01 (by decide)
  · -- joint determination holds: case-bash the three states.
    intro x y hstr hup
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    fin_cases x
    · fin_cases y
      · rfl
      · exact absurd hup (upCoalg_up_ab_ne hinf)
      · exact absurd hstr (upCoalg_str_ap_ne hinf)
    · fin_cases y
      · exact absurd hup (fun h => upCoalg_up_ab_ne hinf h.symm)
      · rfl
      · exact absurd hstr (upCoalg_str_bp_ne hinf)
    · fin_cases y
      · exact absurd hstr (fun h => upCoalg_str_ap_ne hinf h.symm)
      · exact absurd hstr (fun h => upCoalg_str_bp_ne hinf h.symm)
      · rfl

/-! ## Block 4 — the mechanism (K6) -/

/-- **K6 (the mechanism).** Any coalgebra morphism into the terminal carrier
identifies states with equal unfoldings — naturality plus Lambek injectivity. -/
theorem ws11_terminal_identifies (C : Coalg κ) {x y : C.X}
    (h : C.str x = C.str y) (f : C.X → (νPk κ).X) (hf : IsCoalgHom C f) :
    f x = f y :=
  (lambek (νPk_terminal κ)).injective (by rw [hf x, hf y, h])

/-- **K6 applied to the witness.** The (unique) map into the terminal carrier
identifies exactly the pair `a, b` that only upward data separated: the terminal
quotient erases the upward distinction. -/
theorem ws11_witness_collapsed (hinf : ℵ₀ ≤ κ) :
    ∀ f : (upCoalg hinf).X → (νPk κ).X, IsCoalgHom (upCoalg hinf) f →
      f (⟨0⟩ : ULift (Fin 3)) = f ⟨1⟩ :=
  fun f hf => ws11_terminal_identifies (upCoalg hinf) (upCoalg_str_ab hinf) f hf

/-! ## Block 5 — the bundle -/

/-- The WS11 identity split: upward-load-bearing identity is *impossible* inside
the strongly extensional class and *realized* outside it. Named for the split it
proves, not `ws11_resolved`. -/
structure WS11IdentitySplit (κ : Cardinal.{u}) where
  no_upward_on_extensional :
    ∀ C : Coalg κ, StronglyExtensional C → ¬ UpwardLoadBearing C
  upward_witness : ℵ₀ ≤ κ → ∃ C : Coalg κ, UpwardLoadBearing C

/-- **The WS11 deliverable.** -/
theorem ws11_identity_split (κ : Cardinal.{u}) : WS11IdentitySplit κ where
  no_upward_on_extensional := fun C hext => ws11_no_upward_identity C hext
  upward_witness := fun hinf => ws11_upward_witness hinf

end Series3.WS11
