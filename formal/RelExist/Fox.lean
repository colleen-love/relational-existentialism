/-
# Fox's hallmark — the copy comonoid, and the two faces that share it (abstract layer)

The abstract, **mathlib-free** layer of "the seam is the non-comonoidal residue"
([spec: the seam is the non-comonoidal residue](../../docs/spec/00-doctrine.md)). It states the one
notion underneath *classical / copyable / cartesian* — carrying a **copy comonoid** — in the `Type`-level
style of [`Firewall`](Firewall.lean), so the concrete matrix model
([`Scratch/SeamComonoid.lean`](../Scratch/SeamComonoid.lean)) can be shown to instantiate it.

Fox's theorem: a symmetric monoidal category is cartesian **iff** every object carries a natural,
coherent commutative comonoid — a copy `Δ : A → A ⊗ A` and a delete `ε : A → I`, uniform in `A`. The
doctrine's §0.4 already names this hallmark (the natural `Δ`), and `Firewall.copy` already exhibits it.
What this module adds is the **keystone abstraction**: the cartesian self-model obstruction (Lawvere,
[`Mirror`](Mirror.lean)) and broadcastability (the no-cloning face) are stated over the **same**
`Comonoid.copy`. Lawvere *needs* the copy; broadcast *is* the copy; so the place the copy fails — the
seam — is at once non-self-modelable and non-broadcastable: **one missing comonoid, two faces.**

`[proved]` here: the comonoid structure, that the cartesian diagonal is one (Fox forward), that Lawvere's
diagonal *is* the copy, and the faces-share-copy keystone. `[reading]`: the full Fox biconditional in
general `Cl(𝕋)` (the reverse direction) is cited, not mechanized — it is not load-bearing for the
unification, which is concrete (§4).
-/
import RelExist.Firewall
import RelExist.Mirror
import RelExist.Relating

namespace RelExist.Fox

universe u v

/-- A (counital, coassociative, cocommutative) **copy comonoid** on `X`: a copy `Δ : X → X × X` and a
delete `ε : X → Unit`, with the comonoid laws (`Type`-level, over the cartesian tensor as in
`Firewall`). Carrying such a structure is Fox's single hallmark of *classical / copyable / cartesian*. -/
structure Comonoid (X : Type u) where
  copy : X → X × X
  delete : X → Unit
  /-- Counit (left): deleting the first copy returns the original. -/
  counit_left : ∀ x, (copy x).1 = x
  /-- Counit (right): deleting the second copy returns the original. -/
  counit_right : ∀ x, (copy x).2 = x
  /-- Coassociativity: copying-then-recopying agrees on both nestings (the flattened triple). -/
  coassoc : ∀ x,
    (((copy (copy x).1).1, (copy (copy x).1).2, (copy x).2) : X × X × X)
      = ((copy x).1, (copy (copy x).2).1, (copy (copy x).2).2)
  /-- Cocommutativity: the copy is symmetric. -/
  cocomm : ∀ x, Prod.swap (copy x) = copy x

/-- **Every type carries the natural copy** (Fox, forward direction: cartesian ⇒ comonoid). The
cartesian diagonal `Firewall.copy` — the very `(x, x)` that powers Lawvere — is a comonoid: counital,
coassociative, cocommutative, all by `rfl`. -/
def cartesian (X : Type u) : Comonoid X where
  copy := Firewall.copy
  delete := fun _ => ⟨⟩
  counit_left := fun _ => rfl
  counit_right := fun _ => rfl
  coassoc := fun _ => rfl
  cocomm := fun _ => rfl

/-- **The Lawvere diagonal IS the comonoid copy.** The escaping diagonal value `g a a` is `g` applied to
the copy `Δ a = (a, a)`. So the cartesian self-model obstruction runs *on* the copy comonoid — it is the
copy fed back in. -/
theorem lawvere_diagonal_is_copy {A : Type u} {B : Type v} (g : A → A → B) (a : A) :
    g a a = (fun p : A × A => g p.1 p.2) ((cartesian A).copy a) := rfl

/-- **The cartesian face uses the copy** (keystone, face 1). For any attempted self-model `g` and any
fixed-point-free `f`, the family that escapes every row of `g` is the copy `Δ` fed through `g` and then
`f` — this is `Mirror.selfModel_remainder` with the diagonal exhibited as `Comonoid.copy`. The self-model
remainder is therefore a consequence of the copy. -/
theorem cartesian_face_uses_copy {A : Type u} {B : Type v}
    (g : A → A → B) (f : B → B) (hf : ∀ b, f b ≠ b) :
    ¬ ∃ a, g a = fun a' => f ((fun p : A × A => g p.1 p.2) ((cartesian A).copy a')) :=
  Mirror.selfModel_remainder g f hf

/-- **Broadcastability is carrying the copy** (face 2). A space is broadcastable exactly when it carries
the copy comonoid; every `Type` does (`broadcastable_cartesian`). The *failure* of broadcast — the
no-cloning face — is therefore exactly the *absence* of the comonoid, which is what the concrete seam
exhibits (`SeamComonoid.seam_is_noncomonoidal_residue`). -/
def Broadcastable (X : Type u) : Prop := Nonempty (Comonoid X)

theorem broadcastable_cartesian (X : Type u) : Broadcastable X := ⟨cartesian X⟩

/-- **The two faces share one object** (the keystone). Both the cartesian self-model remainder
(`cartesian_face_uses_copy`) and broadcastability (`Broadcastable`) are stated over the *same*
`Comonoid.copy`: Lawvere needs the copy, broadcast *is* the copy. So wherever the copy fails — the seam —
the space is at once non-self-modelable (cartesian face, via `Mirror`) and non-broadcastable (monoidal
face): **one missing comonoid, two faces.** The concrete witness that the copy genuinely fails, and
cannot be restored by any available knowing, is `SeamComonoid.seam_is_noncomonoidal_residue`. -/
theorem faces_share_copy {A : Type u} {B : Type v} (f : B → B) (hf : ∀ b, f b ≠ b) :
    (∀ g : A → A → B,
        ¬ ∃ a, g a = fun a' => f ((fun p : A × A => g p.1 p.2) ((cartesian A).copy a')))
      ∧ Broadcastable A :=
  ⟨fun g => cartesian_face_uses_copy g f hf, broadcastable_cartesian A⟩

end RelExist.Fox
