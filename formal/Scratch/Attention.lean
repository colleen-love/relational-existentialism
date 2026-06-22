/-
# Attention as co-directed eigenstructure — not a bolted-on budget

This module replaces the *external resource* model of attention (a private scalar
budget `β` a self spends down — see `RelExist/Loop.lean`) with one where attention is
a **consequence of the relational structure itself**.

The reframing, in one breath: a relation *co-directs* the attention of both relaters;
your sustained standing is a function of the standing of those who relate to you
("receiving raises giving"); this is a monotone, positively-fed-back operator on the
field of relata; a **self is an eigenform** of it — a fixed point of co-directed
attention-feedback; and finiteness is *constitutive* (the bounded lattice `α` is a
perspective's integration capacity), not an allowance imposed from outside. There is
**no budget parameter anywhere in this file** — attention is determined entirely by
the coupling `c` and the capacity `α`.

Formally we reuse Knaster–Tarski (`OrderHom.gfp`), the same `ν`-modality as `≈` in
`Scratch/We.lean`: the sustained self is the *greatest* co-sustainable attention field.

* `couplingOp`        — the co-directed (and possibly asymmetric) attention operator
                        induced by a coupling `c`. `couplingOp_mono` is "receiving
                        raises giving".
* `sustainedField`    — `νΦ`: the self as an eigenform of co-directed attention.
* `sustainedField_fixed` / `_greatest` — it is a fixed point, and the maximal one.
* `orbit_ascending` / `orbit_le_gfp` — **generativity**: from a self-reinforcing seed,
  iterated relating *accumulates* attention (never depletes it), bounded above by the
  self. This is the formal "receiving more increases what you can give".

See `docs/spec/01-signature.md §1.3` for the prose, and
`docs/spec/03-sparsity-conjecture.md` for why sparsity becomes a spectral/closure
phenomenon here rather than a budget cap.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Logic.Function.Iterate

namespace RelExist.Attention

variable {V : Type*} {α : Type*} [CompleteLattice α]

/-- An **attention field**: each relatum's standing in the (constitutively bounded)
capacity `α`. Finiteness lives in `α` having a `⊤` — a perspective integrates a bounded
total — not in any external budget. The function space `V → α` is itself a complete
lattice, which is all the fixed-point machinery needs. -/
abbrev Field (V : Type*) (α : Type*) := V → α

/-- **The co-directed attention operator** induced by a coupling `c` (read `c i j` as
"`i` relates to `j`"; it need not be symmetric, so co-direction is asymmetric). Your
sustained standing is the supremum of the standing of those you relate to:

    couplingOp c att i = ⨆ j, ⨆ (_ : c i j), att j.

Attention is thus *induced by the relation*, with no budget; the coupling `c` — the
totality of who-relates-to-whom — is what shapes it. -/
def couplingOp (c : V → V → Prop) : Field V α →o Field V α where
  toFun att i := ⨆ j, ⨆ _ : c i j, att j
  monotone' := by
    intro a b hab i
    exact iSup_mono fun j => iSup_mono fun _ => hab j

@[simp] theorem couplingOp_apply (c : V → V → Prop) (att : Field V α) (i : V) :
    couplingOp c att i = ⨆ j, ⨆ _ : c i j, att j := rfl

/-- **Receiving raises giving.** More standing among those you relate to yields at least
as much sustained standing — the operator is monotone. This positive feedback (not a
depleting budget) is what shapes attention. -/
theorem couplingOp_mono (c : V → V → Prop) {a b : Field V α} (h : a ≤ b) :
    couplingOp c a ≤ couplingOp c b :=
  (couplingOp c).monotone h

/-- **The sustained self `νΦ`**: the greatest co-sustainable attention field under the
coupling — an *eigenform* of co-directed attention (a fixed point), determined by the
relational structure alone. -/
def sustainedField (c : V → V → Prop) : Field V α := (couplingOp (α := α) c).gfp

/-- The sustained self is a **fixed point** of co-directed attention: `Φ ≈ = ≈`. -/
theorem sustainedField_fixed (c : V → V → Prop) :
    couplingOp c (sustainedField (α := α) c) = sustainedField c := by
  unfold sustainedField
  exact (couplingOp (α := α) c).map_gfp

/-- **Maximality / coinduction.** Any self-upholding field (`a ≤ Φ a` — every relatum's
standing is justified by those relating to it) lies within the sustained self. To show a
standing is sustained, exhibit a self-upholding field carrying it. -/
theorem sustainedField_greatest (c : V → V → Prop) {a : Field V α}
    (h : a ≤ couplingOp c a) : a ≤ sustainedField c := by
  unfold sustainedField
  exact (couplingOp (α := α) c).le_gfp h

/-- Finiteness is **constitutive**: the sustained self never exceeds capacity `⊤`. No
external budget enforces this — it is `α`'s boundedness, the perspective's own limit. -/
theorem sustainedField_le_top (c : V → V → Prop) : sustainedField (α := α) c ≤ ⊤ :=
  le_top

/-! ### Generativity — relating accumulates attention, bounded by the self

For any monotone attention operator `Φ`, a **self-reinforcing seed** (`a ≤ Φ a`) only
grows under iterated relating, and stays within the maximal self `νΦ`. This is the
formal content of "receiving more attention increases the attention you can give": the
loop is *generative*, not a budget drawn down. -/

section Generative
variable (Φ : Field V α →o Field V α)

/-- From a self-reinforcing seed, the orbit of iterated relating is **non-decreasing**:
each round of being-related-to adds, never subtracts. -/
theorem orbit_ascending {a : Field V α} (h : a ≤ Φ a) (n : ℕ) :
    (Φ^[n]) a ≤ (Φ^[n + 1]) a := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Φ.monotone ih

/-- The accumulating orbit stays **bounded above by the self** `νΦ`: attention grows
toward, and never past, the maximal co-sustainable standing. -/
theorem orbit_le_gfp {a : Field V α} (h : a ≤ Φ a) (n : ℕ) :
    (Φ^[n]) a ≤ Φ.gfp := by
  induction n with
  | zero => simpa using Φ.le_gfp h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc Φ ((Φ^[n]) a) ≤ Φ Φ.gfp := Φ.monotone ih
      _ = Φ.gfp := Φ.map_gfp

end Generative

end RelExist.Attention
