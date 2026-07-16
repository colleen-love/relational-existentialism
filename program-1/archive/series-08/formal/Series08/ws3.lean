/-
`series-08/formal/Series08/ws3.lean`

WS3 — **Re-restriction and forced dynamics.** Series 08, the engine of Part Two.

Genuinely new Lean (the carrier is transcribed via `Series08.ws1`; the re-restriction map, the
order, and forced dynamics are Series 08 content). Owns the re-restriction map, its two cheap
obligations **(NL)** no leaf and **(NF)** not-a-function, the forcing of dynamics, and the ONE
endogenous order `≺`. Conservation (CB) is NOT attempted here and is never folded into `ReReStep`
(that is WS5's, on this map).

Design doc: `series-08/spec/ws3-design.md`. DESIGN FIX (recorded in `charter-status.md`):
`ws3_imported_index_refuted` was designed with `h ≠ h'`, which cannot hold on `twoLoop` (its holds
are fixed points `(i,i)`, so re-restriction returns the SAME hold). The honest content — the order
CYCLES, so no strict monotone index represents it — is a self-loop step `ReReStep h h`. Faithful
correction of the signature (same intent: `≺` is not a disguised strict stage-index), not a retarget.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series08.ws1

universe u

namespace Series08.WS3

open Series08.WS1 Cardinal

variable {κ : Cardinal.{u}} {X : Type u}

/-! ## The re-restriction map and the endogenous order (README §2.4) -/

/-- **Re-restriction step**: `x↾(x,y)  ↝  y↾(y,z)`. Narrow from x's hold toward y to y's hold toward
    z (deeper). The new source is the old target. Touches no sibling set — conservation stays WS5's. -/
def ReReStep (dest : X → PkObj κ X) : Hold dest → Hold dest → Prop :=
  fun h h' => h'.1.1 = h.1.2 ∧ h'.1.2 ∈ (dest h'.1.1).1

/-- **The order**, derived once. `m ≺ m'` iff `m'` is reached by a re-restriction sequence from `m`:
    the reflexive-transitive closure of `ReReStep`, defined from `dest` alone — no external index. -/
def prec (dest : X → PkObj κ X) : Hold dest → Hold dest → Prop := Relation.ReflTransGen (ReReStep dest)

/-! ## The two cheap obligations — the seed (NL, NF) -/

/-- **(NL) no leaf.** From a hold whose target is atomless there is always a next re-restriction, and
    its source is again atomless: narrowing never empties a node. Honors the rejection of
    limit-atomlessness (§4.3). -/
theorem ws3_rerestriction_no_leaf (dest : X → PkObj κ X) (h : Hold dest)
    (hs : SHNE dest h.1.2) : ∃ h' : Hold dest, ReReStep dest h h' ∧ SHNE dest h'.1.1 := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hs.ne_empty
  exact ⟨⟨(h.1.2, z), hz⟩, ⟨rfl, hz⟩, hs⟩

/-- **(NF) not-a-function.** A hold at a two-successor node re-restricts to two DISTINCT holds: the
    narrowing is a free facing, not determined by the prior hold. -/
theorem ws3_rerestriction_not_function (dest : X → PkObj κ X) (h : Hold dest) {z z' : X}
    (hz : z ∈ (dest h.1.2).1) (hz' : z' ∈ (dest h.1.2).1) (hne : z ≠ z') :
    ∃ h₁ h₂ : Hold dest, ReReStep dest h h₁ ∧ ReReStep dest h h₂ ∧ h₁ ≠ h₂ := by
  refine ⟨⟨(h.1.2, z), hz⟩, ⟨(h.1.2, z'), hz'⟩, ⟨rfl, hz⟩, ⟨rfl, hz'⟩, ?_⟩
  intro he
  apply hne
  have hpair : ((h.1.2, z) : X × X) = (h.1.2, z') := congrArg Subtype.val he
  exact (Prod.mk.injEq _ _ _ _).mp hpair |>.2

/-! ## Forced dynamics and the order -/

/-- **Forced dynamics.** On an atomless field every hold has a further re-restriction with an atomless
    target, so `ReReStep` is serial — NO hold is terminal, the field must be unfolded over succession.
    Dynamics is forced by finitude-on-atomlessness, not added. -/
theorem ws3_dynamics_forced (dest : X → PkObj κ X) (h : Hold dest) (hs : SHNE dest h.1.2) :
    ∃ h' : Hold dest, ReReStep dest h h' ∧ SHNE dest h'.1.2 := by
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hs.ne_empty
  exact ⟨⟨(h.1.2, z), hz⟩, ⟨rfl, hz⟩, hs.succ hz⟩

/-- **The endogenous order projects onto `SReaches`.** Reaching is the trace of a narrowing
    sequence (charter §3): `≺` derived from re-restriction, its shadow on the carrier is reachability. -/
theorem ws3_prec_is_reach (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    SReaches dest h.1.1 h'.1.1 := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih => exact ih.tail (by rw [hstep.1]; exact b.2)

/-- **The imported-index branch refuted (§4.2 guard).** On the self-loop `≺` returns to the SAME
    hold via a genuine re-restriction step, so no strict monotone external index can represent it: the
    order is endogenous, not a disguised counter. (A strict index forbids `stage h < stage h`.) -/
theorem ws3_imported_index_refuted (hinf : ℵ₀ ≤ κ) :
    ∃ h : Hold (twoLoop hinf), ReReStep (twoLoop hinf) h h := by
  have hmem : (⟨true⟩ : ULift.{u} Bool) ∈ (twoLoop hinf ⟨true⟩).1 := by
    rw [twoLoop_val]; exact rfl
  exact ⟨⟨(⟨true⟩, ⟨true⟩), hmem⟩, rfl, hmem⟩

end Series08.WS3
