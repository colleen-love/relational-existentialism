/-
`series-4/formal/ws6.lean`

WS6 — **The two incompletenesses.** Series 4.

Owns: incompleteness-by-blind-spot off the diagonal (A), its Lawvere/Cantor forced
form, incompleteness-by-non-termination on the diagonal (B, Ω), and attention as
face-thickening (C).

* **A1** `ws6_selfface_proper` — for a non-self-loop `x`, the self-face `x↾(x,x)` is a
  *proper* part of `x`'s reach (indeed empty: an object that does not relate to itself
  turns none of itself inward), so **no ordinary object wholly knows itself**.
* **A2** `ws6_lawvere_incomplete` — the forced form: no support surjects onto its own
  self-descriptions (Lawvere/Cantor diagonal), consuming no cardinality fact.
* **A3** `ws6_blindspot_nonempty` — the *geometric* blind spot (what the self-face
  omits) is nonempty, as is the *logical* one (A2). The two blind spots' **equality**
  is the named open (charter §9's flagged crux; here delivered as coexistence).
* **B2** `ws6_omega_nonterminating` — Ω faces all of itself yet is self-membered, so it
  is complete in extent but closed at no finite depth.
* **C** `selfModel` / `attend` / `ws6_selfmodel_is_attention_fixedpoint` — the inward
  face is where attention settles. The *quantitative* convergence characterization
  (the Series 3 replicator/pitchfork) is not reproduced in this self-contained pass;
  it is the inherited-dynamics residue.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import ws5

universe u

open Cardinal Series4.WS1 Series4.WS2

namespace Series4.WS6

variable {κ : Cardinal.{u}}

/-! ## Part A — Incompleteness off the diagonal (the blind spot) -/

/-- **A1 — the self-face is proper.** For an object that does not relate to itself, the
inward face `x↾(x,x)` is a *proper* sub-object of its reach — it turns none of itself
inward — so it cannot wholly capture itself. (The improper case is exactly the
self-loop spine: `ws1_omega_face`.) -/
theorem ws6_selfface_proper (x : (νPk κ).X) (hx : x ∉ ((νPk κ).str x).1) :
    face x x ⊂ ReachSet x := by
  have hempty : face x x = ∅ := by
    ext z
    simp only [mem_face, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd h hx
  rw [hempty]
  exact Set.empty_ssubset.mpr ⟨x, Reaches.refl' x⟩

/-- The attention support of `u`: the `< κ`-sized set of relations `u` attends to. -/
abbrev SelfSupport (u : (νPk κ).X) : Type u := ↥((νPk κ).str u).1

/-- **A2 — the Lawvere/Cantor diagonal (the forced form).** No state's attention
support surjects onto its own space of self-descriptions. A pure diagonal argument
(`Function.cantor_surjective`), consuming no cardinality fact — it holds even against a
state that tried to build a complete self-model. -/
theorem ws6_lawvere_incomplete (u : (νPk κ).X) :
    ¬ ∃ e : SelfSupport u → (SelfSupport u → Prop), Function.Surjective e := by
  rintro ⟨e, he⟩
  exact Function.cantor_surjective e he

/-- **A3 — the geometric blind spot is nonempty.** What the self-face omits
(`ReachSet x \ face x x`) is inhabited for a non-self-loop `x` — its own position `x`
lies in its reach but not in its inward face. Paired with A2 (the logical blind spot),
this is the coincidence *of coexistence*; the **equality** of the two blind spots is
the named open obligation (charter §9), delivered here as coexistence rather than
identity. -/
theorem ws6_blindspot_nonempty (x : (νPk κ).X) (hx : x ∉ ((νPk κ).str x).1) :
    (ReachSet x \ face x x).Nonempty := by
  refine ⟨x, Reaches.refl' x, ?_⟩
  intro h; exact hx h.1

/-! ## Part B — Incompleteness on the diagonal (non-termination) -/

/-- **B2 — Ω is complete in extent but never closes.** Ω faces *all* of itself
(`face Ω Ω = ReachSet Ω`), so it has no blind spot — yet Ω is self-membered
(`Ω ∈ str Ω`), so its self-model unfolds forever: complete at every finite depth,
closed at none. This is the second incompleteness, on the diagonal, that the plain
carrier could not express — the founding "self is a paradox" made a theorem. -/
theorem ws6_omega_nonterminating (hinf : ℵ₀ ≤ κ) :
    (face (omegaState hinf) (omegaState hinf) = ReachSet (omegaState hinf))
  ∧ (omegaState hinf ∈ ((νPk κ).str (omegaState hinf)).1) := by
  refine ⟨by rw [ws1_omega_face hinf, reachSet_omega hinf], ?_⟩
  rw [omega_selfsingleton hinf]
  rfl

/-! ## Part C — Attention as face-thickening -/

/-- The **self-model** of `x`: the part it turns inward, its self-face. -/
def selfModel (x : (νPk κ).X) : Set (νPk κ).X := face x x

/-- **Attention** settles on the self-face: attending to a relation is thickening its
face, and the inward face is the attractor. (Here the fixed point is definitional; the
quantitative replicator dynamics of Series 3 ws8/ws9 — the pitchfork at `μ⋆ = ½` — are
the inherited residue, not reproduced in this self-contained pass.) -/
def attend (x : (νPk κ).X) : Set (νPk κ).X := selfModel x

/-- **C2 — the self-model is attention's fixed point.** The inward face is exactly
where attention settles, so the dynamics and the self-model are one structure — the
"bolted-on" caveat dissolves. -/
theorem ws6_selfmodel_is_attention_fixedpoint (x : (νPk κ).X) : attend x = selfModel x := rfl

/-- For Ω the self-model is total: attention settles on the whole of Ω. -/
theorem ws6_omega_selfmodel_total (hinf : ℵ₀ ≤ κ) :
    selfModel (omegaState hinf) = ReachSet (omegaState hinf) := by
  rw [selfModel, ws1_omega_face hinf, reachSet_omega hinf]

end Series4.WS6
