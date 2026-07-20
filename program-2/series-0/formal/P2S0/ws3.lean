/-
`program-2/series-0/formal/P2S0/ws3.lean`

WS3 - The asymmetry of knowing (THE KNOT). Program 2 Series 0 (2.0), the genuinely-uncertain obligation.

Knowing's directionality is seated as the plain/labelled split: the KNOWING-LABELLED LIFT `knowLiftD` tags
each symmetric neighbor with the knowing bit (does the source actively attend the target), and its plain
(label-forgetting) reduct is the symmetric relating. On the two-state PASSIVE witness (`a` attends `b`, `b`
attends nothing) the three payoffs are proved: direction is NOT recoverable from the symmetric relating
(`ws3_direction_not_recoverable`, the plain bisimulation relating `a`,`b` is not a label-bisimulation, since
`a` knows `b` while `b` does not know `a`); passive constitution is real and LOAD-BEARING
(`ws3_passive_constitution`, `b` attended-but-not-attending is plain-bisimilar to the active `a` yet
label-separated, `attends`/`attendedBy` load-bearing in the statement, `AttentionDistinguishes` imported from
`P1.Reader`); active and passive are genuinely two (`ws3_active_passive_distinct`). The razor (charter §4.a):
the asymmetry must be a genuine structural distinction read by `IsBisimL`, NOT an inert tag on the symmetric
relating (the Series 11 Bookkeeping failure). The witness carrier is the monomorphic `Bool` at `Cardinal.{0}`
(a nullary universe-polymorphic witness would take a fresh universe per occurrence; disclosed).

Design docs: `program-2/series-0/spec/ws3-design.md`; shared objects `spec/README.md` §2.3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S0.ws1

universe u

namespace P2S0

open P1.Core P1.Reader Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-! ## The passive witness (`a` attends `b`; `b` attends nothing) -/

/-- The active relatum. -/
def a : Bool := true
/-- The passively-constituted relatum: attended by `a`, attends nothing. -/
def b : Bool := false

/-- The witness attention: `a` attends `b`; `b` attends nothing. -/
def attendsD : Bool → Finset Bool := fun x => if x = a then {b} else ∅

/-- **The knowing-labelled lift on the witness.** At `a`, the symmetric neighbor `b` tagged with the knowing
bit `true` (`a` knows `b`); at `b`, the symmetric neighbor `a` tagged with `false` (`b` does not know `a`).
The plain reduct is the symmetric relating `a — b`. -/
noncomputable def knowLiftD (hinf : ℵ₀ ≤ κ) : Bool → LkObj κ Bool Bool :=
  fun x => if x = a then pkSingle hinf ((true : Bool), b) else pkSingle hinf ((false : Bool), a)

lemma knowLiftD_a (hinf : ℵ₀ ≤ κ) : (knowLiftD hinf a).1 = {((true : Bool), b)} := rfl
lemma knowLiftD_b (hinf : ℵ₀ ≤ κ) : (knowLiftD hinf b).1 = {((false : Bool), a)} := rfl

/-- Every state's plain successor set is a nonempty singleton (so both states are `SHNE`). -/
lemma plainOf_knowLiftD_ne_empty (hinf : ℵ₀ ≤ κ) (v : Bool) :
    (plainOf (knowLiftD hinf) v).1 ≠ ∅ := by
  have h1 : ((knowLiftD hinf v).1).Nonempty := by
    unfold knowLiftD
    split <;> · rw [pkSingle_val]; exact Set.singleton_nonempty _
  simp only [plainOf, PkMap_val]
  exact (h1.image Prod.snd).ne_empty

lemma ws3_SHNE (hinf : ℵ₀ ≤ κ) (x : Bool) : SHNE (plainOf (knowLiftD hinf)) x :=
  fun v _ => plainOf_knowLiftD_ne_empty hinf v

/-- **The label separates `a` and `b`.** No label-bisimulation relates them: `a`'s outgoing edge carries the
knowing bit `true`, `b`'s only edge carries `false`. Mirrors `P1.Core.ws4_label_survives_quotient`. -/
lemma ws3_label_sep (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (knowLiftD hinf) R ∧ R a b := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR a b hRel
  obtain ⟨q, hq, hfst, _⟩ :=
    hfwd ((true : Bool), b) (by rw [knowLiftD_a]; exact Set.mem_singleton _)
  rw [knowLiftD_b, Set.mem_singleton_iff] at hq
  subst hq
  exact absurd hfst (by decide)

/-! ## The three payoffs -/

/-- **DIRECTION IS NON-RECOVERABLE (audit (c)).** The knowing direction is NOT recoverable from the symmetric
relating: the plain bisimulation relating `a`,`b` (both atomless, `ws1_atomless_bisim`) is not a
label-bisimulation. A discharged obligation, not an assumption. -/
theorem ws3_direction_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (knowLiftD hinf) := by
  intro hrec
  obtain ⟨R, hR, hab⟩ :=
    ws1_atomless_bisim (plainOf (knowLiftD hinf)) a b (ws3_SHNE hinf a) (ws3_SHNE hinf b)
  exact ws3_label_sep hinf ⟨R, hrec R hR, hab⟩

/-- **PASSIVE CONSTITUTION IS REAL AND LOAD-BEARING (audit (b), Charter Extension 1 R3, an IMPLICATION not a
bare conjunction).** Stated over the unified witness (`ws1.lean`): IF a relatum `o` reifies the self-relation
(`reifyU {s0} = o`) and attends the self (`s0 ∈ attendsU o`), THEN `o` is plain-bisimilar to the self `s0` over
the bare relating yet NOT recoverable from it (tower-separated). The passive/reification premises DRIVE the
separation: `hreify` places `o` strictly above the self in the tower (that is what separates them), and
`hattend` is the incoming edge the separation is read on. The self is passively constituted by the first
other's attention, and that constitution is non-recoverable from the bare relating. Not a conjunction of an
inert passivity fact with the separation: the passivity is what produces the separation. -/
theorem ws3_passive_constitution (hinf : ℵ₀ ≤ κ)
    (o : Fin 3) (hreify : reifyU {s0} = o) (hattend : s0 ∈ attendsU o) :
    AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) o s0 := by
  -- the reification places o strictly above the self in the tower (this is what separates them)
  have hrank : rankU s0 < rankU o := by rw [← hreify]; decide
  refine ⟨?_, ?_⟩
  · rw [plainOf_rankLift]
    exact ws1_atomless_bisim (outDest hinf attendsU) o s0 (SHNE_U hinf o) (SHNE_U hinf s0)
  · rintro ⟨R, hR, hRel⟩
    obtain ⟨hfwd, _⟩ := hR o s0 hRel
    have hedge : ((⟨rankU o⟩ : ULift.{0} ℕ), s0)
        ∈ (rankLift (outDest hinf attendsU) rankU o).1 := by
      rw [rankLiftU_val]; exact ⟨s0, Finset.mem_coe.mpr hattend, rfl⟩
    obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
    rw [rankLiftU_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have heq : rankU o = rankU s0 := congrArg ULift.down hfst
    omega

/-- **ACTIVE AND PASSIVE ARE TWO (Charter Extension 1 R3).** On the unified witness: the first other `s1` is
ACTIVELY constituted, made by reifying the self-relation it attends (`s1 = reifyU {s0}`, `s0 ∈ attendsU s1`);
the self `s0` is PASSIVELY constituted, attended by the first other (`s1 ∈ attendedBy attendsU s0`) while not
attending it back (`s1 ∉ attendsU s0`). The two occupy the same bare-relating position yet the directed
reification structure tells them apart, and the separation is DERIVED from `ws3_passive_constitution` (the
passive/reification structure), not conjoined beside it. The reaching and the being-reached are two becomings. -/
theorem ws3_active_passive_distinct (hinf : ℵ₀ ≤ κ) :
    (s1 = reifyU {s0} ∧ s1 ∈ attendedBy attendsU s0 ∧ s1 ∉ attendsU s0)
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0 := by
  refine ⟨⟨rfl, ?_, ?_⟩, ws3_passive_constitution hinf s1 rfl (by decide)⟩
  · show s0 ∈ attendsU s1
    decide
  · show s1 ∉ attendsU s0
    decide

end P2S0
