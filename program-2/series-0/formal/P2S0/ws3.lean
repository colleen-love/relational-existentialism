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

/-- **PASSIVE CONSTITUTION IS REAL AND LOAD-BEARING (audit (b)).** `b` is attended by `a` (`a ∈ attendedBy b`)
and attends nothing (`attendsD b = ∅`): PASSIVE. Yet `b` is plain-bisimilar to the ACTIVE `a`
(`AttentionDistinguishes`, imported) and NOT label-bisimilar: what makes `b` passive is the directed reader,
not the plain relating. `attends`/`attendedBy` are load-bearing in the statement; the directed structure does
work the plain relating cannot (`ws3_direction_not_recoverable`), so the asymmetry is a genuine reader, not
the Series 11 Bookkeeping tag. -/
theorem ws3_passive_constitution (hinf : ℵ₀ ≤ κ) :
    (a ∈ attendedBy attendsD b ∧ attendsD b = ∅)
  ∧ AttentionDistinguishes (knowLiftD hinf) a b := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show b ∈ attendsD a
    decide
  · decide
  · exact ws1_atomless_bisim (plainOf (knowLiftD hinf)) a b (ws3_SHNE hinf a) (ws3_SHNE hinf b)
  · exact ws3_label_sep hinf

/-- **ACTIVE AND PASSIVE ARE TWO.** Active constitution (`attendsD a = {b}`, `a` made by what it reaches) and
passive constitution (`attendsD b = ∅`, `b` made only by what reaches it) yield the SAME plain position
(plain-bisimilar) but the directed structure tells them apart (label-separated). The reaching and the
being-reached are two becomings, not one. -/
theorem ws3_active_passive_distinct (hinf : ℵ₀ ≤ κ) :
    (attendsD a ≠ attendsD b)
  ∧ (∃ R, IsBisim (plainOf (knowLiftD hinf)) R ∧ R a b)
  ∧ (¬ ∃ R, IsBisimL (knowLiftD hinf) R ∧ R a b) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact ws1_atomless_bisim (plainOf (knowLiftD hinf)) a b (ws3_SHNE hinf a) (ws3_SHNE hinf b)
  · exact ws3_label_sep hinf

end P2S0
