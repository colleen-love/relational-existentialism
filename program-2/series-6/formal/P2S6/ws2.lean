/-
`program-2/series-6/formal/P2S6/ws2.lean`

WS2 - The weak continuity (recoverable, or import?). Program 2 Series 6 (2.6), where the series lives.

Builds the WEAK CONTINUITY as a continuity lift over the relating, coarser than the rank lift that fixes strict
identity, and proves the fork's substance on two FRESH carriers. General lemmas first: `plainOf_rankLift_gen`
(the plain reduct forgets the label), `const_first_recoverable` (a lift all of whose edge-labels share one value
is `Recoverable` - the RECOVERABLE horn), `distinguishes_not_recoverable` (a lift separating a plain-bisimilar
pair is not `Recoverable` - the IMPORT horn). Then the MERGED carrier `MCar` (`m0 ⇄ m1`, mutual attention, uniform
mark) where the continuity is `Recoverable` (WOVEN), and the CUT carrier `CCar` (`c0 → c1`, one-way, directional
mark) where it is not (SEVERED, the knowing-asymmetry). The weak continuity is GENUINELY WEAKER than strict
identity (`ws2_weaker_than_strict`): over the same relating the rank lift separates `m1`,`m0` while the continuity
lift is recoverable and its plain reduct relates them - not strict identity relabelled (audit b).

Design docs: `program-2/series-6/spec/ws2-design.md`; shared objects `spec/README.md` §2.1-§2.4.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S6.ws1

universe u

namespace P2S6

open P1.Core P1.Reader P2S0 P2S1 Cardinal

set_option linter.unusedVariables false

variable {κ : Cardinal.{0}}

/-! ## General recoverability lemmas (the two horns of the import test) -/

/-- The plain reduct of a rank-style lift forgets the label (general form of `plainOf_rankLiftT`). -/
lemma plainOf_rankLift_gen {X : Type} (dest : X → PkObj κ X) (lab : X → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- **THE RECOVERABLE HORN.** A labelled lift all of whose edge-labels equal one constant `c` is `Recoverable`:
every plain bisimulation is already a label bisimulation, because the first coordinates always match (all `c`)
and the second coordinates are matched by the plain bisimulation. -/
theorem const_first_recoverable {Q X : Type} (destL : X → LkObj κ Q X) (c : Q)
    (hconst : ∀ x, ∀ p ∈ (destL x).1, p.1 = c) : Recoverable destL := by
  intro R hR x y hxy
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp2 : p.2 ∈ (plainOf destL x).1 := ⟨p, hp, rfl⟩
    obtain ⟨hfwd, _⟩ := hR x y hxy
    obtain ⟨y', hy', hRel⟩ := hfwd p.2 hp2
    obtain ⟨q, hq, hqeq⟩ := hy'
    exact ⟨q, hq, by rw [hconst x p hp, hconst y q hq], by rw [hqeq]; exact hRel⟩
  · intro q hq
    have hq2 : q.2 ∈ (plainOf destL y).1 := ⟨q, hq, rfl⟩
    obtain ⟨_, hbwd⟩ := hR x y hxy
    obtain ⟨x', hx', hRel⟩ := hbwd q.2 hq2
    obtain ⟨p, hp, hpeq⟩ := hx'
    exact ⟨p, hp, by rw [hconst x p hp, hconst y q hq], by rw [hpeq]; exact hRel⟩

/-- **THE IMPORT HORN.** A labelled lift that distinguishes a plain-bisimilar pair (`AttentionDistinguishes`) is
NOT `Recoverable`: a recoverable label would lift the plain bisimulation to a label bisimulation
(`ws4_recoverable_not_import`), contradicting the separation. -/
theorem distinguishes_not_recoverable {Q X : Type} (destL : X → LkObj κ Q X) (x y : X)
    (h : AttentionDistinguishes destL x y) : ¬ Recoverable destL := by
  intro hrec
  obtain ⟨hbisim, hsep⟩ := h
  exact hsep (ws4_recoverable_not_import destL hrec x y hbisim)

/-! ## The MERGED carrier (m0 ⇄ m1, mutual attention; the woven stream) -/

/-- The merged carrier: two moments in one stream. -/
abbrev MCar : Type := Fin 2
def m0 : MCar := 0   -- a base moment (rank 0)
def m1 : MCar := 1   -- the reified successor moment (rank 1)

/-- Mutual attention: `m0 ⇄ m1` (one merged stream). -/
def attendsM : MCar → Finset MCar := fun x => if x = m0 then {m1} else {m0}
/-- The tower rank: `m1` the reified successor outranks `m0`. -/
def rankM : MCar → ℕ := fun x => if x = m0 then 0 else 1
/-- The merged continuity lift: a UNIFORM continuity mark `true` on every edge (one stream). -/
noncomputable def mergeLift (hinf : ℵ₀ ≤ κ) : MCar → LkObj κ Bool MCar :=
  fun x => if x = m0 then pkSingle hinf ((true : Bool), m1) else pkSingle hinf ((true : Bool), m0)

lemma attendsM_nonempty : ∀ x : MCar, (attendsM x).Nonempty := by decide

lemma outDestM_ne_empty (hinf : ℵ₀ ≤ κ) (x : MCar) : (outDest hinf attendsM x).1 ≠ ∅ := by
  show (↑(attendsM x) : Set MCar) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsM_nonempty x))

/-- Every merged moment is `SHNE` (all successor sets nonempty), so the collapse engine applies. -/
lemma ws_mcar_SHNE (hinf : ℵ₀ ≤ κ) (x : MCar) : SHNE (outDest hinf attendsM) x :=
  fun v _ => outDestM_ne_empty hinf v

lemma mergeLift_m0 (hinf : ℵ₀ ≤ κ) : (mergeLift hinf m0).1 = {((true : Bool), m1)} := by
  unfold mergeLift; rw [if_pos rfl, pkSingle_val]
lemma mergeLift_m1 (hinf : ℵ₀ ≤ κ) : (mergeLift hinf m1).1 = {((true : Bool), m0)} := by
  unfold mergeLift; rw [if_neg (by decide : ¬ m1 = m0), pkSingle_val]

/-- The tower-labelled edge set at `x` on the merged carrier (an `rfl` unfolding of `rankLift`). -/
lemma rankLiftM_val (hinf : ℵ₀ ≤ κ) (x : MCar) :
    (rankLift (outDest hinf attendsM) rankM x).1
      = (fun z => ((⟨rankM x⟩ : ULift.{0} ℕ), z)) '' (↑(attendsM x) : Set MCar) := rfl

/-! ## The CUT carrier (c0 → c1, one-way; the severed stream) -/

/-- The cut carrier: two moments whose stream is cut. -/
abbrev CCar : Type := Bool
def c0 : CCar := true    -- the active moment (knows c1)
def c1 : CCar := false   -- the passive moment (does not know c0)

/-- The directional knowing the cut continuity encodes: `c0` knows `c1`; `c1` does not know `c0`. -/
@[reducible] def cutKnows : CCar → CCar → Prop := fun x y => x = c0 ∧ y = c1
/-- The directional knowing the merged continuity encodes: mutual. -/
@[reducible] def mergeKnows : MCar → MCar → Prop := fun x y => (x = m0 ∧ y = m1) ∨ (x = m1 ∧ y = m0)

/-- The cut continuity lift: the symmetric relating `c0 — c1` tagged with the directional knowing (`c0`'s edge
carries the active mark `c0`, `c1`'s edge the passive mark `c1`). The plain reduct is the symmetric 2-cycle. -/
noncomputable def cutLift (hinf : ℵ₀ ≤ κ) : CCar → LkObj κ CCar CCar :=
  fun x => if x = c0 then pkSingle hinf (c0, c1) else pkSingle hinf (c1, c0)

lemma cutLift_c0 (hinf : ℵ₀ ≤ κ) : (cutLift hinf c0).1 = {(c0, c1)} := by
  unfold cutLift; rw [if_pos rfl, pkSingle_val]
lemma cutLift_c1 (hinf : ℵ₀ ≤ κ) : (cutLift hinf c1).1 = {(c1, c0)} := by
  unfold cutLift; rw [if_neg (by decide : ¬ c1 = c0), pkSingle_val]

lemma plainOf_cutLift_ne_empty (hinf : ℵ₀ ≤ κ) (v : CCar) : (plainOf (cutLift hinf) v).1 ≠ ∅ := by
  have h1 : ((cutLift hinf v).1).Nonempty := by
    unfold cutLift; split <;> · rw [pkSingle_val]; exact Set.singleton_nonempty _
  simp only [plainOf, PkMap_val]
  exact (h1.image Prod.snd).ne_empty

/-- Both cut moments are `SHNE` over the symmetric plain relating (the collapse engine applies). -/
lemma cut_SHNE (hinf : ℵ₀ ≤ κ) (x : CCar) : SHNE (plainOf (cutLift hinf)) x :=
  fun v _ => plainOf_cutLift_ne_empty hinf v

/-- The cut continuity mark separates `c0` and `c1`: no label-bisimulation relates them (`c0`'s edge carries the
active mark `c0`, `c1`'s only edge the passive mark `c1`). Mirrors `P2S0.ws3_label_sep`. -/
lemma cutLift_label_sep (hinf : ℵ₀ ≤ κ) : ¬ ∃ R, IsBisimL (cutLift hinf) R ∧ R c0 c1 := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR c0 c1 hRel
  obtain ⟨q, hq, hfst, _⟩ := hfwd (c0, c1) (by rw [cutLift_c0]; exact Set.mem_singleton _)
  rw [cutLift_c1, Set.mem_singleton_iff] at hq
  subst hq
  exact absurd hfst (by decide)

/-! ## The fork's substance -/

/-- **THE RECOVERABLE HORN (WOVEN).** The merged continuity is `Recoverable`: its mark is the uniform `true`, so by
`const_first_recoverable` every plain bisimulation is a continuity bisimulation. The continuity is endogenous. -/
theorem ws2_cont_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (mergeLift hinf) := by
  apply const_first_recoverable (mergeLift hinf) (true : Bool)
  intro x p hp
  unfold mergeLift at hp
  split at hp <;> (rw [pkSingle_val, Set.mem_singleton_iff] at hp; subst hp; rfl)

/-- **THE IMPORT HORN (SEVERED).** The cut continuity is NOT `Recoverable`: `c0`,`c1` are plain-bisimilar (the
collapse engine on the symmetric relating) yet the directional mark separates them (`cutLift_label_sep`), so by
`distinguishes_not_recoverable` the continuity is an import. Mirrors `P2S0.ws3_direction_not_recoverable`. -/
theorem ws2_cont_is_import (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (cutLift hinf) := by
  apply distinguishes_not_recoverable (cutLift hinf) c0 c1
  refine ⟨?_, cutLift_label_sep hinf⟩
  exact ws1_atomless_bisim (plainOf (cutLift hinf)) c0 c1 (cut_SHNE hinf c0) (cut_SHNE hinf c1)

/-- **THE WEAK CONTINUITY IS GENUINELY WEAKER THAN STRICT IDENTITY (audit b).** On the merged carrier, over the
one plain relating `outDest hinf attendsM`, the rank lift (strict identity) SEPARATES `m1`,`m0` while the
continuity lift (weak) is `Recoverable`. So the weak continuity holds where strict identity fails: a genuine
intermediate, not strict identity relabelled. -/
theorem ws2_weaker_than_strict (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0
  ∧ Recoverable (mergeLift hinf) := by
  refine ⟨⟨?_, ?_⟩, ws2_cont_recoverable hinf⟩
  · rw [plainOf_rankLift_gen]
    exact ws1_atomless_bisim (outDest hinf attendsM) m1 m0 (ws_mcar_SHNE hinf m1) (ws_mcar_SHNE hinf m0)
  · rintro ⟨R, hR, hRel⟩
    obtain ⟨hfwd, _⟩ := hR m1 m0 hRel
    have hedge : ((⟨rankM m1⟩ : ULift.{0} ℕ), m0) ∈ (rankLift (outDest hinf attendsM) rankM m1).1 := by
      rw [rankLiftM_val]
      exact ⟨m0, by show m0 ∈ (↑(attendsM m1) : Set MCar); exact Finset.mem_coe.mpr (by decide), rfl⟩
    obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
    rw [rankLiftM_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have : rankM m1 = rankM m0 := congrArg ULift.down hfst
    exact absurd this (by decide)

end P2S6
