/-
`program-2/series-1/formal/P2S1/ws1.lean`

WS1 - The attention cycle and its composite (the tick). Program 2 Series 1 (2.1), the blocking workstream.

Imports the `P2S0` ground and builds on its API (`attends`/`outDest`, `FinReify`, `rankLift` via `P1.Reader`,
`ws1_bound_is_finite_attention`, the collapse engine reached transitively). Fixes the shared witness carrier
`TCar = Fin 7` (spec/README.md §3): two genuine 2-cycles `p0⇄p1`, `q0⇄q1`; their composites `kA = reifyT
{p0,p1}`, `kB = reifyT {q0,q1}`; and a higher closure `kC = reifyT {kA,kB}` consuming both. The composite's
`attends` is exactly its cycle pattern (the pointwise `FinReify` section), it is a relatum of the SAME field
`TCar` (no new layer of substance), and its attention is a genuine finite `attends` set. This GENERALIZES S0's
`ws1_first_other` (the self-loop reified into the first other is the length-1 base case).

Design docs: `program-2/series-1/spec/ws1-design.md`; shared objects `spec/README.md` §1-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S0

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The shared witness carrier `TCar` (spec/README.md §3) -/

/-- The witness carrier: two 2-cycles, their composites, and a higher closure. -/
abbrev TCar : Type := Fin 7

def p0 : TCar := 0   -- base, cycle A
def p1 : TCar := 1   -- base, cycle A
def q0 : TCar := 2   -- base, cycle B
def q1 : TCar := 3   -- base, cycle B
def kA : TCar := 4   -- the composite of cycle A (a tick)
def kB : TCar := 5   -- the composite of cycle B (a tick)
def kC : TCar := 6   -- a higher closure consuming kA, kB

/-- The witness attention: `p0 ⇄ p1` and `q0 ⇄ q1` (two genuine 2-cycles); `kA` attends its cycle `{p0,p1}`,
`kB` its cycle `{q0,q1}`, and `kC` consumes the two ticks `{kA,kB}`. -/
def attendsT : TCar → Finset TCar := fun x =>
  if x = p0 then {p1}
  else if x = p1 then {p0}
  else if x = q0 then {q1}
  else if x = q1 then {q0}
  else if x = kA then {p0, p1}
  else if x = kB then {q0, q1}
  else {kA, kB}

/-- The reification-tower height: bases at 0, the ticks `kA`,`kB` at 1, the higher closure `kC` at 2.
NOT a clock: used only to separate a composite from its base, never to order `kA`,`kB` (equal height). -/
def rankT : TCar → ℕ := fun x =>
  if x = kA then 1 else if x = kB then 1 else if x = kC then 2 else 0

/-- Cycle A as a finite pattern. -/
def cycleA : Finset TCar := {p0, p1}
/-- Cycle B as a finite pattern. -/
def cycleB : Finset TCar := {q0, q1}

/-- The pointwise section: each cycle pattern reifies to its composite; the join pattern to `kC`; else `p0`.
Total `FinReify` is unsatisfiable on the finite carrier (as in S0), so the section is pointwise. -/
def reifyT : Finset TCar → TCar := fun s =>
  if s = cycleA then kA else if s = cycleB then kB else if s = ({kA, kB} : Finset TCar) then kC else p0

/-! ## Carrier lemmas (all reduce by the kernel; `decide`/`rfl`) -/

lemma attendsT_kA : attendsT kA = {p0, p1} := rfl
lemma attendsT_kB : attendsT kB = {q0, q1} := rfl
lemma attendsT_kC : attendsT kC = {kA, kB} := rfl

lemma reifyT_cycleA : reifyT cycleA = kA := rfl
lemma reifyT_cycleB : reifyT cycleB = kB := rfl
lemma reifyT_join   : reifyT ({kA, kB} : Finset TCar) = kC := by decide

/-- The pointwise `FinReify` sections at the three used patterns. -/
lemma section_cycleA : attendsT (reifyT cycleA) = cycleA := by decide
lemma section_cycleB : attendsT (reifyT cycleB) = cycleB := by decide
lemma section_join   : attendsT (reifyT ({kA, kB} : Finset TCar)) = ({kA, kB} : Finset TCar) := by decide

/-- Every node's attention is nonempty. -/
lemma attendsT_nonempty : ∀ x : TCar, (attendsT x).Nonempty := by decide

variable {κ : Cardinal.{0}}

lemma outDestT_ne_empty (hinf : ℵ₀ ≤ κ) (x : TCar) : (outDest hinf attendsT x).1 ≠ ∅ := by
  show (↑(attendsT x) : Set TCar) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsT_nonempty x))

/-- Every witness node is `SHNE` (all successor sets nonempty), so the collapse engine applies. -/
lemma ws1_tcar_SHNE (hinf : ℵ₀ ≤ κ) (x : TCar) : SHNE (outDest hinf attendsT) x :=
  fun v _ => outDestT_ne_empty hinf v

/-- The general fact `plainOf (rankLift dest lab) = dest` on `TCar` (the tower/label forgets to the relating). -/
lemma plainOf_rankLiftT (dest : TCar → PkObj κ TCar) (lab : TCar → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- The labelled edge set at `x`. -/
lemma rankLiftT_val (dest : TCar → PkObj κ TCar) (lab : TCar → ℕ) (x : TCar) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1 := rfl

/-! ## The payoffs -/

/-- **THE CYCLE REIFIES (WS1).** The genuine 2-cycle `p0 ⇄ p1` reifies into `kA`, a relatum of the SAME field
`TCar`, with the pointwise section `attendsT (reifyT cycleA) = cycleA` (the composite attends exactly its
cycle), and distinct cycles reify to distinct composites. Generalizes S0's `ws1_first_other` (the self-loop, a
length-1 cycle). The well-formedness is DISCHARGED (`decide`/`rfl`), not posited by an opaque constructor. -/
theorem ws1_cycle_reifies :
    (p1 ∈ attendsT p0 ∧ p0 ∈ attendsT p1)
  ∧ reifyT cycleA = kA
  ∧ attendsT (reifyT cycleA) = cycleA
  ∧ (reifyT cycleA ≠ reifyT cycleB
      ∧ reifyT cycleA ≠ reifyT ({kA, kB} : Finset TCar)
      ∧ reifyT cycleB ≠ reifyT ({kA, kB} : Finset TCar)) := by
  refine ⟨⟨?_, ?_⟩, rfl, section_cycleA, ?_, ?_, ?_⟩ <;> decide

/-- **THE COMPOSITE'S ATTENTION IS A GENUINE FINITE `attends`, COMPOSED FROM ITS COMPONENTS (WS1, audit (a)).**
The out-neighborhoods are finite (`< ℵ₀`), uniform in κ (S0's bound, no cardinal ceiling); `kA`'s attention is
exactly its cycle `cycleA`; and it attends no more than its components (`p0`, `p1`). -/
theorem ws1_composite_attention_finite (hinf : ℵ₀ ≤ κ) :
    (∀ x : TCar, Cardinal.mk (↥((outDest hinf attendsT x).1)) < Cardinal.aleph0)
  ∧ attendsT kA = cycleA
  ∧ (∀ z ∈ attendsT kA, z = p0 ∨ z = p1) := by
  refine ⟨ws1_bound_is_finite_attention hinf attendsT, ?_, ?_⟩
  · decide
  · decide

end P2S1
