/-
`program-2/series-2/formal/P2S2/ws1.lean`

WS1 - The other as a second attending locus (the construction). Program 2 Series 2 (2.2), the blocking
workstream.

Imports the `P2S1` ground and builds on its transitive API (`attends`/`outDest`, `rankLift`, the collapse
engine, `ws1_bound_is_finite_attention`, all reached through S1). Fixes the shared witness carrier `RCar = Fin 5`
(spec/README.md §3): the self `slf` (rank 0), the other `oth` (rank 1, the reified self-relation upgraded to a
locus reading back), a relatum `p` in the self's reach only (rank 0), a relatum `q` in the other's reach only
(rank 0), and a higher reader `bnd` (rank 2, the WS4 residue witness). The other is a relatum of the SAME field
`RCar`, minted by the pointwise section `reifyR {slf,oth,q} = oth` (which sections `attendsR`), its attention
`{slf,oth,q}` a genuine finite `attends` set reading back into the shared field. The two reaches are INCOMPARABLE
(`attendsR slf = {slf,oth,p}` and `attendsR oth = {slf,oth,q}`, `p ∈ slf∖oth`, `q ∈ oth∖slf`), so the WS4 residue
`bnd` is JOINTLY unattended with both memberships load-bearing (neither implies the other, the C2p2-R1 repair).
GENERALIZES S0's `ws1_first_other` (the self-loop reified into the first other) by giving the reified relatum its
own reading.

Design docs: `program-2/series-2/spec/ws1-design.md`; shared objects `spec/README.md` §1-§3.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1

universe u

namespace P2S2

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The shared witness carrier `RCar` (spec/README.md §3) -/

/-- The witness carrier: the self, the other (a second locus), the two private reaches, and a higher reader. -/
abbrev RCar : Type := Fin 5

def slf : RCar := 0   -- the self (base of the constitution tower)
def oth : RCar := 1   -- the OTHER: the reified self-relation upgraded to a locus reading back
def p   : RCar := 2   -- a relatum in the SELF's reach only (self reads it, the other does not)
def q   : RCar := 3   -- a relatum in the OTHER's reach only (the other reads it, the self does not)
def bnd : RCar := 4   -- a higher closure the pair does not jointly attend (WS4 residue witness)

/-- The witness attention: the self reads itself, the other, and its private `p`; the other reads itself, the
self, and its private `q`; `p` and `q` self-loop; the higher reader `bnd` reads only the other. The two reaches
`{slf,oth,p}` and `{slf,oth,q}` are INCOMPARABLE (each reads a relatum the other does not), so the mutual reading
combines two genuinely distinct reaches (the C2p2-R1 repair). -/
def attendsR : RCar → Finset RCar := fun x =>
  if x = slf then {slf, oth, p}
  else if x = oth then {slf, oth, q}
  else if x = p then {p}
  else if x = q then {q}
  else {oth}

/-- The reification-tower height: the bases (`slf`, `p`, `q`) at 0, the other at 1 (the reified self-relation),
`bnd` at 2. -/
def rankR : RCar → ℕ := fun x => if x = oth then 1 else if x = bnd then 2 else 0

/-- The pointwise section: the other's reach pattern `{slf,oth,q}` reifies to the other; `{oth}` to `bnd`; else
the self. Total `FinReify` is unsatisfiable on the finite carrier (as in S0/S1), so the section is pointwise. -/
def reifyR : Finset RCar → RCar := fun s =>
  if s = {slf, oth, q} then oth else if s = {oth} then bnd else slf

/-- The shared field of the facing: the self, the other, and what they attend. -/
def rfield : Finset RCar := {slf, oth, p, q}

/-! ## Carrier lemmas (all reduce by the kernel; `decide`/`rfl`) -/

lemma attendsR_slf : attendsR slf = {slf, oth, p} := rfl
lemma attendsR_oth : attendsR oth = {slf, oth, q} := rfl
lemma attendsR_bnd : attendsR bnd = {oth} := rfl

lemma attendsR_nonempty : ∀ x : RCar, (attendsR x).Nonempty := by decide

variable {κ : Cardinal.{0}}

lemma outDestR_ne_empty (hinf : ℵ₀ ≤ κ) (x : RCar) : (outDest hinf attendsR x).1 ≠ ∅ := by
  show (↑(attendsR x) : Set RCar) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsR_nonempty x))

/-- Every witness node is `SHNE` (all successor sets nonempty), so the collapse engine applies to every pair. -/
lemma ws1_rcar_SHNE (hinf : ℵ₀ ≤ κ) (x : RCar) : SHNE (outDest hinf attendsR) x :=
  fun v _ => outDestR_ne_empty hinf v

/-- The general fact `plainOf (rankLift dest lab) = dest` on `RCar` (the tower label forgets to the relating). -/
lemma plainOf_rankLiftR (dest : RCar → PkObj κ RCar) (lab : RCar → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

/-- The labelled edge set at `x`. -/
lemma rankLiftR_val (dest : RCar → PkObj κ RCar) (lab : RCar → ℕ) (x : RCar) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1 := rfl

/-! ## The payoff -/

/-- **THE OTHER IS A GENUINE SECOND LOCUS (WS1).** The other `oth` is a relatum of the SAME field `RCar`, minted
by reifying its reach pattern `{slf,oth,q}` (the pointwise `FinReify` section `attendsR (reifyR {slf,oth,q}) =
{slf,oth,q}`), distinct from the self, its attention a genuine finite nonempty `attends` set, reading a shared
field `rfield` that contains both the self and the other and every relatum either attends; the out-neighborhoods
are finite (`< ℵ₀`, S0's bound, no cardinal ceiling). The well-formedness is DISCHARGED (`decide`/`rfl`), not
posited by an opaque constructor. GENERALIZES S0's `ws1_first_other` by giving the reified relatum its own
reading back into the field. -/
theorem ws1_other_is_locus (hinf : ℵ₀ ≤ κ) :
    (reifyR {slf, oth, q} = oth ∧ attendsR (reifyR {slf, oth, q}) = {slf, oth, q})
  ∧ oth ≠ slf
  ∧ (attendsR oth).Nonempty
  ∧ (slf ∈ rfield ∧ oth ∈ rfield
      ∧ (∀ z ∈ attendsR slf, z ∈ rfield) ∧ (∀ z ∈ attendsR oth, z ∈ rfield))
  ∧ (∀ x : RCar, Cardinal.mk (↥((outDest hinf attendsR x).1)) < Cardinal.aleph0) := by
  refine ⟨⟨by decide, by decide⟩, by decide, ⟨slf, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩,
          ws1_bound_is_finite_attention hinf attendsR⟩

end P2S2
