/-
`program-2/series-4/formal/P2S4/ws1.lean`

WS1 - The world and the two gradings. Program 2 Series 4 (2.4), the blocking workstream.
-/
import P2S3

universe u

namespace P2S4

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The world carrier `W` (spec/README.md §2.1) -/

abbrev W : Type := Fin 4

def w0 : W := 0   -- the self (basepoint of the self-relative metric)
def w1 : W := 1   -- a peer, one lateral step from the self
def w2 : W := 2   -- a peer, two lateral steps from the self (real extent)
def r  : W := 3   -- a reified copy of the self's locus: same lateral coordinate, higher rank

/-- The directed 3-ring of same-rank peers plus the reified peer `r`. LOCAL: `w0` attends only `w1`. -/
def attendsW : W → Finset W := fun x =>
  if x = w0 then {w1}
  else if x = w1 then {w2}
  else if x = w2 then {w0}
  else {w1}

/-- The vertical grading (reification depth): peers at 0, the reified `r` at 1. -/
def rankW : W → ℕ := fun x => if x = r then 1 else 0

/-- The lateral coordinate (distance-from-the-self on the ring): `r` sits at the self's coordinate. -/
def latW : W → ℕ := fun x =>
  if x = w1 then 1 else if x = w2 then 2 else 0

variable {κ : Cardinal.{0}}

noncomputable def rankLiftW (hinf : ℵ₀ ≤ κ) : W → LkObj κ (ULift.{0} ℕ) W :=
  rankLift (outDest hinf attendsW) rankW
noncomputable def latLiftW (hinf : ℵ₀ ≤ κ) : W → LkObj κ (ULift.{0} ℕ) W :=
  rankLift (outDest hinf attendsW) latW

/-! ## Length-indexed directed reach (the path metric, path-grounded — audit d) -/

def reachIn (att : W → Finset W) : ℕ → W → W → Prop
  | 0,     x, y => x = y
  | (n+1), x, y => ∃ z ∈ att x, reachIn att n z y

instance reachInDec : (n : ℕ) → (x y : W) → Decidable (reachIn attendsW n x y)
  | 0,     x, y => decEq x y
  | (n+1), x, y =>
      haveI : DecidablePred (fun z => reachIn attendsW n z y) := fun z => reachInDec n z y
      inferInstanceAs (Decidable (∃ z ∈ attendsW x, reachIn attendsW n z y))

/-! ## Carrier lemmas -/

lemma attendsW_nonempty : ∀ x : W, (attendsW x).Nonempty := by decide

lemma outDestW_ne_empty (hinf : ℵ₀ ≤ κ) (x : W) : (outDest hinf attendsW x).1 ≠ ∅ := by
  show (↑(attendsW x) : Set W) ≠ ∅
  exact Set.Nonempty.ne_empty (Finset.coe_nonempty.mpr (attendsW_nonempty x))

/-- Every world node is `SHNE`, so `ws1_atomless_bisim` makes ANY two nodes plain-bisimilar. -/
lemma ws1_W_SHNE (hinf : ℵ₀ ≤ κ) (x : W) : SHNE (outDest hinf attendsW) x :=
  fun v _ => outDestW_ne_empty hinf v

/-- The labelled edge set at `x` (definitional). -/
lemma liftW_val (g : W → ℕ) (x : W) :
    (rankLift (outDest hinf attendsW) g x).1
      = (fun z => ((⟨g x⟩ : ULift.{0} ℕ), z)) '' (↑(attendsW x) : Set W) := rfl

/-! ## The payoffs -/

/-- **THE WORLD IS GENUINELY LATERAL (WS1).** Two same-rank peers at path-distance exactly 2 (> 1). -/
theorem ws1_lateral_extent :
    rankW w0 = rankW w2 ∧ w0 ≠ w2
  ∧ reachIn attendsW 2 w0 w2 ∧ ¬ reachIn attendsW 1 w0 w2 ∧ ¬ reachIn attendsW 0 w0 w2 := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide

/-- **THE LATERAL LABEL SEPARATES `w0` and `w2`.** No lat-bisimulation relates them (labels 0 vs 2). -/
lemma lat_sep_w0_w2 (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisimL (latLiftW hinf) R ∧ R w0 w2 := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, _⟩ := hR w0 w2 hRel
  have hedge : ((⟨latW w0⟩ : ULift.{0} ℕ), w1) ∈ (latLiftW hinf w0).1 := by
    rw [latLiftW, liftW_val]; exact ⟨w1, by decide, rfl⟩
  obtain ⟨q, hq, hfst, _⟩ := hfwd _ hedge
  rw [latLiftW, liftW_val] at hq
  obtain ⟨wt, hw, rfl⟩ := hq
  have : latW w0 = latW w2 := congrArg ULift.down hfst
  exact absurd this (by decide)

/-- **THE PEERS ARE NON-RECOVERABLE (WS1).** `w0`,`w2` are plain-bisimilar (the collapse engine, Series 07)
yet not lat-bisimilar: the lateral separation is a genuine import. -/
theorem ws1_peers_non_recoverable (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (latLiftW hinf) w0 w2 := by
  refine ⟨?_, lat_sep_w0_w2 hinf⟩
  have : plainOf (latLiftW hinf) = outDest hinf attendsW := by
    rw [latLiftW]; funext x; apply Subtype.ext
    show Prod.snd '' ((fun z => ((⟨latW x⟩ : ULift.{0} ℕ), z)) '' (↑(attendsW x) : Set W))
        = (↑(attendsW x) : Set W)
    rw [Set.image_image]; simp
  rw [this]
  exact ws1_atomless_bisim (outDest hinf attendsW) w0 w2 (ws1_W_SHNE hinf w0) (ws1_W_SHNE hinf w2)

/-- **NOT A TOWER (WS1).** The graph is LOCAL (non-complete: `w2 ∉ attendsW w0`) with same-rank multiplicity,
and the out-neighborhoods are finite (S0's bound, no cardinal ceiling). -/
theorem ws1_not_collapsed (hinf : ℵ₀ ≤ κ) :
    (w2 ∉ attendsW w0 ∧ reachIn attendsW 2 w0 w2)
  ∧ (rankW w0 = rankW w2 ∧ w0 ≠ w2)
  ∧ (∀ x : W, Cardinal.mk (↥((outDest hinf attendsW x).1)) < Cardinal.aleph0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ws1_bound_is_finite_attention hinf attendsW⟩

end P2S4
