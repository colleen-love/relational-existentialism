/-
`program-2/review/formal/PR2R1.lean`

PROGRAM REVIEW 2-1 REPAIRS (the Fixed branches of `program-2/spec/program-review-1.md`).

This module closes, in Lean, the closable halves of the program review's findings. It is a REVIEW artifact,
deliberately cross-cutting: it imports the probe tips of both Phase-3 branches (`P2S10`, `P2S12`, `P2S13`),
reaching every built layer transitively, because its theorems are ABOUT the built layers. Contents:

- **PR2-S1 (the two-sided wall).** A witness carrier `V` on which plain bisimilarity is NOT the total
  relation (`wall_collapse_not_total`), carrying BOTH a non-constant RECOVERABLE label
  (`wall_label_recoverable`) and a non-constant NON-recoverable label (`wall_label_import`): the first
  inhabitant of the recoverable side of the Import Theorem boundary on any Program 2 witness, so the
  import test genuinely discriminates on this carrier (`pr2s1_two_sided_wall`).
- **PR2-S4/S9 (the cone bounds the becoming).** The missing connective theorem: `n`-step reachability is
  CONTAINED in the ball (`pr2s4_cone_bounds_reach`), proved for every attention, from the triangle
  inequality and the sup-bound — plus the honest slack witness (`pr2s4_ball_exceeds_reach`): the ball is
  symmetric where the attention is not, so containment is strict.
- **PR2-S4/S11 (destructive iff odd holonomy).** The attention-level equivalence the series claimed in
  prose (`pr2s4_destructive_iff_odd_holonomy`): the combined weight falls below the parts iff the built
  holonomy is odd — for EVERY attention, not a ±1 truth table.
- **PR2-S4/S12 (the square is not forced — the obstruction, recorded).** `absWeight` (the |·|¹ form)
  RESPECTS the cancellation, is non-trivial and non-classical, and differs from the squared form
  (`pr2s4_square_not_unique`): the review's refutation of "FORCED," now a theorem in the artifact.
- **PR2-S4/S13 (the faithfulness bridge, and its limit).** `pathDist` applied to Series 2.4's OWN
  `attendsW` agrees with the built `stepsFrom` on every reachable pair (`pr2s4_bridge_faithful`), and
  provably DIVERGES on unreachable pairs (`pr2s4_bridge_diverges`: `stepsFrom` conflates unreachable with
  distance 0; `pathDist` reports the sentinel) — the bridge the re-seat lacked, with its seam disclosed.
- **PR2-S5 (the tick is not monotone).** The built reification lowers the measure at `e2` and is periodic
  on the 3-cycle (`pr2s5_tick_not_monotone`): the obstruction to the MONOTONE-ONLY reading, recorded.
- **PR2-S2 (the verdicts, tied).** For every series 2.0–2.13, a tying theorem: for ANY boolean flags
  whose truth is equivalent to the flag's justifying proposition, the verdict function computes the landed
  outcome (`pr2s2_sN_verdict_tied`). The flag-to-theorem link is now formal, not documentary. The two
  meta-flags with no propositional content (S6 `carrierDecided`, S7 `globalForced`) remain literal
  arguments, DISCLOSED: they are the Relabeled residue of PR2-S2.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S10
import P2S12
import P2S13

universe u

namespace PR2R1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

variable {κ : Cardinal.{0}}

/-! ## PR2-S1 — the two-sided wall: a carrier where the import test discriminates -/

/-- The wall carrier: a leaf and two self-loops. The FIRST Program 2 witness whose plain behavior is not
fully collapsed: the leaf `v0` is plain-distinguishable from the loops `v1`, `v2`, while the loops remain
plain-bisimilar to each other. -/
abbrev V : Type := Fin 3

def v0 : V := 0   -- the leaf (empty out-attention): plain-distinguishable structure
def v1 : V := 1   -- a self-loop
def v2 : V := 2   -- a second self-loop, plain-bisimilar to v1

/-- The attention: `v0` attends nothing; `v1`, `v2` self-attend. -/
def attV : V → Finset V := fun x => if x = v0 then ∅ else {x}

/-- A non-constant label ALIGNED with the plain structure (0 on the leaf, 1 on the loops). -/
def labL : V → ℕ := fun x => if x = v0 then 0 else 1

/-- A non-constant label ACROSS the plain-bisimilar pair (separating `v1` from `v2`). -/
def labD : V → ℕ := fun x => if x = v2 then 1 else 0

lemma attV_v0 : attV v0 = ∅ := rfl

lemma attV_loop : ∀ x : V, x ≠ v0 → attV x = {x} := by decide

lemma memV (hinf : ℵ₀ ≤ κ) {x z : V} (hz : z ∈ attV x) : z ∈ (outDest hinf attV x).1 := by
  show z ∈ (↑(attV x) : Set V)
  exact Finset.mem_coe.mpr hz

lemma memV' (hinf : ℵ₀ ≤ κ) {x z : V} (hz : z ∈ (outDest hinf attV x).1) : z ∈ attV x :=
  Finset.mem_coe.mp (show z ∈ (↑(attV x) : Set V) from hz)

/-- **THE COLLAPSE IS NOT TOTAL (PR2-S1).** No plain bisimulation relates a loop to the leaf: the plain
relating itself distinguishes them. On this carrier "plain-bisimilar" is genuinely informative. -/
theorem wall_collapse_not_total (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ R, IsBisim (outDest hinf attV) R ∧ R v1 v0 := by
  rintro ⟨R, hR, h10⟩
  obtain ⟨hfwd, -⟩ := hR v1 v0 h10
  obtain ⟨y, hy, -⟩ := hfwd v1 (memV hinf (by decide))
  have : y ∈ attV v0 := memV' hinf hy
  rw [attV_v0] at this
  exact Finset.not_mem_empty y this

/-- On this carrier the label-forgetting reduct of the rank lift is the plain attention (generic fact). -/
lemma plainOf_rankLiftV (dest : V → PkObj κ V) (lab : V → ℕ) :
    plainOf (rankLift dest lab) = dest := by
  funext x; apply Subtype.ext
  show Prod.snd '' ((fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1) = (dest x).1
  rw [Set.image_image]; simp

lemma rankLiftV_val (dest : V → PkObj κ V) (lab : V → ℕ) (x : V) :
    (rankLift dest lab x).1 = (fun z => ((⟨lab x⟩ : ULift.{0} ℕ), z)) '' (dest x).1 := rfl

/-- A plain bisimulation on the wall carrier never relates a loop to the leaf, in either order. -/
lemma bisim_respects_leaf (hinf : ℵ₀ ≤ κ) {R : V → V → Prop}
    (hR : IsBisim (outDest hinf attV) R) :
    ∀ x y, R x y → (x = v0 ↔ y = v0) := by
  intro x y hxy
  constructor
  · intro hx
    by_contra hy
    obtain ⟨-, hbwd⟩ := hR x y hxy
    have hyy : y ∈ attV y := by rw [attV_loop y hy]; exact Finset.mem_singleton_self y
    obtain ⟨z, hz, -⟩ := hbwd y (memV hinf hyy)
    have : z ∈ attV x := memV' hinf hz
    rw [hx, attV_v0] at this
    exact Finset.not_mem_empty z this
  · intro hy
    by_contra hx
    obtain ⟨hfwd, -⟩ := hR x y hxy
    have hxx : x ∈ attV x := by rw [attV_loop x hx]; exact Finset.mem_singleton_self x
    obtain ⟨z, hz, -⟩ := hfwd x (memV hinf hxx)
    have : z ∈ attV y := memV' hinf hz
    rw [hy, attV_v0] at this
    exact Finset.not_mem_empty z this

/-- **A NON-CONSTANT LABEL IS RECOVERABLE (PR2-S1, the missing side of the wall).** The leaf/loop label
`labL` is non-constant, yet every plain bisimulation already respects it: the distinction it draws is
carried by the plain relating. The recoverable side of the Import Theorem boundary is inhabited by a
genuine (non-constant) distinction — on every prior Program 2 witness it was inhabited only by constants. -/
theorem wall_label_recoverable (hinf : ℵ₀ ≤ κ) :
    labL v0 ≠ labL v1 ∧ Recoverable (rankLift (outDest hinf attV) labL) := by
  refine ⟨by decide, ?_⟩
  intro R hR
  rw [plainOf_rankLiftV] at hR
  intro x y hxy
  have hlab : labL x = labL y := by
    have hiff := bisim_respects_leaf hinf hR x y hxy
    by_cases hx : x = v0
    · rw [labL, labL, if_pos hx, if_pos (hiff.mp hx)]
    · rw [labL, labL, if_neg hx, if_neg (fun hy => hx (hiff.mpr hy))]
  obtain ⟨hfwd, hbwd⟩ := hR x y hxy
  constructor
  · rintro p hp
    rw [rankLiftV_val] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨w, hw, hRzw⟩ := hfwd z hz
    refine ⟨((⟨labL y⟩ : ULift.{0} ℕ), w), ?_, ?_, hRzw⟩
    · rw [rankLiftV_val]; exact ⟨w, hw, rfl⟩
    · show (⟨labL x⟩ : ULift.{0} ℕ) = ⟨labL y⟩
      rw [hlab]
  · rintro q hq
    rw [rankLiftV_val] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    obtain ⟨z, hz, hRzw⟩ := hbwd w hw
    refine ⟨((⟨labL x⟩ : ULift.{0} ℕ), z), ?_, ?_, hRzw⟩
    · rw [rankLiftV_val]; exact ⟨z, hz, rfl⟩
    · show (⟨labL x⟩ : ULift.{0} ℕ) = ⟨labL y⟩
      rw [hlab]

/-- The generic label-separation mechanism (the sound core of `P2S7.rankM_sep_general`), on `V`. -/
lemma sepV (dest : V → PkObj κ V) (lab : V → ℕ) (x y : V)
    (hlab : lab x ≠ lab y) (hne : (dest x).1 ≠ ∅) :
    ¬ ∃ R, IsBisimL (rankLift dest lab) R ∧ R x y := by
  rintro ⟨R, hR, hRel⟩
  obtain ⟨hfwd, -⟩ := hR x y hRel
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hedge : ((⟨lab x⟩ : ULift.{0} ℕ), z) ∈ (rankLift dest lab x).1 := by
    rw [rankLiftV_val]; exact ⟨z, hz, rfl⟩
  obtain ⟨q, hq, hfst, -⟩ := hfwd _ hedge
  rw [rankLiftV_val] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  exact hlab (congrArg ULift.down hfst)

/-- The loop pair is plain-bisimilar (a two-point bisimulation; not the total relation). -/
lemma loops_bisim (hinf : ℵ₀ ≤ κ) :
    ∃ R, IsBisim (outDest hinf attV) R ∧ R v1 v2 := by
  refine ⟨fun a b => a = v1 ∧ b = v2, ?_, rfl, rfl⟩
  rintro x y ⟨rfl, rfl⟩
  constructor
  · intro z hz
    have hz' : z ∈ attV v1 := memV' hinf hz
    rw [attV_loop v1 (by decide)] at hz'
    rw [Finset.mem_singleton] at hz'
    subst hz'
    exact ⟨v2, memV hinf (by decide), rfl, rfl⟩
  · intro w hw
    have hw' : w ∈ attV v2 := memV' hinf hw
    rw [attV_loop v2 (by decide)] at hw'
    rw [Finset.mem_singleton] at hw'
    subst hw'
    exact ⟨v1, memV hinf (by decide), rfl, rfl⟩

/-- **A LABEL ACROSS THE BISIMILAR PAIR IS AN IMPORT (PR2-S1, the familiar side, on the same carrier).**
`labD` separates the plain-bisimilar loops, so it is not recoverable — on the SAME carrier where `labL` is.
The import test discriminates: alignment with plain structure decides recoverability. -/
theorem wall_label_import (hinf : ℵ₀ ≤ κ) :
    labD v1 ≠ labD v2 ∧ ¬ Recoverable (rankLift (outDest hinf attV) labD) := by
  refine ⟨by decide, ?_⟩
  intro hrec
  obtain ⟨R, hR, h12⟩ := loops_bisim hinf
  have hRL : IsBisimL (rankLift (outDest hinf attV) labD) R := by
    apply hrec
    rw [plainOf_rankLiftV]
    exact hR
  exact sepV (outDest hinf attV) labD v1 v2 (by decide)
    (by
      show (↑(attV v1) : Set V) ≠ ∅
      rw [attV_loop v1 (by decide)]
      simp)
    ⟨R, hRL, h12⟩

/-- **THE TWO-SIDED WALL (PR2-S1, the finding's Fixed branch).** On one carrier: the collapse is not total,
a non-constant label aligned with the plain structure is RECOVERABLE, and a non-constant label across the
bisimilar pair is an IMPORT. Both sides of the Import Theorem boundary are inhabited by genuine
distinctions, and the test discriminates between them. -/
theorem pr2s1_two_sided_wall (hinf : ℵ₀ ≤ κ) :
    (¬ ∃ R, IsBisim (outDest hinf attV) R ∧ R v1 v0)
  ∧ (labL v0 ≠ labL v1 ∧ Recoverable (rankLift (outDest hinf attV) labL))
  ∧ (labD v1 ≠ labD v2 ∧ ¬ Recoverable (rankLift (outDest hinf attV) labD)) :=
  ⟨wall_collapse_not_total hinf, wall_label_recoverable hinf, wall_label_import hinf⟩

/-! ## PR2-S4 / Series 2.9 — the cone bounds the becoming (the missing connective theorem) -/

/-- The inductive bound: if every seed is within `rate·m`, everything reached in `n` more closure steps is
within `rate·(m+n)`. Triangle inequality plus the sup-bound, for EVERY attention. -/
lemma reach_bound (att : P2S9.S → Finset P2S9.S) (x : P2S9.S) :
    ∀ (n : ℕ) (R : Finset P2S9.S) (m : ℕ),
      (∀ y ∈ R, P2S9.dist x y ≤ P2S9.rate att * m) →
      ∀ y ∈ P2S9.reachN att n R, P2S9.dist x y ≤ P2S9.rate att * (m + n) := by
  intro n
  induction n with
  | zero =>
      intro R m hR y hy
      simpa using hR y hy
  | succ n ih =>
      intro R m hR y hy
      have hstep : ∀ z ∈ R ∪ R.biUnion att, P2S9.dist x z ≤ P2S9.rate att * (m + 1) := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact le_trans (hR z hz) (Nat.mul_le_mul_left _ (Nat.le_succ m))
        · obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.mp hz
          have htri : P2S9.dist x z ≤ P2S9.dist x w + P2S9.dist w z :=
            Nat.dist.triangle_inequality _ _ _
          have hspan : P2S9.dist w z ≤ P2S9.span att w := Finset.le_sup hzw
          have hrate : P2S9.span att w ≤ P2S9.rate att := Finset.le_sup (Finset.mem_univ w)
          calc P2S9.dist x z ≤ P2S9.dist x w + P2S9.dist w z := htri
            _ ≤ P2S9.rate att * m + P2S9.rate att :=
                Nat.add_le_add (hR w hw) (le_trans hspan hrate)
            _ = P2S9.rate att * (m + 1) := (Nat.mul_succ _ _).symm
      have hy' : y ∈ P2S9.reachN att n (R ∪ R.biUnion att) := hy
      have := ih (R ∪ R.biUnion att) (m + 1) hstep y hy'
      have harith : P2S9.rate att * (m + 1 + n) = P2S9.rate att * (m + (n + 1)) := by
        ring
      rw [harith] at this
      exact this

/-- **THE CONE BOUNDS THE BECOMING (PR2-S4/S9, the Series 2.9 WS2 target, delivered).** For EVERY attention,
source, and depth, whatever is reached in `n` closure steps lies inside the ball of radius `rate·n`. The
cone genuinely bounds the causal reach — a theorem, not an unfolded definition. -/
theorem pr2s4_cone_bounds_reach (att : P2S9.S → Finset P2S9.S) (x : P2S9.S) (n : ℕ) :
    ∀ y ∈ P2S9.reachN att n {x}, y ∈ P2S9.ball att x n := by
  intro y hy
  have hseed : ∀ z ∈ ({x} : Finset P2S9.S), P2S9.dist x z ≤ P2S9.rate att * 0 := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    simp [P2S9.dist, Nat.dist_self]
  have := reach_bound att x n {x} 0 hseed y hy
  rw [Nat.zero_add] at this
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, this⟩

/-- **THE SLACK IS REAL AND DISCLOSED (PR2-S4/S9).** The converse fails: the ball is symmetric where the
attention is directed, so the cone strictly over-approximates the reach (`p0` is in `p1`'s depth-1 ball but
is never reached from `p1` under `attSlow`). The containment above is the honest content; equality is not. -/
theorem pr2s4_ball_exceeds_reach :
    P2S9.p0 ∈ P2S9.ball P2S9.attSlow P2S9.p1 1
  ∧ P2S9.p0 ∉ P2S9.reachSet P2S9.attSlow P2S9.p1 := by
  constructor <;> decide

/-! ## PR2-S4 / Series 2.11 — destructive interference iff odd holonomy (attention-level) -/

/-- The sign-level equivalence: the combined square falls strictly below the parts iff the argument is odd. -/
lemma amp_destructive_iff (h : ℤ) :
    (P2S11.amp 0 + P2S11.amp h) ^ 2 < (P2S11.amp 0) ^ 2 + (P2S11.amp h) ^ 2 ↔ h % 2 ≠ 0 := by
  by_cases hh : h % 2 = 0
  · simp only [P2S11.amp, if_pos hh, if_pos (show (0 : ℤ) % 2 = 0 by decide)]
    constructor
    · intro hlt; norm_num at hlt
    · intro hne; exact absurd hh hne
  · simp only [P2S11.amp, if_neg hh, if_pos (show (0 : ℤ) % 2 = 0 by decide)]
    constructor
    · intro _; exact hh
    · intro _; norm_num

/-- **DESTRUCTIVE IFF ODD HOLONOMY (PR2-S4/S11, the claimed equivalence, delivered at the attention
level).** For EVERY attention on the population: the combined weight falls strictly below the parts iff the
built holonomy around the triangle is odd. The interference fact is now tied to the model quantity for all
512 attentions, not read off two carriers. -/
theorem pr2s4_destructive_iff_odd_holonomy (att : P2S8.S → Finset P2S8.S) :
    P2S11.combinedWeight att < P2S11.partsWeight att
  ↔ P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2 % 2 ≠ 0 := by
  have := amp_destructive_iff (P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2)
  simpa [P2S11.combinedWeight, P2S11.partsWeight, P2S11.directAmp, P2S11.loopAmp] using this

/-! ## PR2-S4 / Series 2.12 — the square is not forced (the obstruction, recorded as a theorem) -/

/-- The |·|¹ candidate: the absolute value of the summed amplitudes. NOT the squared form. -/
def absWeight (att : P2S8.S → Finset P2S8.S) : ℤ := |P2S11.directAmp + P2S11.loopAmp att|

/-- **THE SQUARE IS NOT FORCED (PR2-S4/S12, the review's refutation, now in the artifact).** `absWeight`
RESPECTS the cancellation, is non-negative, non-trivial (0 on the ring, 2 on the star), falls below the
parts on the ring (non-classical), and DIFFERS from the squared form. So `respectsCancel` selects a class
containing non-squared members: the exponent 2 — the Born-specific content — is not forced by the test.
This is the formal ceiling of the BORN verdict, recorded per protocol §0.2a. -/
theorem pr2s4_square_not_unique :
    P2S12.respectsCancel absWeight
  ∧ (∀ att, 0 ≤ absWeight att)
  ∧ (absWeight P2S8.attTri = 0 ∧ absWeight P2S8.attStar = 2)
  ∧ (absWeight P2S8.attTri < P2S11.partsWeight P2S8.attTri)
  ∧ (∃ att, absWeight att ≠ P2S11.combinedWeight att) := by
  refine ⟨?_, ?_, ⟨by decide, by decide⟩, by decide, ⟨P2S8.attStar, by decide⟩⟩
  · intro att h
    rw [absWeight, h]
    simp
  · intro att
    exact abs_nonneg _

/-! ## PR2-S4 / Series 2.13 — the faithfulness bridge to the built distance, and its seam -/

/-- No node attends the reified peer `r` in Series 2.4's world: `r` is unreachable from the peers. -/
lemma no_attend_r : ∀ w : P2S4.W, P2S4.r ∉ P2S4.attendsW w := by decide

lemma no_reach_r : ∀ (n : ℕ) (x : P2S4.W), x ≠ P2S4.r →
    ¬ P2S4.reachIn P2S4.attendsW n x P2S4.r := by
  intro n
  induction n with
  | zero => intro x hx h; exact hx h
  | succ n ih =>
      rintro x hx ⟨z, hz, hzr⟩
      have hzne : z ≠ P2S4.r := fun h => no_attend_r x (h ▸ hz)
      exact ih z hzne hzr

/-- `stepsFrom` gives 0 on unreachable pairs (`sInf ∅ = 0`): the seam the bridge must disclose. -/
lemma stepsFrom_unreachable (x : P2S4.W) (hx : x ≠ P2S4.r) : P2S4.stepsFrom x P2S4.r = 0 := by
  unfold P2S4.stepsFrom
  have hempty : {n | P2S4.reachIn P2S4.attendsW n x P2S4.r} = ∅ :=
    Set.eq_empty_iff_forall_not_mem.mpr (fun n => no_reach_r n x hx)
  rw [hempty]
  exact Nat.sInf_empty

/-- **THE BRIDGE IS FAITHFUL ON REACHABLE PAIRS (PR2-S4/S13, the missing theorem).** Series 2.13's
`pathDist`, applied to Series 2.4's OWN adjacency `attendsW`, agrees with the built `stepsFrom` on every
pair the built world can reach: all nine peer pairs and all four pairs from the reified peer. The re-seat
is now connected to the built object by proof, exactly where the built object is defined. -/
theorem pr2s4_bridge_faithful :
    (P2S13.pathDist P2S4.attendsW P2S4.w0 P2S4.w0 = P2S4.stepsFrom P2S4.w0 P2S4.w0)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w0 P2S4.w1 = P2S4.stepsFrom P2S4.w0 P2S4.w1)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w0 P2S4.w2 = P2S4.stepsFrom P2S4.w0 P2S4.w2)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w1 P2S4.w0 = P2S4.stepsFrom P2S4.w1 P2S4.w0)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w1 P2S4.w1 = P2S4.stepsFrom P2S4.w1 P2S4.w1)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w1 P2S4.w2 = P2S4.stepsFrom P2S4.w1 P2S4.w2)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w2 P2S4.w0 = P2S4.stepsFrom P2S4.w2 P2S4.w0)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w2 P2S4.w1 = P2S4.stepsFrom P2S4.w2 P2S4.w1)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.w2 P2S4.w2 = P2S4.stepsFrom P2S4.w2 P2S4.w2)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.r P2S4.w0 = P2S4.stepsFrom P2S4.r P2S4.w0)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.r P2S4.w1 = P2S4.stepsFrom P2S4.r P2S4.w1)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.r P2S4.w2 = P2S4.stepsFrom P2S4.r P2S4.w2)
  ∧ (P2S13.pathDist P2S4.attendsW P2S4.r P2S4.r = P2S4.stepsFrom P2S4.r P2S4.r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P2S4.stepsFrom_eq _ _ 0 (by decide) (fun m hm => by omega)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 1 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 2 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 2 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 0 (by decide) (fun m hm => by omega)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 1 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 1 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 2 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 0 (by decide) (fun m hm => by omega)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 3 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 1 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 2 (by decide) (fun m hm => by interval_cases m <;> decide)]; decide
  · rw [P2S4.stepsFrom_eq _ _ 0 (by decide) (fun m hm => by omega)]; decide

/-- **THE BRIDGE DIVERGES ON UNREACHABLE PAIRS (PR2-S4/S13, the seam, disclosed as a theorem).** On the
pairs the built world cannot reach (the peers to `r`), `stepsFrom` reports 0 — conflating "unreachable"
with "here" (`sInf ∅ = 0`) — while `pathDist` reports the sentinel 4. The re-seat is NOT extensionally
faithful off the reachable fragment; any future reuse of either object must carry this seam. -/
theorem pr2s4_bridge_diverges :
    (P2S4.stepsFrom P2S4.w0 P2S4.r = 0 ∧ P2S13.pathDist P2S4.attendsW P2S4.w0 P2S4.r = 4)
  ∧ (P2S4.stepsFrom P2S4.w0 P2S4.w0 = 0)
  ∧ (∀ w : P2S4.W, P2S4.r ∉ P2S4.attendsW w) := by
  refine ⟨⟨stepsFrom_unreachable P2S4.w0 (by decide), by decide⟩, ?_, no_attend_r⟩
  rw [P2S4.stepsFrom_eq _ _ 0 (by decide) (fun m hm => by omega)]

/-! ## PR2-S5 — the built tick is not monotone (the obstruction, recorded) -/

/-- **THE TICK IS PERIODIC AND NOT MONOTONE (PR2-S5, the obstruction to the MONOTONE-ONLY reading).** The
built reification RAISES the measure at `e0` and `e1` but LOWERS it at `e2` (2 → 0), and the three
reachable states cycle with period three, the measure returning with them. What Series 2.7/2.10 prove
(the local rises; the exhaustive no-core) stands; what the verdict name and the "arrow" prose assert
(a monotone dynamics) is refuted by the model itself. Recorded per protocol §0.2a. -/
theorem pr2s5_tick_not_monotone :
    (P2S7.rankM (P2S7.reifyM {P2S7.e2}) < P2S7.rankM P2S7.e2)
  ∧ (P2S7.reifyM {P2S7.reifyM {P2S7.reifyM {P2S7.e0}}} = P2S7.e0)
  ∧ (P2S7.rankM (P2S7.reifyM {P2S7.e0}) = P2S7.rankM P2S7.e0 + 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## PR2-S2 — the verdicts, tied: flags bound to propositions, per series -/

/-- Series 2.0. The flags of `P2S0.verdict`, tied to their justifying propositions. -/
theorem pr2s2_s0_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 : Bool)
    (h1 : b1 = true ↔ AttentionDistinguishes
        (rankLift (outDest hinf P2S0.attendsU) P2S0.rankU) P2S0.s1 P2S0.s0)
    (h2 : b2 = true ↔ ¬ Recoverable (P2S0.knowLiftD hinf))
    (h3 : b3 = true ↔ (∀ (Q : Type) (f : Bool → Q), f true ≠ f false →
        ¬ ∃ R, IsBisimL (P2S0.impLift hinf f) R ∧ R true false)) :
    P2S0.verdict b1 b2 b3 = P2S0.Outcome.groundEstablished := by
  have j := P2S0.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr (fun Q f hf => j.2.2 f hf)
  subst e1; subst e2; subst e3; rfl

/-- Series 2.1. The flags of `P2S1.verdict`, tied. -/
theorem pr2s2_s1_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ P2S1.attendsT (P2S1.reifyT P2S1.cycleA) = P2S1.cycleA)
    (h2 : b2 = true ↔ (∀ x ∈ P2S1.attendsT P2S1.kA, P2S1.rankT x < P2S1.rankT P2S1.kA))
    (h3 : b3 = true ↔ (∀ ch : P2S1.TCar → ℕ, ch P2S1.kA ≠ ch P2S1.kB →
        ¬ Recoverable (rankLift (outDest hinf P2S1.attendsT) ch)))
    (h4 : b4 = true ↔ ((P2S1.causal P2S1.kA P2S1.kC ∧ P2S1.causal P2S1.kB P2S1.kC)
        ∧ (∀ t u : P2S1.TCar, P2S1.causal t u → P2S1.rankT t < P2S1.rankT u)
        ∧ (¬ P2S1.causal P2S1.kA P2S1.kB ∧ ¬ P2S1.causal P2S1.kB P2S1.kA)))
    (h5 : b5 = true ↔ (∀ ord : P2S1.TCar → ℕ, ord P2S1.kA ≠ ord P2S1.kB →
        ¬ Recoverable (rankLift (outDest hinf P2S1.attendsT) ord))) :
    P2S1.verdict b1 b2 b3 b4 b5 = P2S1.Outcome.twoZone := by
  have j := P2S1.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.2. The flags of `P2S2.verdict`, tied. (The sixth justified conjunct — the mutual residue —
feeds no flag; that gap is the series' own, disclosed in the program review as PR2-C1.) -/
theorem pr2s2_s2_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ P2S2.attendsR (P2S2.reifyR {P2S2.slf, P2S2.oth, P2S2.q})
        = {P2S2.slf, P2S2.oth, P2S2.q})
    (h2 : b2 = true ↔ RealFor (rankLift (outDest hinf P2S2.attendsR) P2S2.rankR)
        (P2S2.slfReader hinf) P2S2.oth)
    (h3 : b3 = true ↔ ¬ Recoverable (P2S2.faceLift hinf))
    (h4 : b4 = true ↔ ¬ Recoverable (rankLift (outDest hinf P2S2.attendsR) P2S2.rankR))
    (h5 : b5 = true ↔ (∀ insp : Hold (outDest hinf P2S2.attendsR) →
        HoldPred (outDest hinf P2S2.attendsR), ¬ ∃ t, SelfTotal insp t)) :
    P2S2.verdict b1 b2 b3 b4 b5 = P2S2.Outcome.twoFacing := by
  have j := P2S2.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.1
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.3. The flags of `P2S3.verdict`, tied. -/
theorem pr2s2_s3_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (∃ c₁ c₂ : P2S3.Valuation P2S2.RCar (ULift.{0} Bool),
        P2S3.Faithful₂ c₁ ∧ P2S3.Faithful₂ c₂
        ∧ P2S3.Converges₂ c₁ P2S2.slf P2S2.oth ∧ ¬ P2S3.Converges₂ c₂ P2S2.slf P2S2.oth))
    (h2 : b2 = true ↔ (∀ (Or : Type) (c : P2S3.Valuation P2S2.RCar Or),
        P2S3.Faithful₂ c → P2S3.InSight (outDest hinf P2S2.attendsR) c →
        P2S3.Converges₂ c P2S2.slf P2S2.oth))
    (h3 : b3 = true ↔ (∀ (Or : Type) (c : P2S3.Valuation P2S2.RCar Or),
        P2S3.Faithful₂ c → ¬ P2S3.Converges₂ c P2S2.slf P2S2.oth →
        ¬ Recoverable (P2S3.valLift (outDest hinf P2S2.attendsR) c.val)))
    (h4 : b4 = true ↔ ((∃ c : P2S3.Valuation P2S2.RCar (ULift.{0} Bool),
        P2S3.Faithful₂ c ∧ P2S3.InSight (outDest hinf P2S2.attendsR) c)
        ∧ (∃ c : P2S3.Valuation P2S2.RCar (ULift.{0} Bool),
        P2S3.Faithful₂ c ∧ ¬ P2S3.InSight (outDest hinf P2S2.attendsR) c))) :
    P2S3.verdict b1 b2 b3 b4 = P2S3.Outcome.shapeDrawn := by
  have j := P2S3.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2
  subst e1; subst e2; subst e3; subst e4; rfl

/-- Series 2.4. The flags of `P2S4.verdict`, tied. -/
theorem pr2s2_s4_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ (P2S4.rankW P2S4.w0 = P2S4.rankW P2S4.w2
        ∧ P2S4.reachIn P2S4.attendsW 2 P2S4.w0 P2S4.w2
        ∧ ¬ P2S4.reachIn P2S4.attendsW 1 P2S4.w0 P2S4.w2))
    (h2 : b2 = true ↔ ((¬ ∃ R, IsBisimL (P2S4.latLiftW hinf) R ∧ R P2S4.w0 P2S4.w2)
        ∧ (∃ R, IsBisimL (P2S4.rankLiftW hinf) R ∧ R P2S4.w0 P2S4.w2)
        ∧ (¬ ∃ R, IsBisimL (P2S4.rankLiftW hinf) R ∧ R P2S4.r P2S4.w0)
        ∧ (∃ R, IsBisimL (P2S4.latLiftW hinf) R ∧ R P2S4.r P2S4.w0)))
    (h3 : b3 = true ↔ ¬ Recoverable (P2S4.latLiftW hinf))
    (h4 : b4 = true ↔ (P2S4.rankW P2S4.w0 = P2S4.rankW P2S4.w2
        ∧ P2S4.latW P2S4.r = P2S4.latW P2S4.w0 ∧ P2S4.latT = P2S4.rankT)) :
    P2S4.verdict b1 b2 b3 b4 = P2S4.Outcome.distinct := by
  have j := P2S4.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2
  subst e1; subst e2; subst e3; subst e4; rfl

/-- Series 2.5. The flags of `P2S5.verdict`, tied — including the FALSE fifth flag, refuted by
`ws4_no_fold_on_tower` rather than assumed. -/
theorem pr2s2_s5_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ ((P2S1.p1 ∈ P2S1.attendsT P2S1.p0 ∧ P2S1.p0 ∈ P2S1.attendsT P2S1.p1)
        ∧ P2S1.attendsT (P2S1.reifyT P2S1.cycleA) = P2S1.cycleA))
    (h2 : b2 = true ↔ (¬ ∃ x : P2S1.TCar,
        Relation.TransGen (P2S5.causalDep P2S1.attendsT P2S1.isTick) x x))
    (h3 : b3 = true ↔ (∀ x : P2S1.TCar,
        Relation.TransGen (P2S5.causalDep P2S1.attendsT P2S1.isTick) x x
        → ∃ z, P2S5.causalDep P2S1.attendsT P2S1.isTick z z))
    (h4 : b4 = true ↔ Relation.TransGen (P2S5.causalDep P2S5.attendsF P2S5.compF) P2S5.om P2S5.om)
    (h5 : b5 = true ↔ (∃ x : P2S1.TCar, P2S5.causalDep P2S1.attendsT P2S1.isTick x x)) :
    P2S5.verdict b1 b2 b3 b4 b5 = P2S5.Outcome.acyclic := by
  have j := P2S5.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = false := by
    cases b5 with
    | false => rfl
    | true => exact absurd (h5.mp rfl) j.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.6. The four propositional flags of `P2S6.verdict`, tied. The meta-flags `carrierDecided` and
`carrierWoven` have NO propositional content (finding C3-S1 / PR2-S2): they remain literal `false`
arguments here, DISCLOSED as the Relabeled residue of the finding. -/
theorem pr2s2_s6_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 : Bool)
    (h1 : b1 = true ↔ AttentionDistinguishes
        (rankLift (outDest hinf P2S1.attendsT) P2S1.rankT) P2S1.kC P2S1.kA)
    (h2 : b2 = true ↔ (∀ ord : P2S1.TCar → ℕ, ord P2S1.kA ≠ ord P2S1.kB →
        ¬ Recoverable (rankLift (outDest hinf P2S1.attendsT) ord)))
    (h3 : b3 = true ↔ Recoverable (P2S6.mergeLift hinf))
    (h4 : b4 = true ↔ ¬ Recoverable (P2S6.cutLift hinf)) :
    P2S6.verdict b1 b2 b3 b4 false false = P2S6.Outcome.shapeDrawn := by
  have j := P2S6.ws5_flags_justified hinf
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2
  subst e1; subst e2; subst e3; subst e4; rfl

/-- Series 2.7. The flags of `P2S7.verdict`, tied — the FALSE flags (`inSightConserved`,
`conservedReachable`) refuted from `ws3_not_conserved` rather than assumed. The meta-flag `globalForced`
has no propositional content and remains a literal `false`, disclosed. -/
theorem pr2s2_s7_verdict_tied (hinf : ℵ₀ ≤ κ) (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ (P2S7.rankM P2S7.e1 ≠ P2S7.rankM P2S7.e0
        ∧ AttentionDistinguishes (P2S7.destML hinf) P2S7.e1 P2S7.e0))
    (h2 : b2 = true ↔ (∀ x y : P2S7.MCar,
        (∃ R, IsBisim (plainOf (P2S7.destML hinf)) R ∧ R x y) → P2S7.rankM x = P2S7.rankM y))
    (h3 : b3 = true ↔ (∀ x y : P2S7.MCar, P2S7.rankM x ≠ P2S7.rankM y →
        AttentionDistinguishes (P2S7.destML hinf) x y))
    (h4 : b4 = true ↔ (∀ insp : Hold (outDest hinf P2S7.attendsM) →
        HoldPred (outDest hinf P2S7.attendsM), ¬ ResidueRecoverable insp))
    (h5 : b5 = true ↔ (∃ f : P2S7.MCar → ℕ,
        (∀ x y : P2S7.MCar, (∃ R, IsBisim (plainOf (P2S7.destML hinf)) R ∧ R x y) → f x = f y)
        ∧ f P2S7.e1 ≠ f P2S7.e0)) :
    P2S7.verdict b1 b2 b3 b4 b5 false = P2S7.Outcome.monotoneOnly := by
  have jns := P2S7.ws3_not_conserved hinf
  have e1 : b1 = true := h1.mpr ⟨(P2S7.ws1_rank_nontrivial hinf).1, (P2S7.ws1_rank_nontrivial hinf).2.1⟩
  have e2 : b2 = false := by
    cases b2 with
    | false => rfl
    | true =>
        have hinv := h2.mp rfl
        exact absurd (hinv P2S7.e1 P2S7.e0 jns.1.1) jns.1.2
  have e3 : b3 = true := h3.mpr (P2S7.ws3_change_is_source hinf).1
  have e4 : b4 = true := h4.mpr (P2S7.ws4_rise_is_internal hinf).1
  have e5 : b5 = false := by
    cases b5 with
    | false => rfl
    | true =>
        obtain ⟨f, hf, hfne⟩ := h5.mp rfl
        exact absurd (jns.2 f hf) hfne
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.8. The flags of `P2S8.verdict`, tied. -/
theorem pr2s2_s8_verdict_tied (b1 b2 b3 b4 b5 b6 : Bool)
    (h1 : b1 = true ↔ P2S8.valu P2S8.attTri P2S8.p1 ≠ P2S8.valu P2S8.attTri P2S8.p2)
    (h2 : b2 = true ↔ (∀ (att : P2S8.S → Finset P2S8.S) (x y : P2S8.S) (v : ℤ),
        P2S8.recon att y x (P2S8.recon att x y v) = v))
    (h3 : b3 = true ↔ (∀ att : P2S8.S → Finset P2S8.S, ∀ x y : P2S8.S,
        P2S8.incr att x y + P2S8.incr att y x = 0))
    (h4 : b4 = true ↔ (∀ (att : P2S8.S → Finset P2S8.S),
        (∀ x y : P2S8.S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : P2S8.S, P2S8.hol att x y z = 0))
    (h5 : b5 = true ↔ (P2S8.hol P2S8.attTri P2S8.p0 P2S8.p1 P2S8.p2 = 3
        ∧ ¬ ∃ s : P2S8.S → ℤ, P2S8.IsSection P2S8.attTri s))
    (h6 : b6 = true ↔ (∃ s : P2S8.S → ℤ, P2S8.IsSection P2S8.attStar s)) :
    P2S8.verdict b1 b2 b3 b4 b5 b6 = P2S8.Outcome.frustrated := by
  have j := P2S8.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.2.1
  have e6 : b6 = true := h6.mpr j.2.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; rfl

/-- Series 2.9. The flags of `P2S9.verdict`, tied. -/
theorem pr2s2_s9_verdict_tied (b1 b2 b3 b4 b5 b6 : Bool)
    (h1 : b1 = true ↔ (∀ (att : P2S9.S → Finset P2S9.S) (x y : P2S9.S),
        y ∈ att x → P2S9.dist x y ≤ P2S9.rate att))
    (h2 : b2 = true ↔ (∀ att : P2S9.S → Finset P2S9.S,
        P2S9.rate att = Finset.univ.sup (fun x => (att x).sup (fun y => P2S9.dist x y))))
    (h3 : b3 = true ↔ P2S9.p4 ∉ P2S9.ball P2S9.attSlow P2S9.p0 1)
    (h4 : b4 = true ↔ ((∀ x y, P2S9.reaches P2S9.attSlow x y = P2S9.reaches P2S9.attFast x y)
        ∧ P2S9.ball P2S9.attSlow P2S9.p0 1 ≠ P2S9.ball P2S9.attFast P2S9.p0 1))
    (h5 : b5 = true ↔ (∃ y, y ∉ P2S9.ball P2S9.attSlow P2S9.p0 1))
    (h6 : b6 = true ↔ (∀ y, y ∈ P2S9.ball P2S9.attAll P2S9.p0 1)) :
    P2S9.verdict b1 b2 b3 b4 b5 b6 = P2S9.Outcome.coneOut := by
  have j := P2S9.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.2.1
  have e6 : b6 = true := h6.mpr j.2.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; rfl

/-- Series 2.10. The flags of `P2S10.verdict`, tied — the FALSE `builtHasCore` flag refuted by the
exhaustive `ws4_no_core_built` rather than assumed. -/
theorem pr2s2_s10_verdict_tied (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ (P2S10.tick P2S7.e0 ≠ P2S7.e0
        ∧ P2S10.mu (P2S10.tick P2S7.e0) = P2S10.mu P2S7.e0 + 1))
    (h2 : b2 = true ↔ (¬ Function.Injective P2S10.tick
        ∧ P2S10.mu (P2S10.tick P2S7.e0) = P2S10.mu P2S7.e0 + 1))
    (h3 : b3 = true ↔ (P2S7.attendsM (P2S7.reifyM {P2S7.e0}) = {P2S7.e0}
        ∧ P2S10.mu (P2S7.reifyM {P2S7.e0}) ≠ P2S10.mu P2S7.e0))
    (h4 : b4 = true ↔ (∃ D : Finset P2S10.Cfg, D.Nonempty ∧ P2S10.IsCore P2S10.tick P2S10.mu D))
    (h5 : b5 = true ↔ (∃ D : Finset P2S10.Cfg, D.Nonempty ∧ P2S10.IsCore P2S10.tickR P2S10.mu D)) :
    P2S10.verdict b1 b2 b3 b4 b5 = P2S10.Outcome.noCore := by
  have j := P2S10.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = false := by
    cases b4 with
    | false => rfl
    | true =>
        obtain ⟨D, hD, hcore⟩ := h4.mp rfl
        exact absurd hcore (j.2.2.2.1 D hD)
  have e5 : b5 = true := h5.mpr j.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.11. The flags of `P2S11.verdict`, tied. -/
theorem pr2s2_s11_verdict_tied (b1 b2 b3 b4 b5 b6 : Bool)
    (h1 : b1 = true ↔ (P2S11.loopAmp P2S8.attTri = -1 ∧ P2S11.loopAmp P2S8.attStar = 1))
    (h2 : b2 = true ↔ P2S11.directAmp + P2S11.loopAmp P2S8.attTri = 0)
    (h3 : b3 = true ↔ (∀ att : P2S8.S → Finset P2S8.S,
        P2S11.loopAmp att = P2S11.amp (P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2)))
    (h4 : b4 = true ↔ P2S11.combinedWeight P2S8.attTri < P2S11.partsWeight P2S8.attTri)
    (h5 : b5 = true ↔ P2S11.combinedWeight P2S8.attTri < P2S11.partsWeight P2S8.attTri)
    (h6 : b6 = true ↔ P2S11.partsWeight P2S8.attStar ≤ P2S11.combinedWeight P2S8.attStar) :
    P2S11.verdict b1 b2 b3 b4 b5 b6 = P2S11.Outcome.interfering := by
  have j := P2S11.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.1
  have e6 : b6 = true := h6.mpr j.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; rfl

/-- Series 2.12. The flags of `P2S12.verdict`, tied. -/
theorem pr2s2_s12_verdict_tied (b1 b2 b3 b4 b5 : Bool)
    (h1 : b1 = true ↔ P2S11.combinedWeight P2S8.attTri ≠ P2S11.combinedWeight P2S8.attStar)
    (h2 : b2 = true ↔ (∀ att : P2S8.S → Finset P2S8.S, 0 ≤ P2S11.combinedWeight att))
    (h3 : b3 = true ↔ P2S11.combinedWeight P2S8.attTri < P2S11.partsWeight P2S8.attTri)
    (h4 : b4 = true ↔ P2S12.respectsCancel P2S11.combinedWeight)
    (h5 : b5 = true ↔ ¬ P2S12.respectsCancel P2S11.partsWeight) :
    P2S12.verdict b1 b2 b3 b4 b5 = P2S12.Outcome.squared := by
  have j := P2S12.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.2
  subst e1; subst e2; subst e3; subst e4; subst e5; rfl

/-- Series 2.13. The flags of `P2S13.verdict`, tied — the FALSE `couplingPresent` flag refuted by
`ws3_grain_test` rather than assumed. -/
theorem pr2s2_s13_verdict_tied (b1 b2 b3 b4 b5 b6 : Bool)
    (h1 : b1 = true ↔ (∃ x y : P2S13.S, P2S13.grainBump x ≠ P2S13.grainBump y))
    (h2 : b2 = true ↔ (∃ x y x' y' : P2S13.S,
        P2S13.pathDist P2S13.aChain x y ≠ P2S13.pathDist P2S13.aChain x' y'))
    (h3 : b3 = true ↔ (∀ c1 c2 : P2S13.Config, c1.1 = c2.1 →
        ∀ x y, P2S13.adjDist c1 x y = P2S13.adjDist c2 x y))
    (h4 : b4 = true ↔ (∀ c x y, P2S13.adjDist c x y = P2S13.pathDist c.1 x y))
    (h5 : b5 = true ↔ P2S13.grainDependent P2S13.foilDist P2S13.cfgFlat P2S13.cfgBump)
    (h6 : b6 = true ↔ P2S13.grainDependent P2S13.adjDist P2S13.cfgFlat P2S13.cfgBump) :
    P2S13.verdict b1 b2 b3 b4 b5 b6 = P2S13.Outcome.inert := by
  have j := P2S13.ws5_flags_justified
  have e1 : b1 = true := h1.mpr j.1
  have e2 : b2 = true := h2.mpr j.2.1
  have e3 : b3 = true := h3.mpr j.2.2.1
  have e4 : b4 = true := h4.mpr j.2.2.2.1
  have e5 : b5 = true := h5.mpr j.2.2.2.2.1
  have e6 : b6 = false := by
    cases b6 with
    | false => rfl
    | true => exact absurd (h6.mp rfl) (P2S13.ws3_grain_test P2S13.cfgFlat P2S13.cfgBump rfl)
  subst e1; subst e2; subst e3; subst e4; subst e5; subst e6; rfl

end PR2R1
