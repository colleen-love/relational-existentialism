/-
`series-06/formal/ws5.lean`

WS5 — **One arrow or many: the relativity crux.** Series 06.

Consumes `prec` (WS3/WS4). Delivers the totality question for `≺` and the endogenous
two-sided face `faceAt`. The genuine, clean core: **agreement is the collapse** — a single
agreeing knower is the subsingleton (`ws5_agreement_is_collapse`), so plurality forbids
agreement (`ws5_plurality_forbids_agreement`).

BUILD FINDING (routed to WS5 design, recorded in `charter-status.md`). Two pre-registered
honest outcomes fire:
* **Relativity laundered.** `≺` is a strict order and `¬ Total` holds — but the incomparable
  witnesses are two distinct *same-depth* moments, and their incomparability follows from bare
  depth-posethood (`prec` strictly increases depth), with NO use of the `faceAt` mismatch. So
  the strip of "face" survives: this is posethood relabelled, not earned relativity
  (`ws5_incomparability_is_bare_poset`). Reported Partial — laundered.
* **Ω is not an absolute frame.** A global survey forces collapse (Newton = the subsingleton),
  and Ω is not a global survey, so Newton does not return via Ω (`ws5_omega_absolute_frame`).
The genuine relativity (incomparability earned from mismatched two-sided faces on a productive
plurality) is obstructed because productive plurality fails on C2 (WS1); it is owed to the
richer home. The Lorentzian ceiling stays unbuilt (flagged heuristic, charter §5.4).

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series06.ws4

universe u

namespace Series06.WS5

open Series06.WS1 Series06.WS3 Series06.WS4 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The endogenous two-sided face, and agreement -/

/-- The **endogenous two-sided face**: the part of `a`'s stage-`n` state engaged in surveying
`b`. Read off the survey structure (which coarsens to the state), so `faceAt a b n` is `a`'s
own stage-`n` state — internal, no imported label. -/
def faceAt (a _b : Proc κ) (n : ℕ) : Approx κ n := a.1 n

/-- **Cross-survey agreement** at a pair, read off the two-sided face. -/
def Agree (a b : Proc κ) : Prop := ∀ n, faceAt a b n = faceAt b a n

/-- Totality of `≺` (global time). -/
def Total (hinf : ℵ₀ ≤ κ) : Prop :=
  ∀ m m' : Moment κ, prec hinf m m' ∨ prec hinf m' m ∨ m = m'

/-- Agreement is exactly identity: the two-sided faces coincide iff the threads are equal. -/
theorem ws5_agree_iff_eq (a b : Proc κ) : Agree a b ↔ a = b := Iff.symm (proc_ext a b)

/-! ## Agreement is the collapse -/

/-- **`ws5_agreement_is_collapse` — totality-forcing agreement everywhere IS the subsingleton
collapse.** A single agreeing self-knower is the §3 collapsed point. This is the honest
content of "totality ⟺ agreement": universal agreement identifies all threads. -/
theorem ws5_agreement_is_collapse : (∀ a b : Proc κ, Agree a b) ↔ Subsingleton (Proc κ) := by
  constructor
  · intro h; exact ⟨fun a b => (ws5_agree_iff_eq a b).mp (h a b)⟩
  · intro h a b; exact (ws5_agree_iff_eq a b).mpr (Subsingleton.elim a b)

/-- **`ws5_plurality_forbids_agreement`.** Any two distinct threads disagree — plurality
forbids agreement. (Holds for the genuine plurality of *processes*; the *productive* plurality
the achievement needs fails on C2, WS1.) -/
theorem ws5_plurality_forbids_agreement (hne : ∃ a b : Proc κ, a ≠ b) :
    ∃ a b : Proc κ, ¬ Agree a b := by
  obtain ⟨a, b, hab⟩ := hne
  exact ⟨a, b, fun h => hab ((ws5_agree_iff_eq a b).mp h)⟩

/-! ## The processes ARE plural (as processes) — omega vs the atom -/

/-- The atom process: relates to nothing (the empty successor at every stage). -/
noncomputable def emptyApprox (hinf : ℵ₀ ≤ κ) : (n : ℕ) → Approx κ n
  | 0     => PUnit.unit
  | (n+1) => toPk hinf (∅ : Set (Approx κ n))

theorem empty_compat (hinf : ℵ₀ ≤ κ) :
    ∀ n, trunc κ n (emptyApprox hinf (n+1)) = emptyApprox hinf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n _ =>
      show PkMap κ (trunc κ n) (emptyApprox hinf (n+2)) = emptyApprox hinf (n+1)
      apply Subtype.ext
      show (trunc κ n) '' (∅ : Set (Approx κ (n+1))) = (∅ : Set (Approx κ n))
      rw [Set.image_empty]

noncomputable def emptyProc (hinf : ℵ₀ ≤ κ) : Proc κ :=
  ⟨emptyApprox hinf, empty_compat hinf⟩

theorem omega_ne_empty (hinf : ℵ₀ ≤ κ) : omegaProc hinf ≠ emptyProc hinf := by
  apply ws1_no_collapse (omegaProc hinf) (emptyProc hinf) 1
  intro h
  change omegaApprox hinf 1 = emptyApprox hinf 1 at h
  have hv := congrArg Subtype.val h
  rw [omegaApprox_succ] at hv
  simp only [emptyApprox, toPk_val] at hv
  exact (Set.singleton_ne_empty (omegaApprox hinf 0)) hv

/-- The world has genuinely more than one process (Ω and the atom). -/
theorem ws5_processes_plural (hinf : ℵ₀ ≤ κ) : ∃ a b : Proc κ, a ≠ b :=
  ⟨omegaProc hinf, emptyProc hinf, omega_ne_empty hinf⟩

/-! ## `≺` is a strict order; but `¬ Total` LAUNDERS -/

/-- **`ws5_precedes_order`** (cited from WS4). -/
theorem ws5_precedes_order (hinf : ℵ₀ ≤ κ) :
    Irreflexive (prec hinf) ∧ Transitive (prec (κ := κ) hinf) := ws4_arrow_strict hinf

/-- Distinct same-depth moments are `≺`-incomparable — purely from depth-posethood. -/
theorem ws5_incomparable_same_depth (hinf : ℵ₀ ≤ κ) {m m' : Moment κ}
    (hd : m.1 = m'.1) : ¬ prec hinf m m' ∧ ¬ prec hinf m' m := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlt := prec_depth_lt hinf h; rw [hd] at hlt; exact Nat.lt_irrefl _ hlt
  · have hlt := prec_depth_lt hinf h; rw [hd] at hlt; exact Nat.lt_irrefl _ hlt

lemma moment_snd_eq {n : ℕ} {s t : Approx κ n}
    (he : (⟨n, s⟩ : Moment κ) = ⟨n, t⟩) : s = t := by
  rw [Sigma.ext_iff] at he; exact eq_of_heq he.2

/-- **`ws5_incomparability_is_bare_poset` — the LAUNDERING finding (SERIOUS, honest).** There
are `≺`-incomparable moments, but the witnesses are two distinct *same-depth* moments and the
incomparability is proved with NO appeal to `faceAt`/`Agree` — it is bare depth-posethood.
Strip "face" and the incomparability survives. So the causal order LAUNDERS on C2. -/
theorem ws5_incomparability_is_bare_poset (hinf : ℵ₀ ≤ κ) :
    ∃ m m' : Moment κ, m ≠ m' ∧ ¬ prec hinf m m' ∧ ¬ prec hinf m' m := by
  refine ⟨⟨1, toPk hinf (∅ : Set (Approx κ 0))⟩, ⟨1, omegaApprox hinf 1⟩, ?_, ?_⟩
  · intro he
    have hs := moment_snd_eq he
    have hv := congrArg Subtype.val hs
    rw [toPk_val, omegaApprox_succ] at hv
    exact (Set.singleton_ne_empty (omegaApprox hinf 0)) hv.symm
  · exact ws5_incomparable_same_depth hinf rfl

/-- **`ws5_causal_partial_order` (Partial — laundered).** `≺` is a strict order and NOT total,
but the incomparability is bare posethood (`ws5_incomparability_is_bare_poset`), not earned
from the two-sided face. Reported Partial. -/
theorem ws5_causal_partial_order (hinf : ℵ₀ ≤ κ) :
    (Irreflexive (prec hinf) ∧ Transitive (prec (κ := κ) hinf))
  ∧ ¬ Total hinf := by
  refine ⟨ws4_arrow_strict hinf, ?_⟩
  intro htot
  obtain ⟨m, m', hne, hnp, hnp'⟩ := ws5_incomparability_is_bare_poset hinf
  rcases htot m m' with h | h | h
  · exact hnp h
  · exact hnp' h
  · exact hne h

/-! ## The Ω-absolute-frame branch (Newton, checked) -/

/-- A shared reference surveyed identically by all relata. -/
def GlobalSurvey (g : Proc κ) : Prop := ∀ a : Proc κ, Agree a g ∧ Agree g a

/-- **`ws5_omega_absolute_frame` — Newton = collapse, and Ω is not it.** (i) A global survey
forces the subsingleton (an absolute frame that synchronizes all threads IS the collapse). (ii)
Ω is NOT a global survey, so Newton does not return via Ω — the plurality is not synchronized. -/
theorem ws5_omega_absolute_frame (hinf : ℵ₀ ≤ κ) :
    (∀ g : Proc κ, GlobalSurvey g → Subsingleton (Proc κ))
  ∧ ¬ GlobalSurvey (omegaProc hinf) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    exact ⟨fun a b => by
      rw [(ws5_agree_iff_eq a g).mp (hg a).1, (ws5_agree_iff_eq b g).mp (hg b).1]⟩
  · intro hg
    have := (ws5_agree_iff_eq (emptyProc hinf) (omegaProc hinf)).mp (hg (emptyProc hinf)).1
    exact (omega_ne_empty hinf) this.symm

end Series06.WS5
