/-
`series-7/formal/Series7/ws5.lean`

WS5 — **The limit-atomlessness loophole.** Series 7.

Owns the ONE real escape: relaxing ingredient (3) from every-moment to limit atomlessness,
with transient atoms at the finite stages. Proved a genuine relaxation (not a counterexample):
any two distinct processes are distinguished by a finite-stage leaf. Adjudicated by the
pre-registered fork, designed toward `importInTime` (the transient leaf is a genuine atom at a
genuine finite moment, so plurality is bought with an atom, deferred not escaped).

Design doc: `series-7/spec/ws5-design.md`. The metric/`CauchySeq` packaging (the concrete
convergent family) is the pre-registered build-owed Partial; the bare existence of leafy
plurality and the leaf-forcing characterization are Discharged.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series7.ws4

universe u

namespace Series7.WS5

open Series7.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The atom process (transcribed) — a leafy thread -/

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

/-- The atom process carries a finite-stage leaf: at stage 1 its successor set is empty. -/
theorem empty_leafy (hinf : ℵ₀ ≤ κ) : ¬ allNonempty κ 1 ((emptyProc hinf).1 1) := by
  intro h
  have hne : ((emptyApprox hinf 1).1).Nonempty := h.1
  simp only [emptyApprox, toPk_val] at hne
  exact Set.not_nonempty_empty hne

theorem omega_ne_empty (hinf : ℵ₀ ≤ κ) : omegaProc hinf ≠ emptyProc hinf := by
  apply ws1_no_collapse (omegaProc hinf) (emptyProc hinf) 1
  intro h
  change omegaApprox hinf 1 = emptyApprox hinf 1 at h
  have hv := congrArg Subtype.val h
  rw [omegaApprox_succ] at hv
  simp only [emptyApprox, toPk_val] at hv
  exact (Set.singleton_ne_empty (omegaApprox hinf 0)) hv

/-! ## The loophole is a relaxation, not a counterexample -/

/-- **D1 — limit-atomlessness reintroduces leaves.** Any two DISTINCT processes differ at a
finite stage, and that stage necessarily carries a leaf in at least one — because an
every-moment-atomless stage is UNIQUE (`allNonempty_unique`). So limit-atomlessness relaxes
(3); it never contradicts the every-moment theorem. -/
theorem ws5_limit_reintroduces_leaves (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n)) := by
  have hxy' : ¬ ∀ n, x.1 n = y.1 n := fun h => hxy ((proc_ext x y).mpr h)
  push_neg at hxy'
  obtain ⟨n, hn⟩ := hxy'
  refine ⟨n, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy⟩ := hcon
  apply hn
  rw [allNonempty_unique hinf n (x.1 n) hx, allNonempty_unique hinf n (y.1 n) hy]

/-- **D2 (core) — leafy plurality exists.** Ω and the atom are distinct processes, and the
atom carries a finite-stage leaf. The distinct-leafy family converging to Ω (the metric
`CauchySeq` packaging) is the pre-registered build-owed Partial; this bare existence is the
Discharged core. -/
theorem ws5_leafy_plurality (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, x ≠ y ∧ (∃ n, ¬ allNonempty κ n (y.1 n)) :=
  ⟨omegaProc hinf, emptyProc hinf, omega_ne_empty hinf, ⟨1, empty_leafy hinf⟩⟩

/-! ## The adjudication (the pre-registered fork) -/

inductive LoopholeVerdict
  | genuineEscape
  | importInTime
  deriving DecidableEq

/-- **D3 — the adjudication.** Designed toward `importInTime`: the distinction between any two
limit-atomless processes is provably carried by a finite-stage atom (D1), so the plurality is
bought with an atom, deferred not escaped. The Import Theorem stands unqualified. -/
def ws5_loophole_adjudication : LoopholeVerdict := .importInTime

/-- The verdict's justification is horn-neutral D1: the plurality lives in the leafy finite
stages and nowhere else — never in the atomless limit, where all threads coincide with Ω. -/
theorem ws5_adjudication_justified (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n)) :=
  ws5_limit_reintroduces_leaves hinf x y hxy

/-- The fork is genuine: `genuineEscape` (limit-as-object ⇒ headline weakens to "impossible
except in the limit") is retained as the terminal alternative, `importInTime` designed toward. -/
theorem ws5_fork_is_genuine :
    ws5_loophole_adjudication = LoopholeVerdict.importInTime
  ∧ (LoopholeVerdict.genuineEscape ≠ LoopholeVerdict.importInTime) := by
  refine ⟨rfl, by decide⟩

end Series7.WS5
