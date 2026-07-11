/-
`series-07/formal/Series07/ws5.lean`

WS5 — **The limit-atomlessness loophole.** Series 07.

Owns the ONE real escape: relaxing ingredient (3) from every-moment to limit atomlessness, with
transient atoms at the finite stages. Proved a genuine relaxation (not a counterexample): any two
distinct processes are distinguished by a finite-stage leaf. Adjudicated by the pre-registered
fork, designed toward `importInTime`.

Design doc: `series-07/spec/ws5-design.md`.

REVIEW RESPONSE (project-review-1.md R4/R5, recorded in `charter-status.md`). Pass 1 was right on
two points, both fixed here as scope/framing (no signature retargeted):
* R4 — the loophole is CHARACTERIZED (D1, `ws5_limit_reintroduces_leaves`, genuine) but never
  INSTANTIATED as a convergent leafy family. `ws5_leafy_pair` is honestly relabelled: it is Ω
  versus a PERMANENT atom (`emptyProc`, proved non-productive in WS1), a leafy pair — NOT a
  limit-atomless thread. The convergent `CauchySeq` family (metric `bdist`/`Tendsto`) is not
  built; stated Partial, build-owed.
* R5 — the adjudication is a RULING, not a forced theorem. `ws5_adjudication_justified` is the
  horn-neutral D1 (equally consistent with `.genuineEscape`); the "Import Theorem stands
  unqualified" reading is the designed-toward interpretation, not a consequence. Prose corrected.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series07.ws4

universe u

namespace Series07.WS5

open Series07.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## The loophole is a relaxation, not a counterexample -/

/-- **D1 — limit-atomlessness reintroduces leaves (genuine).** Any two DISTINCT processes differ
at a finite stage, and that stage necessarily carries a leaf in at least one — because an
every-moment-atomless stage is UNIQUE (`allNonempty_unique`). So limit-atomlessness relaxes (3);
it never contradicts the every-moment theorem. -/
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

/-- **D2 (honest core, relabelled per R4).** A leafy PAIR exists: Ω and the atom process. The
atom (`emptyProc`) is a PERMANENT atom (non-productive, WS1's `empty_not_productive`), NOT a
limit-atomless thread — so this witnesses that leafy threads are plural, but it is NOT the
convergent transient-atoms-healing-in-the-limit family (which is build-owed, Partial). -/
theorem ws5_leafy_pair (hinf : ℵ₀ ≤ κ) :
    ∃ x y : Proc κ, x ≠ y
      ∧ (∃ n, ¬ allNonempty κ n (y.1 n))    -- y is leafy
      ∧ ¬ Productive y :=                    -- and y is a PERMANENT atom, not limit-atomless
  ⟨omegaProc hinf, emptyProc hinf, omega_ne_empty hinf, ⟨1, empty_leafy hinf⟩,
   empty_not_productive hinf⟩

/-! ## The adjudication (the pre-registered fork) -/

inductive LoopholeVerdict
  | genuineEscape
  | importInTime
  deriving DecidableEq

/-- **D3 — the adjudication (a RULING, not a forced theorem, per R5).** Designed toward
`importInTime`: the distinguisher between any two limit-atomless processes is provably a
finite-stage atom (D1), which the ruling reads as an atom paid in installments. The horn-neutral
theorem D1 does NOT force this reading; `genuineEscape` (limit-as-object ⇒ headline weakens to
"impossible except in the limit") is retained as the terminal alternative. -/
def ws5_loophole_adjudication : LoopholeVerdict := .importInTime

/-- The ruling's justification is the horn-neutral D1 — equally consistent with `.genuineEscape`.
It does not force `.importInTime`; the constructor choice is a ruling on the theorem, not a
consequence of it. -/
theorem ws5_adjudication_justified (hinf : ℵ₀ ≤ κ) (x y : Proc κ) (hxy : x ≠ y) :
    ∃ n, (¬ allNonempty κ n (x.1 n)) ∨ (¬ allNonempty κ n (y.1 n)) :=
  ws5_limit_reintroduces_leaves hinf x y hxy

/-- The fork is genuine: both constructors are distinct and terminal. `.importInTime` is the
designed-toward ruling, NOT forced by any theorem. -/
theorem ws5_fork_is_genuine :
    ws5_loophole_adjudication = LoopholeVerdict.importInTime
  ∧ (LoopholeVerdict.genuineEscape ≠ LoopholeVerdict.importInTime) :=
  ⟨rfl, by decide⟩

end Series07.WS5
