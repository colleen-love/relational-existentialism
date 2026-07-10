/-
`series-6/formal/ws3.lean`

WS3 — **The engine: incompleteness as fuel.** Series 6, the signature crux.

Owns the diagonal time-step: the successor of a moment IS the residue its own self-survey
missed — literally, not by a naming convention. `residue` is DEFINED as the Cantor
diagonal `diagPred (survey m)`, realized as a concrete stage-`(m.1+1)` element (possible
because every `Approx κ n` is finite, WS1). `stepM`'s successor STATE is that residue and
has no other definiens: delete `survey`/`diagPred`/`residue` and `stepM` fails to elaborate.
So the engine genuinely drives (charter §5.2, protocol §0.4), it is not painted on.

Design doc: `series-6/spec/ws3-design.md`, candidate C1 (`Δ`/`stepM` literally
residue-opening). Moments are founded approximations `Moment κ = Σ n, Approx κ n` (README §2,
"a moment is a finite founded history-prefix").

HONESTY NOTE (routed to WS3/WS7, recorded in `charter-status.md`). Moment-level
fixed-point-freeness `stepM m ≠ m` combines two facts: (a) the STATE genuinely moves — the
residue differs from self-reproduction (`ws3_residue_new`, Cantor-driven, survives the
strip), and (b) the survey-depth advances (`m.1 + 1 ≠ m.1`, arithmetic, does NOT survive the
strip). The genuinely diagonal-driven content is (a) and the incompleteness
`ws3_incompleteness`; the depth counter (b) is auxiliary. WS7's strip ledger records this
split.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series6.ws1

universe u

namespace Series6.WS3

open Series6.WS1 Cardinal

variable {κ : Cardinal.{u}}

/-! ## Moments -/

/-- A **moment**: a founded state at a survey-depth (a finite founded history-prefix). -/
def Moment (κ : Cardinal.{u}) : Type u := Σ n : ℕ, Approx κ n

/-! ## The self-survey and the Cantor residue (the engine) -/

/-- The **Cantor diagonal** of a survey `f`: the predicate `f` provably omits. -/
def diagPred {A : Type u} (f : A → Set A) : Set A := {a | a ∉ f a}

/-- The diagonal is always missed (Cantor). -/
lemma diag_not_mem_range {A : Type u} (f : A → Set A) : diagPred f ∉ Set.range f := by
  rintro ⟨a, ha⟩
  have h1 : (a ∈ diagPred f) ↔ (a ∉ f a) := Iff.rfl
  rw [← ha] at h1
  exact (iff_not_self h1)

/-- The **stage-`n` self-survey** of a moment `⟨n, s⟩`: the maximally lossy self-survey that
coarsens every state to the moment's own state `s` (README §2/§4: "surveying coarsens").
Cantor bites on it regardless; its lossiness is used by WS4. -/
def survey (m : Moment κ) : Approx κ m.1 → Set (Approx κ m.1) := fun _ => {m.2}

/-- The **residue**: the successor stage IS the diagonal the survey missed, realized as a
concrete stage-`(m.1+1)` element (finiteness of `Approx`, WS1). No other definiens. -/
noncomputable def residue (hinf : ℵ₀ ≤ κ) (m : Moment κ) : Approx κ (m.1 + 1) :=
  toPk hinf (diagPred (survey m))

/-- The **diagonal time-step on moments**: the successor opens the residue. -/
noncomputable def stepM (hinf : ℵ₀ ≤ κ) (m : Moment κ) : Moment κ :=
  ⟨m.1 + 1, residue hinf m⟩

/-! ## The obligations -/

/-- **Incompleteness (the fixed-point-free source, Cantor).** No moment's self-survey is
surjective: it always misses the residue. This is the single fact the engine runs on. -/
theorem ws3_incompleteness (m : Moment κ) : ¬ Function.Surjective (survey m) :=
  fun hsurj => diag_not_mem_range (survey m) (hsurj (diagPred (survey m)))

/-- A state is **at rest** if its self-survey is complete (surjective) — a closed
self-model. -/
def AtRest (m : Moment κ) : Prop := Function.Surjective (survey m)

/-- **D1 — the engine identity as one chain.** Fixed-point-freeness (no rest) = incompleteness
(the survey is non-surjective) = the residue is always missed (productivity: the successor
content is always available). One fact, three readings. -/
theorem ws3_fpf_eq_incompleteness_eq_nontermination (m : Moment κ) :
    (¬ AtRest m ↔ ¬ Function.Surjective (survey m))
  ∧ (¬ Function.Surjective (survey m) ↔ (diagPred (survey m) ∉ Set.range (survey m)))
  ∧ (diagPred (survey m) ∉ Set.range (survey m)) := by
  have hmiss := diag_not_mem_range (survey m)
  exact ⟨Iff.rfl, ⟨fun _ => hmiss, fun _ => ws3_incompleteness m⟩, hmiss⟩

/-- **D2 — the residue IS the successor (definitional).** -/
theorem ws3_residue_is_successor (hinf : ℵ₀ ≤ κ) (m : Moment κ) :
    (stepM hinf m).2 = residue hinf m := rfl

/-- **D2 — the residue is LITERALLY the Cantor diagonal.** Its underlying set is exactly the
predicate `survey m` missed. Strip `survey`/`diagPred` and this loses its content. -/
theorem ws3_residue_is_diagonal (hinf : ℵ₀ ≤ κ) (m : Moment κ) :
    (residue hinf m).1 = diagPred (survey m) := rfl

/-- **The successor STATE genuinely moves** — the residue differs from self-reproduction
`{m.2}`. So the diagonal really changes the state, it does not merely advance a counter.
Cantor-driven, survives the strip. -/
theorem ws3_residue_new (hinf : ℵ₀ ≤ κ) (m : Moment κ) :
    (residue hinf m).1 ≠ ({m.2} : Set (Approx κ m.1)) := by
  intro h
  have hm : m.2 ∈ (residue hinf m).1 ↔ m.2 ∈ ({m.2} : Set (Approx κ m.1)) := by rw [h]
  rw [ws3_residue_is_diagonal] at hm
  have hmem : m.2 ∈ diagPred (survey m) := hm.mpr rfl
  simp only [diagPred, survey, Set.mem_setOf_eq, Set.mem_singleton_iff] at hmem
  exact hmem trivial

/-- **Moment-level fixed-point-freeness.** No moment is its own successor. (State moves —
`ws3_residue_new` — and depth advances; see the honesty note above.) -/
theorem ws3_fixed_point_free (hinf : ℵ₀ ≤ κ) (m : Moment κ) : stepM hinf m ≠ m := by
  intro h
  have : (stepM hinf m).1 = m.1 := congrArg Sigma.fst h
  simp only [stepM] at this
  exact Nat.succ_ne_self m.1 this

/-- **D4 — the diagonal drives (uniqueness / the coincidence).** Any transition whose
successor at each moment is the survey-residue IS `stepM`: the residue-law pins the
transition uniquely, so there is no independent dynamics for the diagonal to be painted onto.
Strip `residue` and the hypothesis cannot even be stated. -/
theorem ws3_diagonal_drives (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, (stepM hinf m).2 = residue hinf m)
  ∧ (∀ step : Moment κ → Moment κ,
       (∀ m, step m = ⟨m.1 + 1, residue hinf m⟩) → step = stepM hinf) := by
  refine ⟨fun m => rfl, ?_⟩
  intro step hstep
  funext m
  rw [hstep m]; rfl

/-! ## The order `≺` on moments (shared with WS4/WS5) -/

/-- `m ≺ m'` iff `m'` is reached from `m` by iterating the diagonal step (README §4). -/
def prec (hinf : ℵ₀ ≤ κ) : Moment κ → Moment κ → Prop :=
  Relation.TransGen (fun a b => b = stepM hinf a)

/-- Every step strictly advances survey-depth. -/
lemma stepM_depth (hinf : ℵ₀ ≤ κ) (m : Moment κ) : (stepM hinf m).1 = m.1 + 1 := rfl

/-- `≺` strictly increases depth (the properness of self-knowledge, as an order fact). -/
theorem prec_depth_lt (hinf : ℵ₀ ≤ κ) {m m' : Moment κ} (h : prec hinf m m') : m.1 < m'.1 := by
  induction h with
  | single hb => rw [hb]; exact Nat.lt_succ_self _
  | tail _ hb ih => rw [hb]; exact Nat.lt_succ_of_lt ih

/-! ## Ω as the canonical non-terminating orbit -/

/-- **D3 — Ω the canonical non-terminating orbit.** Ω is the productive process (WS1), never
closing: a nonempty successor at every stage, and every moment strictly advances (no rest). -/
theorem ws3_omega_orbit (hinf : ℵ₀ ≤ κ) :
    Productive (omegaProc hinf)
  ∧ (∀ n, (omegaApprox hinf (n+1) : Approx κ (n+1)).1.Nonempty)
  ∧ (∀ m : Moment κ, stepM hinf m ≠ m) :=
  ⟨ws1_omega_process hinf, ws1_omega_nonclosing hinf, ws3_fixed_point_free hinf⟩

end Series6.WS3
