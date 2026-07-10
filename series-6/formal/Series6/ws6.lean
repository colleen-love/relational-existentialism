/-
`series-6/formal/ws6.lean`

WS6 — **Globally atomless and plural, and the one-engine unification.** Series 6, headline.

BUILD FINDING (routed to WS6/WS1 designs, recorded in `charter-status.md`). The headline
achievement — genuinely globally atomless AND plural — is **NOT** deliverable on C2, and the
reason is a theorem: `ws6_atomless_and_plural_impossible` (= WS1's `ws1_no_productive_plurality`).
On the finite founded-approximation carrier Ω is the unique productive (hereditarily nonempty)
thread, so there is no productive plurality. The plurality that DOES exist among processes
(Ω vs the atom) is bought by an atom (the empty successor), exactly the Static Collapse (WS2)
diagnosis reappearing at the process level. So the genuine achievement is obstructed and owed
to the richer carrier home (metric C4 / guarded).

What IS delivered (Discharged), independent of productive plurality:
* the inherited incompleteness re-read as the engine (`ws6_incompleteness_inherited`);
* groundlessness from the diagonal — no completion, so the survey always misses a residue
  (`ws6_groundlessness_from_diagonal`);
* no view from nowhere — every vantage misses the residue, the past-map is a function and the
  future-map one-to-many (`ws6_no_view_from_nowhere`).
The one-engine unification is therefore a conjunction obstructed by the collapse, not the
same-mechanism reduction (`ws6_one_engine_obstructed`): verdict pressure toward
`payoffsEstablished`, per the program's pattern.

Sorry-free; axiom-clean beyond Mathlib's standard three.
-/
import Series6.ws5

universe u

namespace Series6.WS6

open Series6.WS1 Series6.WS3 Series6.WS4 Cardinal

variable {κ : Cardinal.{u}}

/-! ## Inherited incompleteness, re-read as the engine -/

/-- **`ws6_incompleteness_inherited`.** The two carrier-independent incompletenesses,
transported: (a) the self-survey is non-surjective at every moment (Cantor/Lawvere), which is
`residue`'s source; (b) Ω is complete-in-extent yet closed at no depth (productive, a nonempty
successor at every stage). -/
theorem ws6_incompleteness_inherited (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, ¬ Function.Surjective (survey m))
  ∧ (Productive (omegaProc hinf)
      ∧ ∀ n, (omegaApprox hinf (n+1) : Approx κ (n+1)).1.Nonempty) :=
  ⟨ws3_incompleteness, ws1_omega_process hinf, ws1_omega_nonclosing hinf⟩

/-! ## Groundlessness from the diagonal (no completion ⇒ no atom) -/

/-- **`ws6_groundlessness_from_diagonal`.** No self-survey completes: the residue (the Cantor
diagonal) is never in the survey's image, so there is always an un-surveyed part — a bud not
closed, hence no atom. The specific missed element is the residue; strip `survey`/`diagPred`
and the statement is contentless. -/
theorem ws6_groundlessness_from_diagonal (m : Moment κ) :
    diagPred (survey m) ∉ Set.range (survey m) :=
  diag_not_mem_range (survey m)

/-! ## No view from nowhere (inhabited, not surveyed) -/

/-- **`ws6_no_view_from_nowhere`.** (i) No completed vantage: every depth-`m` survey is
non-surjective, missing the residue (the engine, not mere limit-refusal). (ii) The past-map
(`trunc`) is a total function while the future-map (residue-opening) is one-to-many (`≥ 2`
continuations over one past). The inhabited/surveyed asymmetry is load-bearing: strip the
residue and (i) loses its proof. -/
theorem ws6_no_view_from_nowhere (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, ¬ Function.Surjective (survey m))
  ∧ (∀ n, ∃ x : Approx κ n, 2 ≤ Cardinal.mk {s : Approx κ (n+1) // trunc κ n s = x}) :=
  ⟨ws3_incompleteness, ws4_residue_one_to_many hinf⟩

/-! ## THE ACHIEVEMENT — obstructed (Impossibility on C2) -/

/-- **`ws6_atomless_and_plural_impossible` — the headline finding (Impossibility).** There is
NO productive plurality on `Proc`: Ω is the unique hereditarily-nonempty thread, so genuinely
atomless plurality cannot be exhibited on C2. The escape is owed to the richer carrier home. -/
theorem ws6_atomless_and_plural_impossible (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ x y : Proc κ, Productive x ∧ Productive y ∧ x ≠ y := by
  rintro ⟨x, y, hx, hy, hne⟩
  exact ws1_no_productive_plurality hinf ⟨x, y, hne, hx, hy⟩

/-- **The plurality that exists is bought by an atom.** There ARE two distinct processes
(Ω and the atom), but one of them (the empty process) relates to nothing — it is an atom. So
process-plurality on C2 costs an atom, exactly the Static Collapse (WS2) diagnosis at the
process level: no genuinely-atomless plurality. -/
theorem ws6_plurality_costs_an_atom (hinf : ℵ₀ ≤ κ) :
    (∃ x y : Proc κ, x ≠ y)
  ∧ ¬ Productive (Series6.WS5.emptyProc hinf) := by
  refine ⟨Series6.WS5.ws5_processes_plural hinf, ?_⟩
  intro hprod
  exact (ws6_atomless_and_plural_impossible hinf)
    ⟨omegaProc hinf, Series6.WS5.emptyProc hinf, ws1_omega_process hinf, hprod,
     Series6.WS5.omega_ne_empty hinf⟩

/-! ## The one-engine unification — obstructed (conjunction, not reduction) -/

/-- **`ws6_one_engine_obstructed`.** Groundlessness from the diagonal holds
(`ws6_groundlessness_from_diagonal`) and processes are plural
(`ws5_processes_plural`) — but the two are NOT the same productive-atomless mechanism, because
that mechanism (`ws6_atomless_and_plural`) is impossible on C2. So the unification is a
conjunction obstructed by the collapse, not the same-residue reduction. Verdict pressure toward
`payoffsEstablished`. -/
theorem ws6_one_engine_obstructed (hinf : ℵ₀ ≤ κ) :
    (∀ m : Moment κ, diagPred (survey m) ∉ Set.range (survey m))   -- groundlessness (diagonal)
  ∧ (∃ x y : Proc κ, x ≠ y)                                        -- plurality (of processes)
  ∧ (¬ ∃ x y : Proc κ, Productive x ∧ Productive y ∧ x ≠ y) :=     -- but NOT both at once (collapse)
  ⟨fun m => ws6_groundlessness_from_diagonal m,
   Series6.WS5.ws5_processes_plural hinf,
   ws6_atomless_and_plural_impossible hinf⟩

end Series6.WS6
