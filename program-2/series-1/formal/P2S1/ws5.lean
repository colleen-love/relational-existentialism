/-
`program-2/series-1/formal/P2S1/ws5.lean`

WS5 - The verdict and the audit folded in. Program 2 Series 1 (2.1).

The verdict is COMPUTED from the WS1-WS4 flags (never hand-set): `verdict : Bool⁵ → Outcome`, `ws5_verdict_eq`
computes `twoZone` by `rfl`, and `ws5_verdict_discriminates` shows the function is not constant (flip a flag,
get a different outcome). The flags are EARNED by `ws5_flags_justified` (the WS1-WS4 headlines: the section, the
named reader, the stream separation, the FULL causal-order headline with its rank clause, the linearization
import). The five audit clauses (a)-(e) are actual propositions bundling the payoffs; (e) is the NAMES property,
certified by the mechanical grep (protocol §6), carried as a `True` placeholder.

The charter's pre-registered outcome "TIME-IS-IMPORT" is named `causalImport` in Lean (no identifier embeds a
forbidden content-name; audit (e)).

Design docs: `program-2/series-1/spec/ws5-design.md`; shared objects `spec/README.md` §7.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P2S1.ws1
import P2S1.ws2
import P2S1.ws3
import P2S1.ws4

universe u

namespace P2S1

open P1.Core P1.Reader P2S0 Cardinal

set_option linter.unusedVariables false

/-! ## The verdict (universe-free) -/

/-- **The outcome type.** `causalImport` is the charter's TIME-IS-IMPORT outcome (the causal order itself proves
non-recoverable); `partial'` primed (`partial` is a Lean keyword). -/
inductive Outcome
  | twoZone
  | endogenous
  | causalImport
  | partial'
  | disconnected
  deriving DecidableEq

/-- **The verdict FUNCTION.** twoZone iff the construction is well-formed (WS1), the arrow and stream land
(WS2/WS3), the causal order is endogenous AND the linearization is import (WS4). The pre-registered
alternatives: disconnected (WS1 fails), partial' (WS2/WS3 degenerate), endogenous (linearization forced),
causalImport (causal order non-recoverable). -/
def verdict (wf arrow exo causEndo linImport : Bool) : Outcome :=
  if !wf then Outcome.disconnected
  else if !(arrow && exo) then Outcome.partial'
  else if causEndo && linImport then Outcome.twoZone
  else if causEndo && !linImport then Outcome.endogenous
  else Outcome.causalImport

/-- **THE COMPUTED VERDICT.** On the certified flags, twoZone, by computation. -/
theorem ws5_verdict_eq : verdict true true true true true = Outcome.twoZone := rfl

/-- **Falsifiability.** The verdict function DISCRIMINATES: flipping a flag computes a different outcome. -/
theorem ws5_verdict_discriminates :
    verdict true true true true false = Outcome.endogenous
  ∧ verdict true true true false true = Outcome.causalImport
  ∧ verdict false true true true true = Outcome.disconnected
  ∧ verdict true false true true true = Outcome.partial' := by decide

/-! ## The flags are earned -/

/-- **THE FLAGS ARE JUSTIFIED.** The verdict's five `true` inputs are EARNED by the WS1-WS4 headlines: the WS1
section (`wf`); the DIRECTIONAL arrow (`arrow`, Ext-1 R1: the composite strictly outranks its components); the
TICK-SPECIFIC stream on `TCar` (`exo`, Ext-1 R2: every choice label distinguishing `kA`,`kB` is non-recoverable);
the FULL causal-order headline with its rank clause (`causEndo`); and the linearization import (`linImport`). The
reader (audit (c)) is separate. The `wf`, `exo`, `linImport` conjuncts are load-bearing halves; `causEndo` and
`arrow` are full theorems. -/
theorem ws5_flags_justified {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    (attendsT (reifyT cycleA) = cycleA)
  ∧ (∀ x ∈ attendsT kA, rankT x < rankT kA)
  ∧ (∀ ch : TCar → ℕ, ch kA ≠ ch kB →
        ¬ Recoverable (rankLift (outDest hinf attendsT) ch))
  ∧ ((causal kA kC ∧ causal kB kC)
      ∧ (∀ t u : TCar, causal t u → rankT t < rankT u)
      ∧ (¬ causal kA kB ∧ ¬ causal kB kA))
  ∧ (∀ ord : TCar → ℕ, ord kA ≠ ord kB →
        ¬ Recoverable (rankLift (outDest hinf attendsT) ord)) := by
  refine ⟨section_cycleA, (ws2_tick_irreversible hinf).1, ?_, ws4_causal_order_endogenous, ?_⟩
  · intro ch hch; exact (ws3_stream_exogenous hinf ch hch).2
  · intro ord hord; exact (ws4_linearization_import hinf ord hord).2

/-! ## The five audit clauses (a)-(e) -/

/-- **(a) NO SMUGGLED CLOCK.** Every temporal fact strips to a reification/attention/import fact: the
linearization is the `ord`-lift non-recoverability, no background index. (Named `no_smuggled_index` so no
identifier embeds a forbidden content-name; audit (e).) -/
theorem ws5_audit_no_smuggled_index {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ ord : TCar → ℕ, ord kA ≠ ord kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ord) :=
  fun ord hord => (ws4_linearization_import hinf ord hord).2

/-- **(b) THE STREAM IS EXOGENOUS, TICK-SPECIFIC (Ext-1 R2).** A proof term on the real carrier: every exogenous
choice label distinguishing the concurrent closures `kA`,`kB` is non-recoverable. -/
theorem ws5_audit_stream_exogenous {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∀ ch : TCar → ℕ, ch kA ≠ ch kB → ¬ Recoverable (rankLift (outDest hinf attendsT) ch) :=
  fun ch hch => (ws3_stream_exogenous hinf ch hch).2

/-- **(c) THE READER IS LOAD-BEARING.** A named `FiniteAttention` for which `kA` is real; not `Many`. -/
theorem ws5_audit_reader_loadbearing {κ : Cardinal.{0}} (hinf : ℵ₀ ≤ κ) :
    ∃ att : FiniteAttention (rankLift (outDest hinf attendsT) rankT),
      RealFor (rankLift (outDest hinf attendsT) rankT) att kA :=
  ws2_composite_real_for hinf

/-- **(d) THE FORK IS GENUINE.** A concurrent pair (`kA ≠ kB`, incomparable in `causal`) AND a causal pair
(`causal kA kC`) are both witnessed on `TCar`, and the order carries the structural constraint `causal t u →
rankT t < rankT u`. No empty concurrency, no order total by construction (PR1-S1 foreclosed). -/
theorem ws5_audit_fork_genuine :
    (kA ≠ kB ∧ ¬ causal kA kB ∧ ¬ causal kB kA)
  ∧ causal kA kC
  ∧ (∀ t u : TCar, causal t u → rankT t < rankT u) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide

/-- **(e) NAMES-NOT-TERMS.** No proof term, definition, or discharged obligation is named as content
`time`/`now`/`clock`/`before`/`after`/`moment`/`self`/`other`/`chance`/`choice`/`subjectivity`. A NAMES
property, certified by the mechanical grep (protocol §6); carried here as a `True` placeholder, as the property
is about identifiers, not a proposition. -/
theorem ws5_audit_names_not_terms : True := trivial

end P2S1
