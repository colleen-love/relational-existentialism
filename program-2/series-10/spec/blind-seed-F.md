# Blind seed — Phase F (code review). Series 2.10.

You are reviewing BUILT Lean 4 code against a self-contained contract. Judge whether the code PROVES the claimed signatures — not whether the interpretation is nice. You are seeded with the target signatures, success criteria, audit checks, the strip test, the forbidden-names list, and the grading rubric. Judge the code ONLY against these.

You MAY read the Lean sources under `program-2/series-10/formal/` (the aggregator `P2S10.lean`, `P2S10/ws1.lean … ws5.lean`, `P2S10/AxiomCheck.lean`). You MUST NOT read any other file (no `charter.md`, `charter-status.md`, `protocol.md`, `summary*.md`, `reversal-derisking.md`, the `wsNN-design.md` files, or `spec/README.md`) — those carry motivating prose that would break blindness. Docstring/comment prose INSIDE the `formal/` sources is part of the code you review; you may read it, but judge the THEOREMS, not the prose.

## 1. The imported facts you may assume (from the predecessor build `P2S7`, verbatim, `decide`-checkable on `Fin 4`)

`MCar = Fin 4` with states `e0, e0', e1, e2`; `rankM e0 = rankM e0' = 0`, `rankM e1 = 1`, `rankM e2 = 2`; `reifyM {e0} = e1`, `reifyM {e1} = e2`, `reifyM {e0'} = e0`, `reifyM {e2} = e0`; `attendsM (reifyM {e0}) = {e0}`; `P2S7.ws2_tick_raises : (ℵ₀ ≤ κ) → rankM (reifyM {e0}) = rankM e0 + 1 ∧ …`.

## 2. The shared objects and target theorems (in namespace `P2S10`)

```
abbrev Cfg : Type := P2S7.MCar
abbrev mu  : Cfg → ℕ := P2S7.rankM
def tick  : Cfg → Cfg := fun x => reifyM {x}
def tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x
def IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D) ∧ (D.image t = D) ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y) ∧ (∀ x ∈ D, m (t x) = m x)

theorem ws1_tick_moves : tick e0 ≠ e0 ∧ mu (tick e0) = mu e0 + 1
theorem ws2_tick_not_invertible : ¬ Function.Injective tick ∧ (∃ x, mu (tick x) ≠ mu x) ∧ mu (tick e0) = mu e0 + 1
theorem ws3_section_not_measure_preserving :
    attendsM (reifyM {e0}) = {e0} ∧ mu (reifyM {e0}) = mu e0 + 1 ∧ mu (reifyM {e0}) ≠ mu e0
theorem ws3_core_criterion :
    (∀ t m D, IsCore t m D → (∀ x ∈ D, m (t x) = m x) ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y))
  ∧ (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D)
theorem ws4_core_reachable : ∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D
theorem ws4_no_core_built : ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D
def verdict (tickMoves notInvertible sectionNotMP builtHasCore criterionSat : Bool) : Outcome  -- 5 outcomes
theorem ws5_verdict_eq : verdict true true true false true = Outcome.noCore
theorem ws5_verdict_discriminates : «reaches all five outcomes»
theorem ws5_flags_justified : «the five WS1–WS4 propositions, conjoined»
theorem ws5_audit_no_smuggle : (∀ D, D.Nonempty → ¬ IsCore tick mu D) ∧ (tick = fun x => reifyM {x})
theorem ws5_audit_fork_genuine : (∃ D, D.Nonempty ∧ IsCore tickR mu D) ∧ (∀ D, D.Nonempty → ¬ IsCore tick mu D)
theorem ws5_audit_decode_not_measure_preserving :
    (attendsM (reifyM {e0}) = {e0}) ∧ (mu (reifyM {e0}) ≠ mu e0) ∧ (∀ t m D, IsCore t m D → ∀ x ∈ D, m (t x) = m x)
theorem ws5_audit_measure_is_built_rank : (mu = P2S7.rankM) ∧ (rankM (reifyM {e0}) = rankM e0 + 1)
theorem ws5_audit_names_not_terms : True
```

## 3. Your task

For EACH target theorem:
1. Does the code in `formal/` state exactly this signature (no weakening, no hidden extra hypothesis, no `sorry`, no `axiom`) and DISCHARGE it? Check the proof term actually closes the goal.
2. STRIP TEST: delete any interpretive word from the docstring; does the THEOREM STATEMENT still stand as a plain fact about a finite map / its rank / injectivity / bijection / a right-inverse? Flag any theorem whose CONTENT depends on an interpretive reading rather than the literal Lean.
3. Verify the crux by hand on `Fin 4`: is `ws4_no_core_built` (∀ nonempty D, ¬ IsCore tick mu D) actually TRUE? Enumerate `tick` (e0→e1, e0'→e0, e1→e2, e2→e0) and check no nonempty D ⊆ {e0,e0',e1,e2} is closed + image=D + injective-on-D + rank-preserving. And is `{e0,e0'}` genuinely `IsCore tickR mu` (tickR swaps e0,e0', both rank 0)?

## 4. Audit checks (a)–(e), pressing hardest on (c), (a), (d)

- (a) NO INVERSE SMUGGLED. Confirm `IsCore` in `ws4_no_core_built` / `ws5_audit_no_smuggle` tests the SAME built `tick` (`= fun x => reifyM {x}`), and no separate inverse map is introduced. `tickR` is a control (a swap), used only in the positive satisfiability witness, not as an inverse of `tick`.
- (b) FORK NOT BY FIAT. `ws4_core_reachable` (satisfiable) and `ws4_no_core_built` (built map fails) both against the same `mu`; `IsCore` neither satisfiable-by-all nor unsatisfiable-by-all.
- (c) DECODABILITY IS NOT REVERSAL (highest priority). Confirm `ws3_section_not_measure_preserving` shows the right-inverse `attendsM` recovers the pattern YET `mu (reifyM {e0}) ≠ mu e0`, and that the `noCore` verdict rests on `IsCore` (bijection + measure-preservation), NOT on `attendsM` alone.
- (d) THE MEASURE IS THE BUILT RANK. Confirm `mu = P2S7.rankM` (`ws5_audit_measure_is_built_rank`, first conjunct `rfl`), and the rise cites the imported `ws2_tick_raises`.
- (e) NAMES-NOT-TERMS. Grep `formal/` for `\b(reversal|reversible|symmetry|conservation|energy|time|self|import|god|choice)\b` and confirm every hit is docstring/comment prose (or the Lean `import` keyword), NOT a proof-term / definition / theorem NAME. (`invertible`, `bijection`, `injective`, `section`, `measure`, `rank`, `core`, `tick` are allowed.)

## 5. Grading rubric

- **SERIOUS:** the verdict rests on it; a signature is not actually proved (a `sorry`/`axiom`, or the proof closes a weaker goal); an inverse is smuggled (added, not the built map); the verdict rests on the right-inverse `attendsM` rather than a measure-preserving bijection; the lower bar is used; the measure is rigged (not `rankM`); the fork is trivially true/false by construction; a proof-term/definition/theorem NAME is a forbidden content-word; an undisclosed narrowing between the seed signature and the built theorem.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim, a redundant clause, a naming nit, a `True` placeholder for the grep-enforced names audit.

Report a structured list of findings, each with a stable ID (`Fn-Sm`), a grade, the exact location (file + theorem), and the defect. State explicitly for each target whether the code proves it. Confirm at the top which files you read, and confirm you did NOT read any forbidden file. End with a count: SERIOUS / REAL / COSMETIC.
