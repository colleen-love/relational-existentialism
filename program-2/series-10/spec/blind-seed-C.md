# Blind seed — Phase C (design review). Series 2.10.

You are reviewing a DESIGN (typed signatures, not yet built). Judge each signature for coherence and non-vacuity against the contracts below. You are seeded with signatures, success criteria, audit checks, the strip test, the forbidden-names list, and the grading rubric — and NOTHING else. Do not seek motivating prose.

## 1. The objects and signatures under review

Carrier and measure are imported and reused verbatim from a predecessor build (`P2S7`):

```
abbrev Cfg : Type := P2S7.MCar         -- = Fin 4;  four states named e0, e0', e1, e2
abbrev mu  : Cfg → ℕ := P2S7.rankM      -- an imported measure; mu e0 = 0, mu e0' = 0, mu e1 = 1, mu e2 = 2

-- imported maps (from P2S7), reused verbatim:
--   reifyM  : Finset Cfg → Cfg   with  reifyM {e0} = e1,  reifyM {e1} = e2,  reifyM s = e0 otherwise
--   attendsM: Cfg → Finset Cfg   with  attendsM (reifyM {e0}) = {e0}   (a right-inverse on the used pattern)
--   P2S7.ws2_tick_raises : (ℵ₀ ≤ κ) → rankM (reifyM {e0}) = rankM e0 + 1 ∧ ...

def tick  : Cfg → Cfg := fun x => reifyM {x}
def tickR : Cfg → Cfg := fun x => if x = e0 then e0' else if x = e0' then e0 else x

def IsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Prop :=
    (∀ x ∈ D, t x ∈ D)
  ∧ (D.image t = D)
  ∧ (∀ x ∈ D, ∀ y ∈ D, t x = t y → x = y)
  ∧ (∀ x ∈ D, m (t x) = m x)

instance decIsCore (t : Cfg → Cfg) (m : Cfg → ℕ) (D : Finset Cfg) : Decidable (IsCore t m D) := by
  unfold IsCore; infer_instance

theorem ws1_tick_moves :
    tick e0 ≠ e0 ∧ mu (tick e0) = mu e0 + 1

theorem ws2_tick_not_invertible :
    ¬ Function.Injective tick
  ∧ (∃ x : Cfg, mu (tick x) ≠ mu x)
  ∧ mu (tick e0) = mu e0 + 1

theorem ws3_section_not_measure_preserving :
    attendsM (reifyM {e0}) = {e0}
  ∧ mu (reifyM {e0}) = mu e0 + 1
  ∧ mu (reifyM {e0}) ≠ mu e0

theorem ws3_core_criterion :
    (∀ t m D, IsCore t m D → ∀ x ∈ D, m (t x) = m x)
  ∧ (∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D)

theorem ws4_core_reachable :
    ∃ D : Finset Cfg, D.Nonempty ∧ IsCore tickR mu D

theorem ws4_no_core_built :
    ∀ D : Finset Cfg, D.Nonempty → ¬ IsCore tick mu D

inductive Outcome | noCore | coreFound | shapeDrawn | disconnected | partial'  deriving DecidableEq

def verdict (tickMoves notInvertible sectionNotMP builtHasCore criterionSat : Bool) : Outcome :=
  if !tickMoves then Outcome.disconnected
  else if !notInvertible then Outcome.partial'
  else if !sectionNotMP then Outcome.partial'
  else if builtHasCore then Outcome.coreFound
  else if criterionSat then Outcome.noCore
  else Outcome.shapeDrawn

theorem ws5_verdict_eq : verdict true true true false true = Outcome.noCore
theorem ws5_verdict_discriminates : «reaches all five outcomes on five input tuples»
theorem ws5_flags_justified : «the five flags are the WS1–WS4 propositions, conjoined»
theorem ws5_audit_no_smuggle : (∀ D, D.Nonempty → ¬ IsCore tick mu D) ∧ (tick = fun x => reifyM {x})
theorem ws5_audit_fork_genuine : (∃ D, D.Nonempty ∧ IsCore tickR mu D) ∧ (∀ D, D.Nonempty → ¬ IsCore tick mu D)
theorem ws5_audit_decode_not_measure_preserving :
    (attendsM (reifyM {e0}) = {e0}) ∧ (mu (reifyM {e0}) ≠ mu e0) ∧ (∀ t m D, IsCore t m D → ∀ x ∈ D, m (t x) = m x)
theorem ws5_audit_measure_is_built_rank : (mu = P2S7.rankM) ∧ (rankM (reifyM {e0}) = rankM e0 + 1)
theorem ws5_audit_names_not_terms : True
```

Facts you may assume from the imported build (verbatim, `decide`-checkable on `Fin 4`): `reifyM {e0} = e1`, `reifyM {e1} = e2`, `reifyM {e0'} = e0`, `reifyM {e2} = e0`; `rankM e0 = rankM e0' = 0`, `rankM e1 = 1`, `rankM e2 = 2`; `attendsM (reifyM {e0}) = {e0}`.

## 2. Success criteria (restated, mechanical)

1. The map `tick` and the measure `mu` are set up so that "invertible" and "measure-preserving" are well-posed, and `tick` non-trivially changes a state and its measure.
2. The full `tick` is not a measure-preserving bijection: not injective, and/or measure-raising.
3. The right-inverse `attendsM` recovers a pattern but does not preserve `mu`; `IsCore` is the stronger criterion (bijection AND measure-preservation).
4. The fork is genuine: `IsCore` is satisfiable on `mu` (some `D`, some map) AND the built `tick` satisfies it for no nonempty `D`.
5. The verdict is computed from the flags, discriminating, the flags earned by WS1–WS4; no inverse added; the higher bar (bijection + measure-preservation) used, not the right-inverse alone.

## 3. Audit checks (a)–(e), as mechanical instructions

- (a) NO INVERSE SMUGGLED. Check that `IsCore` tests the SAME map `t` (here `tick`) as the bijection; no separate inverse map is introduced anywhere; `ws4_no_core_built` searches restrictions of the built `tick`.
- (b) THE FORK NOT BY FIAT. Check both `ws4_core_reachable` (satisfiable) and `ws4_no_core_built` (built map fails) are stated against the SAME measure `mu`, and are not trivially true/false by construction (e.g. `IsCore` unsatisfiable for all maps, or satisfiable for all).
- (c) DECODABILITY IS NOT REVERSAL. Check `ws3_section_not_measure_preserving` states the right-inverse recovers the pattern YET `mu (reifyM {e0}) ≠ mu e0`; and that the verdict rests on `IsCore` (bijection + measure-preservation), NOT on `attendsM` alone. This is the highest-priority check.
- (d) THE MEASURE IS THE BUILT RANK. Check `mu` is the imported `P2S7.rankM` (not a fresh/rigged measure), and the raising fact is the imported `ws2_tick_raises`.
- (e) NAMES-NOT-TERMS. Grep the signatures: no definition or theorem NAME is a forbidden content-word as a whole word (list below). Names may mention the map, the measure, bijection/injectivity/right-inverse, the criterion, standard Lean/Mathlib.

## 4. The strip test and the forbidden-names list

**Strip test.** For each payoff, delete any interpretive term and check the bare statement still stands as a plain fact about a finite map, its rank, injectivity/bijection, or a right-inverse. Report any payoff whose content evaporates when the interpretive word is removed (a term doing load-bearing work).

**Forbidden as whole-word identifiers** (docstring prose exempt): `reversal`, `reversible`, `symmetry`, `conservation`, `energy`, `time`, `self`, `import`, `god`, `choice`. (`invertible`, `bijection`, `injective`, `section`, `measure`, `rank`, `core`, `tick` are all allowed.)

## 5. Grading rubric

- **SERIOUS:** the verdict rests on it; an inverse is smuggled (added, not the built map); the verdict rests on the right-inverse `attendsM` rather than a measure-preserving bijection; the lower bar is used (decodability counted as reversal); the measure is rigged; the fork is trivially true/false by construction (a fiat); a name is a forbidden content-word; or an undisclosed narrowing.
- **REAL:** a genuine gap, correctly labelled once fixed (an overclaimed docstring, an assumed-and-returned hypothesis, an over-strong name).
- **COSMETIC / ACCEPTABLE:** a nominal overclaim or naming nit.

Report a structured list of findings, each with a stable ID (`Cn-Sm`), a grade, the exact signature/location, and the defect. If you find nothing at a grade, say so.
