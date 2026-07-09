# WS7 triage

## Paper-decidable predicates

Seven predicates, each answerable by inspection of the imported artifacts without running Lean:

- **T1 — imports resolve:** every upstream symbol the candidate cites exists in ws1/ws2/ws4/ws5/ws6 with a compatible signature.
- **T2 — hypotheses cohold:** the candidate's hypothesis set is demonstrably jointly satisfiable (no two premises contradict at the cardinal or order level).
- **T3 — no new hard analysis:** the candidate needs no genuinely new proof beyond assembly of imported results.
- **T4 — carrier lower bound owned:** the candidate's need for `κ ≤ #(νPk κ).X` is either imported (WS1 exposes it) or must be assumed as a hypothesis (⚠ = assumed, not owned).
- **T5 — closes an open obligation:** discharges something currently open (WS5 contraction, WS6 (vi), WS4 Layer C) rather than repackaging closed results.
- **T6 — outcome is two-valued:** success and failure are both sharp, nameable terminal states (no vacuous-true escape).
- **T7 — non-laundering:** the deliverable's shape structurally prevents a proved sub-part from being read as the whole.

## Triage table

| | T1 imports | T2 cohold | T3 no new analysis | T4 lower bound | T5 closes open | T6 two-valued | T7 non-launder | Verdict |
|---|---|---|---|---|---|---|---|---|
| **C1** static band | Yes | Yes | Yes | ⚠ assume | No | partial | needs naming | **Assembly — floor** |
| **C2** conditional band | Yes | Yes | Yes | ⚠ assume | No (re-exposes WS5) | No (conditional) | Yes (field) | **Assembly — packaging** |
| **C3** mutation contracts | ⚠ `IsReplicatorMutator` only typed | unknown (μ-range) | **No — the hard proof** | n/a | **Yes (WS5 C4)** | **Yes** | Yes | **Primary — decision node** |
| **C4** band empty | Yes (types) | n/a | cardinal squeeze only | n/a | Yes (negative) | Yes | Yes | **Reserve** |
| **C5** retro-validate | Yes | ⚠ reg + lower bound | Yes | ⚠ assume | No | **Yes** | Yes | **Collector — mandatory** |

**Reading the table.** C3 is the only row with `T5 = Yes` *and* `T3 = No` — it is the sole candidate that closes a genuinely open obligation and the sole one requiring real analysis. That combination makes it the decision node: its outcome (Discharged vs. Impossibility vs. Partial-with-precise-μ-obstruction) determines the class of the entire workstream. C5 is the only row that *is* the collector deliverable (`T6 = Yes`, mandatory regardless). C1/C2 are assembly-only (`T3 = Yes`, `T5 = No`) — necessary scaffolding, insufficient alone. C4 is a clean reserve: fully paper-decidable, pursued only if C1/C5's arithmetic exposes a real conflict.

**Selection.** Primary design target: **C3** (the contraction), assembled with **C5** (retro-validation) as the collector spine, resting on **C1** as the static floor. C2 becomes the fallback *packaging* if C3 resists; C4 held in reserve. The triage — not a framing preference — forces C3 to the front: it is where the only undecided-on-paper cell sits (C3/T2), and paper triage cannot resolve it, so the design must.

---

# Full design — WS7 non-collapse

## 0. Ambient theory and imports

Carrier `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, `F = P_κ`. No monad or distributive law at this layer; WS7 consumes upstream carriers, it does not compose. AFA modeled coalgebraically. Axiom budget `[propext, Classical.choice, Quot.sound]`, `#print axioms` owed on the top bundle.

Imports (established, axiom-free):
- **ws1/ws2:** `νPk`, `νPk_terminal`, `ws2_nondegenerate`, `ws2_characterization`, `PkObj`, `PkMap`. If WS1 exposes the carrier lower bound `mk (νPk κ).X ≥ κ` as a ratified lemma it is consumed; otherwise `hcard` is a WS7 hypothesis (T4 ⚠, honestly stated).
- **ws4:** `Luk`, `GradedWeakLawCoherence`, `ws4_graded_law_coherence` — for the retro-validation conjunct.
- **ws5:** `Attn`, `IsReplicatorMutator`, `ws5_attention_converges` (the Banach step), `ws5_plurality_floor`, and the *uninhabited* `replicator_mutator_contracts` — C3's target is precisely to inhabit an instance of this.
- **ws6:** `IsMaximal`, `ws6_no_maximal`, `WS6NoPoles`, `ws6_split_and_no_maximal`.
- **Mathlib:** `ContractingWith`, `LipschitzWith`, `MetricSpace`/`CompleteSpace`, `Finset.sum`, the `ℓ¹`/simplex API, `NNReal`, `Cardinal.IsRegular`.

## 1. Proof architecture

```
   ws2_nondegenerate   ws6_no_maximal   ws2_weak_pullback
        │                   │                 │
        └─────────┬─────────┴────────┬────────┘
                  ▼                  ▼
          ws7_static_band ◄── C1 (assembly, floor)
                  │
                  │  (μ>0 from hμ)
                  ▼
   ── THE DECISION NODE (C3) ─────────────────────────────
   simplex model M := floored attention simplex on S u
   T := (1−μ)·R  +  μ·U          (replicator + uniform mutation)
        │              │
   R Lipschitz on   U strict contraction
   μ-floored interior   toward barycenter
        └──────┬───────┘
               ▼
      ws7_mutation_contracts : ∃ K<1, Lipschitz T ≤ K·dist
               │  (feeds hcontr)
               ▼
   ws5_attention_converges ──► ws7_attention_fixed_point (∃! p, T p = p)
   ────────────────────────────────────────────────────
                  │
                  ▼
   ws7_retro_validate ◄── C5 (collector spine)
   instantiates ws2/ws4/ws6 at one concrete (κ₀, μ₀)
                  │
                  ▼
      WS7NonCollapse  (assembly — NOT ws7_resolved)
```

The static floor (C1) and collector (C5) are pure assembly and cannot fail beyond a cohold check. All real content is the C3 branch; everything else routes through or around it.

## 2. Definitions

**The floored simplex model.** Fix a state `u` with support `S := SelfSupport κ u`, assumed finite for the concrete band (the general case routes to a countable-`ℓ¹` completion, deferred). The attention simplex with a `μ`-floor against uniform reference `unif`:

```lean
def FlooredSimplex (S : Type*) [Fintype S] (μ : ℝ) (unif : S → ℝ) : Type _ :=
  { w : S → ℝ // (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) }
```

Metric: `ℓ¹` (total variation), `dist w w' = ∑ r, |w r − w' r|`. This is a closed subset of a complete space, hence complete; nonempty because the floored uniform point lies in it (for `μ ≤ 1` and `unif` a probability vector).

**The mutation operator.** Given a selection map `R : (S → ℝ) → (S → ℝ)` (replicator, weight-preserving, Lipschitz constant `L_R` on the interior) and uniform pull:

```lean
def mutationStep (μ : ℝ) (unif R) : (S → ℝ) → (S → ℝ) :=
  fun w r => (1 - μ) * R w r + μ * unif r
```

**The Lipschitz-witness predicate (C3 target).** An inhabitant of WS5's `replicator_mutator_contracts μ` for this concrete `T`.

## 3. Lemmas and theorems

**C1 — static band (assembly).**
```lean
theorem ws7_static_band (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) :
    (∃ a b : (νPk κ).X, a ≠ b)
  ∧ (∀ u : (νPk κ).X, ¬ IsMaximal u)
  ∧ PkPreservesWeakPullback κ :=
  ⟨ws2_nondegenerate hinf, fun u => ws6_no_maximal hcard u, ws2_weak_pullback⟩
```
Trivial once T1/T2 pass. Non-vacuity of `hcard` is the only owed side-fact (T4).

**C3 — the contraction (the one new proof).** Structure the Lipschitz bound as the sum of two contributions:

*Lemma A — mutation term contracts.* The map `w ↦ μ·unif` component is constant, contributing `0` to the Lipschitz constant; the `(1−μ)·R` component scales `R`'s constant by `(1−μ)`.
```lean
lemma mutation_lipschitz (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (R : (S → ℝ) → (S → ℝ)) (L_R : ℝ≥0)
    (hR : ∀ w w', dist (R w) (R w') ≤ L_R * dist w w') :
    ∀ w w', dist (mutationStep μ unif R w) (mutationStep μ unif R w')
              ≤ ((1 - μ) * L_R) * dist w w'
```
Proof: `dist(Tw, Tw') = ∑|((1−μ)Rw + μu) − ((1−μ)Rw' + μu)| = (1−μ)∑|Rw − Rw'| ≤ (1−μ)L_R·dist`, the `μu` terms cancelling. Pure `ℓ¹` algebra, no analysis beyond triangle inequality.

*Lemma B — the floor bounds `R`'s expansion.* On the `μ`-floored interior, replicator selection has a bounded Lipschitz constant `L_R = L_R(μ)` (the fitness gradient is bounded where all weights exceed `μ·min unif > 0`). This is the genuinely analytic step and the one paper-triage could not decide.

*Theorem (C3).*
```lean
theorem ws7_mutation_contracts (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (R : (S → ℝ) → (S → ℝ)) (L_R : ℝ≥0)
    (hR : ∀ w w', dist (R w) (R w') ≤ L_R * dist w w')
    (hfloor_contr : (1 - μ) * L_R < 1) :
    ∃ K : ℝ≥0, K < 1 ∧ ∀ w w',
      dist (mutationStep μ unif R w) (mutationStep μ unif R w') ≤ K * dist w w' :=
  ⟨⟨(1 - μ) * L_R, by positivity⟩, hfloor_contr, mutation_lipschitz μ hμ hμ1 R L_R hR⟩
```

**Critical honesty point.** The contraction is *conditional on `hfloor_contr : (1−μ)·L_R < 1`*. This inequality is where the outcome forks and is what the paper triage left as C3/T2 unknown:

- If `L_R` (the interior selection Lipschitz bound) can be proved `< 1/(1−μ)` for some `μ`-range → **Discharged**, and `hfloor_contr` is closed by Lemma B, not assumed.
- If `L_R` provably exceeds `1/(1−μ)` for all `μ ∈ (0,1]` → the operator is non-contractive: **Impossibility proved** on the dynamical axis (the "attention need not converge" risk realized).
- If Lemma B yields `L_R` bounded only on a sub-range of `μ` → **Partial**, with the exact admissible `μ`-interval as the precise obstruction.

The design must not leave `hfloor_contr` as a bare hypothesis in the final bundle — that would relaunder the WS5 conditional under a new name (T7 violation). Lemma B must either discharge it or report which case obtains.

**Feed into Banach.**
```lean
theorem ws7_attention_fixed_point (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (R L_R) (hR) (hfloor_contr : (1 - μ) * L_R < 1)
    [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p, mutationStep μ unif R p = p := by
  obtain ⟨K, hK, hlip⟩ := ws7_mutation_contracts μ hμ hμ1 R L_R hR hfloor_contr
  exact ws5_attention_converges _ K hK hlip
```
Direct reuse of the imported Banach step — no re-proof, the payoff of WS5 having quarantined the contraction as its sole hypothesis.

**C5 — retro-validation (collector spine).**
```lean
theorem ws7_retro_validate (κ₀ : Cardinal.{u}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X) (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WS2Characterization κ₀)
  ∧ (∀ u : (νPk κ₀).X, ¬ IsMaximal u)
  ∧ Nonempty (WS6NoPoles κ₀)
  ∧ Nonempty (GradedWeakLawCoherence (Luk n) κ₀ hreg) :=
  ⟨ws2_characterization hreg.aleph0_le hreg,
   fun u => ws6_no_maximal hcard u,
   ws6_split_and_no_maximal hreg.aleph0_le hcard,
   ws4_graded_law_coherence (Luk n) hreg⟩
```
Certifies all consumed theorems survive one concrete `κ₀`. Its only owed cohold: `hreg` and `hcard` co-holding — the T2/T4 check that WS1's lower bound is available at a regular cardinal.

## 4. Assembly

```lean
structure WS7NonCollapse (κ : Cardinal.{u}) (μ : ℝ) where
  hinf         : ℵ₀ ≤ κ
  hcard        : κ ≤ Cardinal.mk (νPk κ).X
  richness     : ∃ a b : (νPk κ).X, a ≠ b            -- structural non-collapse
  no_maximal   : ∀ u : (νPk κ).X, ¬ IsMaximal u       -- non-totalization
  weak_pb      : PkPreservesWeakPullback κ
  plurality    : 0 < μ                                -- dynamical floor
  -- dynamical convergence: present ONLY if C3's Lemma B discharged hfloor_contr.
  -- If Partial, this field is REPLACED by `converges_on : admissible μ-range`,
  -- never by a bare-hypothesis contraction field.
```

```lean
theorem ws7_band_and_retro
    (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) (hμ : 0 < μ) :
    Nonempty (WS7NonCollapse κ μ)
```

Named `ws7_band_and_retro`, **not** `ws7_resolved`: the static band is discharged, retro-validation holds at `κ₀`, but the dynamical field's status is exactly C3's outcome. A positive-sounding name would let the proved static floor launder an open (or Partial) contraction — the T7 requirement, and the discipline transplanted from `ws4_graded_coherence_Luk` / `ws6_split_and_no_maximal`.

## 5. Dependencies on imported theorems (explicit)

- `ws2_nondegenerate`, `ws2_weak_pullback`, `ws2_characterization` → static band + retro; `(F,κ)`-coupled, must survive `κ₀`.
- `ws6_no_maximal`, `ws6_split_and_no_maximal` → non-totalization; carries WS1's `κ`-fiat forward — WS7 is where it finally rests as a ratified concrete `κ₀`.
- `ws5_attention_converges` → the Banach step, consumed verbatim; **`replicator_mutator_contracts` is the target C3 inhabits**, closing WS5's sole open obligation.
- `ws4_graded_law_coherence` → retro conjunct; couples the `#Q ≤ κ` side condition (vacuous at `Luk n`, live for unbounded `Q` — the C4 reserve territory).
- WS1 carrier lower bound `mk (νPk κ).X ≥ κ` → the single owed import (T4); if unavailable it stays a WS7 hypothesis and the "unconditional band" claim is qualified accordingly.

## 6. Expected terminal status

- Static band (C1) — **Discharged**, assembly.
- Retro-validation (C5) — **Discharged** at `κ₀`, contingent on `hreg`+`hcard` cohold.
- Dynamical convergence (C3) — **the decision node**: Discharged if Lemma B closes `hfloor_contr`; Impossibility-proved if the selection Lipschitz bound provably defeats mutation for all `μ`; Partial with an exact admissible `μ`-interval otherwise. This single lemma sets the whole workstream's class.
- If C3 resists: fall back to the C2 packaging (`converges_if` conditional field) and report **Partial**, obstruction = the precise inequality `(1−μ)·L_R < 1` and the `μ`-range on which Lemma B fails.

**Overall WS7: class deferred to Lemma B.** The design is complete and assembly-ready on every axis except the one the paper triage correctly flagged as undecidable on paper; that axis is now isolated to a single Lipschitz inequality whose resolution is the workstream's terminal verdict.
