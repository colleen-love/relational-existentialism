# WS7 non-collapse — design v3

**Provenance.** v2 closed three *mathematical* gaps (μ↔L_R coupling, T-invariance, non-monotone outcome). v3 closes three *charter-binding* gaps found when the v2 signature was checked against the Relational Existentialism charter (Rev A/B/C). v3 changes nothing v2 got right; it makes the collector duty (§6.1 of the charter) fully explicit.

**v2 mathematical fixes (retained verbatim, see §§2–3, 6):**
1. `L_R : ℝ → ℝ≥0` is bundled in `SelectionLipschitz`, tied to the operator's own `μ` via `floorRegion μ` membership living in the simplex type — loose-constant laundering is untypeable.
2. `mutationStep_maps_into` (B0) makes `T : M → M` a total self-map of the complete `FlooredSimplex`; Banach is invoked only after invariance is discharged.
3. `DynamicalStatus` is a four-constructor inductive over an arbitrary `Set ℝ` admissible set; disconnected / empty-interior bands are nameable terminal states.

**v3 charter-binding fixes (new in this revision):**
4. **Collector tuple `(F, κ, μ, #Q)`, not `(κ, μ)`.** Charter Rev C §6.1 upgraded WS7's collector tuple to include `#Q`. `ws7_retro_validate` now takes an explicit `hQsmall : #Q ≤ κ` premise and `WS7NonCollapse` carries a `q_small` field. For the finite Łukasiewicz witness `Łₙ` this is discharged by `Nat.lt` (`#Łₙ = n+1 < ℵ₀ ≤ κ`), but it is now a *recorded discharged premise*, not silent vacuity — so "retro-validated at `κ₀`" no longer over-reads to the unbounded-`Q` case it does not cover.
5. **Richness floor split into (vii)-witness and (iv)-blocking general forms.** Charter Rev B pins WS7's branching-≥2 richness floor as *criterion (iv)-blocking* (WS3's sharp `alg`-non-triviality depends on it), not merely (vii)-blocking. v2 proved only the concrete two-element witness (the (vii) reading, which WS3 already had). v3 keeps that as `richness_witness` and adds `richness_general : GeneralBranching κ` as a **named open obligation**, flagged (iv)-blocking, never asserted from the two-element witness.
6. **Ambient-category scope stated, not assumed.** Charter §8.1-WS6 flags that the zero-object / no-view-from-nowhere face of §3.7 may live in a *different category* than the `Set`-based `Cofix` carrier. v3 states explicitly that WS7 operates entirely within the `Set`/`Cofix` category and therefore speaks to §3.7's *no-maximal* face and criterion (vii) only — **not** to the zero-object face or criterion (vi). This scope limit is a documented boundary field, so the collector's retro-validation cannot be read as ratifying a single-category coincidence the charter lists as open.

---

## 0. Ambient theory and imports

Carrier `νPk κ = ⟨Cofix (PkObj κ), Cofix.dest⟩`, `F = P_κ`, AFA coalgebraic, axiom budget `[propext, Classical.choice, Quot.sound]`, `#print axioms` owed on the top bundle. Imports from ws1/ws2/ws4/ws5/ws6 and Mathlib as in v2. The single owed import remains the WS1 carrier lower bound `mk (νPk κ).X ≥ κ` (T4 ⚠).

`ws5_attention_converges` is Banach on a complete metric space; the space must be shown complete **and** the map a self-map of it (v2's B0). `ws4_graded_law_coherence` is imported *with* its shape-count side condition `hQsmall : #Q ≤ κ` now made visible at the WS7 boundary (v3 fix 4).

**Scope of the carrier (v3 fix 6).** Every theorem below lives in the category of the `Set`-based `Cofix` construction of WS1/WS2. The zero-object route to §3.7's poles-coincidence (charter §3.7 bullet 1, §8.1-WS6) requires a category with a zero object, which is *not* this one. WS7 therefore makes **no** claim about criterion (vi) or the zero-object face; a `carrier_category` boundary note records this so the collector's scope is not over-read.

## 1. Proof architecture

```
   ws2_nondegenerate   ws6_no_maximal   ws2_weak_pullback
        └─────────┬─────────┴────────┬────────┘
                  ▼                  ▼
          ws7_static_band ◄── C1 (assembly, floor)
                  │
                  ▼
   ── DECISION NODE (C3) ──────────────────────────────────
   M := FlooredSimplex S μ unif           (complete, nonempty)
        ├─ B0  mutationStep_maps_into : T : M → M        (invariance, v2)
        ├─ B   selection_lipschitz_on_floor : L_R : ℝ→ℝ≥0 (coupling, v2)
        └─ A   mutation_lipschitz : Lip T ≤ (1−μ)(L_R μ)   (uses L_R μ, v2)
                  ▼
   ws7_mutation_contracts   (hfloor : (1−μ)(L_R μ) < 1)
                  ▼
   ws7_attention_fixed_point   (Banach on M; needs B0 + contraction)
   ─────────────────────────────────────────────────────────
                  ▼
   ws7_retro_validate ◄── C5 (collector spine)
     ratifies (F, κ, μ, #Q) at ONE concrete tuple      ← v3 fix 4
                  ▼
      ws7_band_and_retro   (assembly — NOT ws7_resolved)
        carries: q_small, richness_general (open, iv-block),  ← v3 fixes 4,5,6
                 carrier_category (scope note)
```

## 2. Definitions

Unchanged from v2 (reproduced for a self-contained artifact).

```lean
def FlooredSimplex (S : Type*) [Fintype S] (μ : ℝ) (unif : S → ℝ) : Type _ :=
  { w : S → ℝ // (∀ r, μ * unif r ≤ w r) ∧ (∑ r, w r = 1) }

instance : MetricSpace (FlooredSimplex S μ unif) := ...      -- ℓ¹
instance : CompleteSpace (FlooredSimplex S μ unif) := ...    -- closed subset of complete

structure SelectionMap (S : Type*) [Fintype S] (unif : S → ℝ) where
  R        : (S → ℝ) → (S → ℝ)
  nonneg   : ∀ w, (∀ r, 0 ≤ w r) → ∀ r, 0 ≤ R w r
  sum_one  : ∀ w, (∑ r, w r = 1) → (∑ r, R w r = 1)

def mutationStep (μ : ℝ) (unif : S → ℝ) (sel : SelectionMap S unif) :
    (S → ℝ) → (S → ℝ) :=
  fun w r => (1 - μ) * sel.R w r + μ * unif r

def floorRegion (μ : ℝ) (unif : S → ℝ) : Set (S → ℝ) :=
  { w | ∀ r, μ * unif r ≤ w r }

structure SelectionLipschitz (S : Type*) [Fintype S] (unif) (sel : SelectionMap S unif) where
  L_R    : ℝ → ℝ≥0
  bound  : ∀ (μ : ℝ), 0 < μ → μ ≤ 1 →
             ∀ w ∈ floorRegion μ unif, ∀ w' ∈ floorRegion μ unif,
               dist (sel.R w) (sel.R w') ≤ (L_R μ) * dist w w'
```

**New in v3 — the general branching predicate (fix 5).** The (iv)-blocking richness floor is *not* `∃ a b, a ≠ b`. It is the general one-step distinguishability WS3's `alg`-non-triviality consumes: every state has ≥2 behaviourally-distinct one-step observations available, uniformly.

```lean
-- (vii)-witness form: what v2 proved, what WS3 already had. Concrete, closed.
abbrev RichnessWitness (κ : Cardinal.{u}) : Prop := ∃ a b : (νPk κ).X, a ≠ b

-- (iv)-blocking form: what WS3's sharp non-triviality actually needs. OPEN.
-- "branching ≥ 2 everywhere, distinguishably" — not implied by a single a≠b pair.
structure GeneralBranching (κ : Cardinal.{u}) : Prop where
  branch : ∀ u : (νPk κ).X, ∃ x y, x ∈ (νPk κ).dest u ∧ y ∈ (νPk κ).dest u ∧
             ¬ Bisim x y                              -- two distinguishable successors
```

## 3. Lemmas and theorems

### C1 — static band. Unchanged from v2.

```lean
theorem ws7_static_band (hinf : ℵ₀ ≤ κ) (hcard : κ ≤ Cardinal.mk (νPk κ).X) :
    RichnessWitness κ
  ∧ (∀ u : (νPk κ).X, ¬ IsMaximal u)
  ∧ PkPreservesWeakPullback κ :=
  ⟨ws2_nondegenerate hinf, fun u => ws6_no_maximal hcard u, ws2_weak_pullback⟩
```

Note `ws2_nondegenerate` discharges the **witness** form only. It does **not** discharge `GeneralBranching`; v3 does not pretend it does (fix 5).

### B0, B, A, C3, fixed-point. Unchanged from v2.

```lean
lemma mutationStep_maps_into (μ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (unif) (hunif_nonneg) (hunif_sum) (sel) (w) (hw) :
    (∀ r, μ * unif r ≤ mutationStep μ unif sel w r)
  ∧ (∑ r, mutationStep μ unif sel w r = 1) := ...   -- (1−μ)·R w r ≥ 0 ; weight-preserving

def T ... : FlooredSimplex S μ unif → FlooredSimplex S μ unif := ...

lemma mutation_lipschitz (μ) (hμ1) (unif) (sel) (sl : SelectionLipschitz S unif sel) (hμ0)
    (w w' : FlooredSimplex S μ unif) :
    dist (T ... w) (T ... w') ≤ ((1 - μ) * (sl.L_R μ)) * dist w w' := ...

theorem ws7_mutation_contracts (μ) (hμ0) (hμ1) (unif) (sel) (sl)
    (hfloor_contr : (1 - μ) * (sl.L_R μ) < 1) :
    ∃ K : ℝ≥0, K < 1 ∧ ∀ w w' : FlooredSimplex S μ unif,
      dist (T ... w) (T ... w') ≤ K * dist w w' :=
  ⟨⟨(1 - μ) * (sl.L_R μ), by positivity⟩, hfloor_contr, mutation_lipschitz ...⟩

theorem ws7_attention_fixed_point (μ) (hμ0) (hμ1) (unif) (hunif_nonneg) (hunif_sum)
    (sel) (sl) (hfloor_contr) [Nonempty (FlooredSimplex S μ unif)] :
    ∃! p : FlooredSimplex S μ unif, T ... sel p = p := by
  obtain ⟨K, hK, hlip⟩ := ws7_mutation_contracts μ hμ0 hμ1 unif sel sl hfloor_contr
  exact ws5_attention_converges (T ...) K hK hlip
```

### C5 — retro-validation. REVISED (v3 fix 4): tuple `(F, κ, μ, #Q)`.

```lean
theorem ws7_retro_validate
    (κ₀ : Cardinal.{u}) (hreg : κ₀.IsRegular)
    (hcard : κ₀ ≤ Cardinal.mk (νPk κ₀).X)
    (n : ℕ) (hn : 2 ≤ n)
    (hQsmall : Cardinal.mk (Łuk n).Carrier ≤ κ₀) :          -- NEW: the #Q ≤ κ side condition
    Nonempty (WS2Characterization κ₀)
  ∧ (∀ u : (νPk κ₀).X, ¬ IsMaximal u)
  ∧ Nonempty (WS6NoPoles κ₀)
  ∧ Nonempty (GradedWeakLawCoherence (Luk n) κ₀ hreg hQsmall) :=   -- coherence now consumes hQsmall
  ⟨ws2_characterization hreg.aleph0_le hreg,
   fun u => ws6_no_maximal hcard u,
   ws6_split_and_no_maximal hreg.aleph0_le hcard,
   ws4_graded_law_coherence (Luk n) hreg hQsmall⟩

-- For the finite Łukasiewicz witness the shape count is discharged, not assumed:
example (κ₀) (hreg : κ₀.IsRegular) (n : ℕ) : Cardinal.mk (Łuk n).Carrier ≤ κ₀ := by
  -- #Łₙ = n+1 < ℵ₀ ≤ κ₀ by regularity
  have : Cardinal.mk (Łuk n).Carrier = (n + 1 : Cardinal) := luk_card n
  calc Cardinal.mk (Łuk n).Carrier = (n+1 : Cardinal) := this
       _ < Cardinal.aleph0 := by exact_mod_cast Nat.lt_of_lt ...   -- finite < ℵ₀
       _ ≤ κ₀ := hreg.aleph0_le
```

The `example` is the discharge: `hQsmall` is **proved** for `Łₙ`, so the collector genuinely ratifies the full tuple at the witness rather than dodging `#Q`. For an unbounded quantale `hQsmall` would be a live premise (the C4 reserve, `#Q = 𝔠 ⇒ κ₀ > 𝔠` or a ratified truncation) — and because it is now a *typed premise* of `ws7_retro_validate`, that case cannot be silently absorbed.

## 4. Assembly — REVISED (v3 fixes 4, 5, 6)

```lean
structure WS7NonCollapse (κ : Cardinal.{u}) (μ : ℝ) where
  -- static band (criterion vii structural + §3.7 no-maximal face)
  hinf              : ℵ₀ ≤ κ
  hcard             : κ ≤ Cardinal.mk (νPk κ).X
  richness_witness  : RichnessWitness κ                 -- (vii): ≥2 distinct objects. CLOSED.
  no_maximal        : ∀ u : (νPk κ).X, ¬ IsMaximal u     -- §3.7 bullet 2 / Cmt 3, κ-fiat resting
  weak_pb           : PkPreservesWeakPullback κ
  plurality         : 0 < μ                              -- §3.6 / §3.8 dynamical floor

  -- v3 fix 4: collector tuple includes #Q
  q_small           : QSmallRatified κ                   -- carries the #Q ≤ κ discharge/premise

  -- v3 fix 5: the (iv)-blocking richness floor, held OPEN and separate.
  -- Never inhabited from richness_witness. Its status is reported, not asserted.
  richness_general  : RichnessGeneralStatus κ            -- Discharged | Open(iv-blocking)

  -- v3 fix 6: ambient-category scope boundary. Documents what WS7 does NOT cover.
  carrier_category  : CarrierScope κ                     -- = SetCofixOnly (no zero-object/(vi))

  -- dynamical convergence: one of DynamicalStatus's four shapes (v2), never a bare hyp.
  dynamics          : DynamicalStatus S unif sel sl
```

Supporting status types (v3):

```lean
-- fix 4: makes the #Q duty a first-class, inspectable field.
inductive QSmallRatified (κ : Cardinal.{u})
  | discharged (Q : Type*) (h : Cardinal.mk Q ≤ κ)        -- e.g. Łₙ, h by Nat.lt
  | premised   (Q : Type*) (h : Cardinal.mk Q ≤ κ)        -- unbounded-Q: h is a live hypothesis
  -- both constructors CARRY the proof; the distinction records provenance, not strength.

-- fix 5: the (iv)-blocking floor is either proved or an explicitly-open, tagged obligation.
inductive RichnessGeneralStatus (κ : Cardinal.{u})
  | discharged (h : GeneralBranching κ)                   -- closes WS3's (iv) dependency
  | open_iv_blocking                                      -- NAMED open; (iv) NOT closable via WS7 yet
  -- there is deliberately no constructor that derives this from RichnessWitness.

-- fix 6: scope boundary, so collector retro-validation is not read past its category.
inductive CarrierScope (κ : Cardinal.{u})
  | set_cofix_only     -- covers §3.7 no-maximal face + (vii); NOT zero-object face / (vi)
  | unified_category (h : ZeroObjectCoincidesWithCarrier κ)  -- reserved; requires WS6 bridge
```

## 5. Dependencies and criterion binding (explicit)

Each WS7 field bound to the charter commitment / criterion it serves, and to the workstream that owns any residual:

- `richness_witness` → **criterion (vii)** structural non-collapse; §3.8 richness floor. *Owned & discharged by WS7.*
- `no_maximal` → **§3.7 bullet 2 / Commitment 3**; the WS1 §3.9 `κ`-fiat "no-everything" hand-off *resting* at concrete `κ₀`. *Discharged here; this is where the hand-off lands.*
- `plurality` + `dynamics` → **§3.6 / §3.8 / criterion (vii)** dynamical non-collapse; the standing risk "attention need not converge." *Owned by WS7; class = `DynamicalStatus`.*
- `q_small` → **charter Rev C §6.1** `(F,κ,μ,#Q)` collector duty; WS4's `#Q ≤ κ` shape count. *Discharged for `Łₙ`, premised for unbounded `Q`.*
- `richness_general` → **criterion (iv)**, via charter Rev B: WS3's `alg`-non-triviality is (iv)-blocking and rests on general branching. *WS7-owned, currently `open_iv_blocking`; criterion (iv) is NOT closable until this is `discharged`.*
- `carrier_category` → **§3.7 bullets 1&3 / criterion (vi)**: explicitly OUT of WS7 scope. *Owned by WS6; WS7 records only that it does not cover it.*

## 6. Expected terminal status

- **Static band (C1)** — Discharged (witness form), assembly.
- **Invariance (B0)** — Discharged (v2).
- **Retro-validation (C5)** — Discharged at `κ₀` for the **full `(F,κ,μ,#Q)` tuple**, with `hQsmall` proved for `Łₙ`; contingent on `hreg`+`hcard` cohold. *(v3 fix 4 — no longer silent on `#Q`.)*
- **Dynamical convergence (C3)** — decision node, four-way `DynamicalStatus` (v2): `discharged` / `impossible` / `partial` (interval or disconnected). Class deferred to `SelectionLipschitz` (Lemma B).
- **Richness (iv-blocking)** — `open_iv_blocking` (v3 fix 5). WS7 discharges the (vii) witness; the (iv)-blocking general branching is a *named open obligation*, not derived from the witness. **Criterion (iv) is not closable from the WS7 side until this flips to `discharged`.**
- **Ambient-category scope** — `set_cofix_only` (v3 fix 6). WS7 covers §3.7's no-maximal face and (vii); it makes **no** claim on the zero-object face or criterion (vi), which the charter §8.1-WS6 leaves open across a possible category split.

**Overall WS7: class deferred to Lemma B on the dynamical axis; three collector duties now explicit rather than silent.** The bundle is named `ws7_band_and_retro`, **not** `ws7_resolved`: the static band and full-tuple retro-validation are discharged, but (a) the dynamical field's status is C3's outcome, (b) the (iv)-blocking richness floor is an open tagged field, and (c) the zero-object/(vi) face is explicitly out of scope. A positive-sounding name, or folding any of (a)–(c) into a discharged-looking field, would launder an open obligation — the §8.2 discipline, and exactly the three over-reads the charter check flagged.

**What v3 no longer lets an importer over-read.** (1) "Retro-validated" now provably includes `#Q ≤ κ`, not by luck. (2) `richness_witness` cannot be mistaken for the (iv)-blocking floor — they are different fields, and no constructor bridges them. (3) The collector's category scope is a stated boundary, so single-category coincidence is never implicitly ratified. The one genuinely open mathematical obligation remains Lemma B; the collector-level obligations are now visible, typed, and correctly attributed.
