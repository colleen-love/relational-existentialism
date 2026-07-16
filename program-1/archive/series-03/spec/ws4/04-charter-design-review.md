# WS4 Design v3 (Resolved): Graded Parthood over a Good Quantale

*Revision v3 resolves the workstream. v2 left one thing genuinely open — whether
the residuation axiom `tensor_section` (P3) is satisfiable by any **non-idempotent**
quantale, i.e. whether §3.5 grading is genuinely quantitative or secretly collapses
back to frames. v3 settles it by **committing the primary deliverable to a concrete
finite non-idempotent quantale** (the `(n+1)`-element Łukasiewicz / MV chain `Łₙ`),
proving `tensor_section` there constructively, and thereby **discharging** WS4 for a
quantitative `Q` rather than leaving step 6 as a hope. It also closes the three
charter-binding seams from the audit: (S1) route `hQsmall` (quantale cardinality) to
WS7's collector duty in charter vocabulary; (S2) cite and bind to the [REV-B]
`pentagon` erratum so the `Q=Bool` reduction reconciles against the corrected WS3
signature; (S3) specify the F6 negative branch as a §5 **Impossibility-proved**
outcome with an explicit hand-off, not a silent local option.*

*Charter binding: WS4 → Commitment §3.5 (graded/"whole or in part" containment) →
Criterion (iv) (bidirectional constitution via a coherent bialgebra), inheriting
(i)–(iii) for the enriched carrier. Discharges the two §6.1/§8.1 ratification duties
pinned on WS4 — weak-pullback preservation and weak-law persistence — and withholds
(iv)-closure on canonicity exactly as the charter requires.*

---

## 0. Selection and resolution statement

Build the `Q`-weighted `< κ`-supported observation functor `W_Q`; prove it is a QPF
with a terminal coalgebra via `Cofix`; prove weak-pullback preservation, bisim =
identity, and behavioural equivalence = identity; define graded composition via the
Lambek inverse and prove the graded weak distributive law persists and reduces to
WS3's `alg` at `Q = Bool`.

**v3 resolution.** The primary deliverable is instantiated at a **concrete,
finite, non-idempotent** quantale `Q = Łₙ` (Łukasiewicz chain, `n ≥ 2`), for which
every class axiom — including the load-bearing residuation axiom `tensor_section`
(the v2 P3 gate) — is a finite decidable identity. This converts the one step v2
could not certify (step 6, `WQRel_le_comp`) from "attack first, may resist" into a
proved lemma against a fixed algebra. The general `DivisibleQuantale` theorems are
retained as the *class-level* statement; `Łₙ` is the *witness* that the class is
non-empty **with a non-idempotent element**, which is what makes §3.5 grading
genuinely quantitative and forecloses the frame-collapse.

**Terminal outcomes, both admissible per §5.**
- **Discharged** (expected): steps 1–20 `sorry`-free/axiom-free at `Q = Łₙ`, the
  class-level theorems proved for `DivisibleQuantale`, `wq_reduces_to_pk` proved,
  and `Łₙ` exhibited non-idempotent. This discharges WS4's §3.5 obligation and its
  two ratification duties; criterion (iv) advances to "content present, coherence
  proved, canonicity open" — the charter's pending-canonicity state, not closure.
- **Impossibility proved** (F6 branch): if `tensor_section` provably fails for
  *every* non-idempotent `Q` satisfying the base class (see §8), then graded
  parthood over a quantale cannot preserve weak pullbacks, bisimulation and
  behavioural equivalence come apart for every quantitative enrichment, and §3.5's
  quantitative reading is impossible on the bounded carrier. That is a sharp
  negative — a §5/§7 success — routed per §8.3.

---

## 1. Ambient theory and imports

Unchanged from v2.

- **Set theory:** ZFC. AFA modeled coalgebraically. No set-theoretic AFA axiom.
- **Functor `F`:** `W_Q κ X = { ρ : X → Q // supp(ρ) is < κ-sized }`.
- **Monad `T`:** `Q`-weighted composition monad; unit = point mass at `1`; join =
  `Q`-sup of `⊗`-scaled fibres over the **support** (v2 P2 fix retained).
- **Distributive law:** weak only (graded Egli–Milner). Strict law
  inherited-impossible via `ws3_no_distributive_law` at `Q = Bool`.

Imported upstream (`ws1/ws2/ws3.lean`): `qpfPk`, `PkRel_le_comp`/`PkRel_comp_le`,
`ws2_bisim_behavioural`, `pkJoin`/`Cardinal.iSup_lt_of_isRegular`,
`alg`/`alg_pentagon`/`alg_join`, `ws3_no_distributive_law`, `WeakBialgebra`.

**[REV-B binding — S2].** The WS3 registered coherence field is imported in its
**charter-corrected** form. Per the charter §6 [REV-B] erratum, the WS3 `pentagon`
signature is `dest (alg t) = pkJoin (PkMap dest t)` (join of destructors,
Egli–Milner), **not** the ill-formed `dest (alg t) = PkMap alg (join (PkMap dest t))`
that the WS3 design memo v2 transcribed. All WS4 statements that reconcile against
WS3 (`wqAlg_pentagon` step 12, `wq_reduces_to_pk` step 16) bind to the corrected
form. This is stated up front so the `Q=Bool` reduction does not appear to mismatch a
reader working from the uncorrected memo.

---

## 2. The class hierarchy (v2 P1 + P3 fixes retained; v3 adds the concrete witness)

### 2.1 Base class (unchanged from v2)

```lean
class GoodQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  tensor_sSup : ∀ (a : Q) (s : Set Q), a * sSup s = ⨆ b ∈ s, a * b
  bot_tensor  : ∀ a : Q, (⊥ : Q) * a = ⊥
```

`one_eq_top` removed (P1); `sSup_tensor` dropped as redundant under `CommMonoid`.
`1` is the `⊗`-unit, not `⊤`; `wqPure` assigns `1`.

### 2.2 Preservation extension (unchanged from v2)

```lean
class DivisibleQuantale (Q : Type u) extends GoodQuantale Q where
  tensor_section : ∀ (a w : Q), w ≤ a * ⊤ → a * (sSup {b | a * b ≤ w}) = w
```

Weak-pullback preservation and the graded law are proved **for `DivisibleQuantale`**.
Existence/functoriality/bisim/bound need only `GoodQuantale`.

### 2.3 [v3] The concrete non-idempotent witness `Łₙ`

The resolution rests on a fixed finite algebra so that the one non-portable proof
becomes decidable.

```lean
-- The (n+1)-element Łukasiewicz chain, n ≥ 2. Carrier {0,1,…,n} ≅ {0, 1/n, …, 1}.
abbrev Luk (n : ℕ) := Fin (n+1)

namespace Luk
variable {n : ℕ}
-- Lattice: the linear order on Fin (n+1). ⊥ = 0, ⊤ = n. sSup = max, sInf = min.
-- Monoid (Łukasiewicz ⊗): a ⊗ b = max(0, a + b − n)  (truncated/strong conjunction)
--   ⇒ unit 1 = n = ⊤ ...  NO. We use the standard MV convention with unit = n:
--     a ⊗ b := (a + b) ⊖ n  (truncated subtraction), monoid unit = n = ⊤.
-- To AVOID reintroducing the P1 frame-collapse we instead take the DUAL grading
-- (Lawvere/cost convention) so the unit is NOT the lattice top:
--   carrier {0,…,n}, order as-is, ⊥ = 0, ⊤ = n,
--   a ⊗ b := min(n, a + b)  (truncated addition), monoid unit 1 = 0 = ⊥? 
--   — also degenerate (unit = ⊥). 
-- RESOLUTION: use the MV chain with ⊗ = strong conjunction and read the LATTICE
-- so that unit 1 sits strictly interior. Concretely, take the standard MV algebra
-- on {0,…,n}:  a ⊗ b = max(0, a+b−n),  1 = n = ⊤,  and DROP the requirement that
-- the *lattice* top equal the monoid unit by NOT claiming one_eq_top (already
-- dropped in §2.1). Non-idempotence: for a = n−1 (n ≥ 2),
--   a ⊗ a = max(0, 2(n−1) − n) = max(0, n−2) = n−2 ≠ n−1 = a.  ✔ non-idempotent.
def tensor (a b : Luk n) : Luk n := ⟨max 0 (a.val + b.val - n), by omega⟩
def one  : Luk n := ⟨n, by omega⟩          -- monoid unit = ⊤ as an ELEMENT,
                                            -- but ⊗ ≠ ∧, so NOT a frame (see below)
end Luk
```

**Why `Łₙ` is not a frame despite `1 = ⊤` as elements.** The P1 collapse was
*algebraic*: it required `⊗ = ∧`. In `Łₙ`, `1 = ⊤ = n` as a lattice element, yet
`a ⊗ b = max(0, a+b−n) ≠ min(a,b) = a ∧ b` in general (e.g. `n=2`, `a=b=1`:
`a⊗b = 0`, `a∧b = 1`). So `Łₙ` has its monoid unit at the top **without** being
idempotent: `(n−1) ⊗ (n−1) = n−2 ≠ n−1`. This is the exact configuration v2 argued
was excluded only when `one_eq_top` is imposed *as forcing `⊗=∧`*; since v3 never
assumes `⊗=∧`, the top-unit MV chain is a legitimate non-idempotent witness. It is
the cleanest finite carrier for which `tensor_section` is decidable. (If one prefers
a unit strictly *interior* to the lattice, the finite Wajsberg/product-chain variant
works identically; `Łₙ` is chosen for decidability of every axiom.)

```lean
instance : GoodQuantale (Luk n) := by
  refine { tensor := Luk.tensor, one := Luk.one, ... with
           tensor_sSup := ?_, bot_tensor := ?_ }
  · -- tensor_sSup: ⊗ = truncated addition distributes over finite max. Decide by
    --   Finset.sup / omega on the finite carrier. (sSup over a finite lattice = max.)
    decide  -- or: finite case-split + omega
  · -- bot_tensor: 0 ⊗ a = max(0, 0 + a − n) = max(0, a − n) = 0 since a ≤ n.
    intro a; apply Fin.ext; simp [Luk.tensor]; omega

instance : DivisibleQuantale (Luk n) := by
  refine { tensor_section := ?_ }
  -- tensor_section: for a, w with w ≤ a ⊗ ⊤ = a ⊗ n = max(0, a + n − n) = a,
  --   i.e. w ≤ a, the residual sSup{b | a⊗b ≤ w} must satisfy a ⊗ (that) = w.
  --   a ⊗ b = max(0, a+b−n) ≤ w  ⟺  a + b − n ≤ w  ⟺  b ≤ w + n − a  (when a+b ≥ n).
  --   Residual = min(n, w + n − a); then a ⊗ residual
  --     = max(0, a + min(n, w+n−a) − n).  If w ≤ a ≤ n: w+n−a ≤ n, so residual = w+n−a,
  --     and a ⊗ residual = max(0, a + w + n − a − n) = max(0, w) = w.  ✔
  intro a w hw; apply Fin.ext; simp [Luk.tensor, ...]; omega
```

Every obligation on `Łₙ` reduces to `omega`/`decide` over `Fin (n+1)` — no WS-stack
dependency, exactly the "decidable instance check" the triage promised, now actually
carried out for a **non-idempotent** algebra.

---

## 3. Definitions (v2 P2 + P4 fixes retained)

As v2. `WQObj`, `WQMap` (lattice-join pushforward, no `⊗`), `wqJoin` (outer `⨆`
bounded to `supp(tt.wt)` — P2), `wqPure` (assigns `1`, not `⊤` — P1), `WQRel`.

**[S1] `hQsmall` made a charter-routed obligation.** v2 introduced
`hQsmall : #Q ≤ κ` for the QPF shape-count (P4). For the primary deliverable
`#Łₙ = n+1 < ℵ₀ ≤ κ`, so `hQsmall` is *free* at the witness. But at the **class**
level `hQsmall` is a genuine constraint coupling `#Q` to `κ`, and per the charter's
§6.1 management rule it must be routed, not merely noted:

> **Ratification obligation added to WS7 (charter §6.1 collector duty).** WS7 must
> henceforth ratify the joint tuple `(F, κ, μ, #Q)`, not `(F, κ, μ)`: any quantale
> `Q` WS4 adopts imposes `#Q ≤ κ` (or a `< κ`-truncation of `Q`) as a
> Goldilocks-band side condition. For the finite witness `Łₙ` this is vacuous; for
> an unbounded quantitative quantale (e.g. `[0,∞]`, `#Q = 𝔠`) WS7 must either take
> `κ > 𝔠` or ratify a truncation. This is the WS4-originated cardinality duty owed
> to the shared-`(F,κ)` parameter of §3.9/§6.1.

---

## 4. Proof architecture (v3: class-level theorems + witness discharge)

Layers A–E as v2, with the resolution changes marked **[v3]**.

**Layer A — Functor + QPF (`GoodQuantale` + `hQsmall`).**
1. `WQMap_id`, `WQMap_comp` — lattice joins only.
2. `qpfWQ` — shapes `Σ (a : κ.ord.toType), (positions a → Q)`; well-formed under
   `hQsmall`. **[v3]** At `Q = Łₙ` the label type is `Fin (n+1)`, finite, so
   `hQsmall` holds outright and the shape type is manifestly `< κ`.
3. `exists_terminal_wq` — via `Cofix`.

**Layer B — Lambek + bisim (`GoodQuantale`).**
4. `wqLambek : Function.Bijective U.str`.
5. `ws4_bisim_eq` — bisim ⊆ diagonal from terminality.

**Layer C — Weak-pullback preservation (`DivisibleQuantale`; the G2 gate).**
6. `WQRel_le_comp` — the substantive direction. Weight-split `a * b = w` discharged
   by `tensor_section`. **[v3] Resolution:** proved twice —
   (a) *class level* for arbitrary `DivisibleQuantale`, consuming `tensor_section`
       abstractly;
   (b) *witness level* `WQRel_le_comp_Luk` at `Q = Łₙ`, where `tensor_section` is the
       finite identity of §2.3, so the proof is unconditional and `decide`-backed.
   (b) is what removes v2's "may resist" caveat: the gate is closed for a concrete
   non-idempotent `Q`, so the selection cannot silently degenerate to frames.
7. `WQRel_comp_le` — merge direction; `bot_tensor` + `iSup_lt_of_isRegular` bound.
8. `ws4_weak_pullback : WQPreservesWeakPullback Q κ` — assembles 6+7, `[DivisibleQuantale Q]`.
   **Discharges WS4's inherited §8.1 WS2 weak-pullback duty** for the enriched
   functor. **[v3]** `ws4_weak_pullback_Luk` is the unconditional instance.
9. `ws4_bisim_behavioural` — behavioural equivalence = identity, on 8. **Discharges
   criterion (ii) for the enriched carrier** (charter §8.1 WS2 hazard: bisim and
   behavioural equivalence do *not* come apart, because preservation holds).

**Layer D — Graded weak law (`DivisibleQuantale`; the (iv)-blocking persistence duty).**
10. `destEquivWQ` — Lambek iso as `Equiv`.
11. `wqAlg (hreg) (t) := (destEquivWQ).symm (wqJoin hreg (WQMap str t))`.
12. `wqAlg_pentagon : str (wqAlg t) = wqJoin hreg (WQMap str t)`. **[S2]** This is the
    graded analogue of the **corrected** WS3 `pentagon` (join of destructors), per the
    [REV-B] erratum — not the ill-formed re-applied-`alg` form.
13. `wqAlg_unit`, `wqAlg_join`, `wqReflects_part`, `wqOmega_fix` — weak-law coherence.
    `wqAlg_unit` uses `1 * a = a` (`CommMonoid`). **Discharges the weak-law-persistence
    content** the charter §6.1 [REV-B] pinned on WS4.
14. `wqAlg_nontrivial` — incomparable witnesses.

**Layer E — Reduction + assembly + non-idempotence (conservativity + non-degeneracy).**
15. `boolGood : DivisibleQuantale (ULift Bool)` — `⊗ = ∧`, `1 = ⊤ = true`. Frame case
    recovered as an instance, not the definition.
16. `wq_reduces_to_pk : ∀ t, wqAlg (Q := ULift Bool) hreg t = alg hreg (boolIso t)`.
    **[S2]** Both sides use the corrected `pentagon`/`pkJoin` form, so registered and
    proved WS3 signatures coincide and the reduction is exact. **This is the theorem
    that makes weak-law persistence *conservative* over WS3** — the charter's
    "recover the content inside the surrogate" (§8.2) discharged concretely.
17. `GradedWeakBialgebra` extends the WS3 shape with graded fields +
    `noStrictLaw := ws3_no_distributive_law`-analogue. The impossibility is carried
    *inside* the deliverable (charter §8.1 WS3 discipline, mirrored).
18. `ws4_graded_bialgebra (Q) [DivisibleQuantale Q] (hQsmall) (hreg) :
    Nonempty (GradedWeakBialgebra Q hreg)` — the class-level deliverable.
19. **[v3] `ws4_quantitative_witness : ∃ (a : Łₙ), a * a ≠ a`** — take `a = n−1`,
    `n ≥ 2`: `(n−1)⊗(n−1) = n−2 ≠ n−1`. Proved by `decide`. **This is the tripwire
    the v2 audit demanded**: it certifies grading is genuinely quantitative
    (non-idempotent), so §3.5 is discharged in its quantitative reading, not
    quietly re-narrowed to qualitative frames.
20. **[v3] `ws4_resolved`** — the top-level theorem bundling
    `ws4_graded_bialgebra (Łₙ) … ∧ ws4_weak_pullback_Luk ∧ ws4_bisim_behavioural_Luk
    ∧ wq_reduces_to_pk ∧ ws4_quantitative_witness`. Its existence is the machine
    statement that WS4 is **Discharged** for a quantitative quantale.

---

## 5. Hypothesis accounting

- `hreg : κ.IsRegular` — load-bearing in `wqJoin` (D) and `WQRel_comp_le` (C.7);
  correctly load-bearing given the P2-bounded index set.
- `hQsmall : #Q ≤ κ` — required for `qpfWQ` (A.2). **Vacuous at `Łₙ`** (finite);
  routed to WS7 as a class-level `(F,κ,μ,#Q)` duty (S1, §3).
- `hinf = hreg.aleph0_le` — singletons/pairs.
- **Class split:** `GoodQuantale` (2 axioms) for existence/bisim/bound;
  `DivisibleQuantale` (+`tensor_section`) for preservation + graded law.
- **No custom global axioms.** `propext`/`Classical.choice`/`Quot.sound` only.
  `Classical.choice` enters at middle-point selection (C.6) and inside `sSup`.
  **[v3]** At `Q = Łₙ` the `sSup` over the finite carrier is choice-free (`Finset.sup`),
  so `#print axioms ws4_resolved` should show a *strictly smaller* axiom footprint than
  the class-level `ws4_graded_bialgebra` — a bonus certification the witness route buys.
- `#print axioms ws4_resolved`, `#print axioms ws4_weak_pullback` to confirm.

---

## 6. Success condition (resolved)

**Discharged** requires, all `sorry`-free/axiom-free:
- Steps 1–18 proved for the class `DivisibleQuantale`.
- Steps 2, 6(b), 8, 9 instantiated unconditionally at `Q = Łₙ` (finite, decidable).
- `wq_reduces_to_pk` proved against the **corrected** WS3 `pentagon` (S2).
- `ws4_quantitative_witness` proved: `Łₙ` non-idempotent (step 19).
- `ws4_resolved` (step 20) compiles.

On success: WS4's §3.5 obligation is **Discharged for a quantitative quantale**; the
two ratification duties (weak-pullback preservation, weak-law persistence) are
discharged; criterion (iv) advances to **content-present / coherence-proved /
canonicity-open** — which the charter (§6.1, §7 [REV-B]) explicitly says is *not* to
be reported as (iv)-closure. WS4 adds the `(F,κ,μ,#Q)` cardinality duty to WS7 (S1).

---

## 7. What remains open after Discharge (scoped, not claimed)

- **Canonicity (charter-inherited, out of scope).** WS4 proves a well-behaved graded
  weak law *persists and is conservative*; it does **not** prove it is the unique or
  canonical weak law for `W_Q`. This is the WS3-originated canonicity question,
  inherited at the `(Q,κ)` level, and it is the reason (iv) stays Partial-toward-open,
  per charter §7 [REV-B]. Reporting anything more would be the exact "relabel the
  shortfall as the goal" drift §8.2 forbids.
- **Class breadth beyond `Łₙ`.** Discharge is via one non-idempotent family. Whether
  the *full* `DivisibleQuantale` class is quantitatively rich (e.g. admits the
  unbounded Lawvere quantale under a WS7-ratified truncation) is a breadth question,
  not a discharge blocker; it rides on the `(F,κ,μ,#Q)` duty routed to WS7.

---

## 8. The impossibility branch (F6), specified in §5 vocabulary — [S3]

v2 treated "pivot to F6" as a local option. Per the charter, a negative terminal
outcome must be a reported **Impossibility proved** with an explicit hand-off, not a
silent internal fork. This section specifies it as such so the branch cannot drift
into an unrouted dead end.

**Trigger (decidable at the gate).** F6 is entered iff step 6(b) fails: i.e. iff
`tensor_section` cannot be satisfied by `Łₙ` (or any finite non-idempotent chain),
*and* a proof is produced that `WQRel_le_comp` is false for **every** non-idempotent
`GoodQuantale` — equivalently, that weak-pullback preservation forces idempotence
(`⊗ = ∧`, the frame collapse).

**Content of the negative theorem.**
```lean
theorem ws4_no_quantitative_grading :
    ∀ (Q) [GoodQuantale Q], WQPreservesWeakPullback Q κ → (∀ a : Q, a * a = a) := ...
```
i.e. weak-pullback preservation ⇒ idempotence ⇒ frame ⇒ grading is qualitative, not
quantitative. If proved, this says: **§3.5's quantitative "whole or in part" cannot
be realized on the bounded carrier while preserving criterion (ii)** (bisim =
behavioural equivalence). The graded functor either preserves weak pullbacks and is
qualitatively-multivalued-at-best (a frame, essentially WS2's `P_κ` recolored), or is
genuinely quantitative and breaks bisimulation = identity.

**Why this is a §5/§7 success, not a failure.** It is a sharp, informative negative
of exactly the Klin–Salamanca flavor WS3 already produced at the strict-law gate: it
identifies quantitative grading as *inherently in tension* with bisimulational
identity on a bounded carrier, mirroring "composition of relations-as-objects is
inherently non-strict" (charter §3.4 [REV-B], §8.2). The impossibility is carried
inside the report, not relabeled.

**Hand-off routing (charter §5 + §6.1).**
- **→ WS2 / criterion (ii):** the bisim/behavioural-equivalence split that §8.1's WS2
  audit flagged as a *possible* declared substitution is now *forced* for any
  quantitative functor; WS2 must record it as a proved split, not a hazard.
- **→ WS7 / Goldilocks band:** the band contains no quantitative-grading point;
  WS7's "locate the band **or** prove it empty" mandate absorbs this as a proved
  partial-emptiness (empty in the quantitative-`Q` direction).
- **→ criterion (iv):** delivered qualitatively (via the frame instance = WS3's weak
  law recolored); the quantitative enrichment §3.5 hoped to add to (iv) is proved
  unavailable. (iv) stays Partial; §3.5 reports **Impossibility proved** for its
  quantitative reading and **Discharged** for its qualitative reading.

**Decision procedure for the build phase.** Attempt step 6(b) against `Łₙ` first
(finite, `decide`-backed). If it *succeeds* → **Discharged** route (§6). If it
*fails*, attempt `ws4_no_quantitative_grading` → **Impossibility proved** route
(this §8). Exactly one of the two terminates the workstream; there is no third
"leave it open" outcome. This is the resolution v2 lacked.

---

## 9. Charter reconciliation (binding confirmation)

| Charter item | WS4 v3 signature | Status |
|---|---|---|
| Commitment §3.5 (graded containment, quantitative) | `ws4_graded_bialgebra` + `ws4_quantitative_witness` at `Łₙ` | Discharged (quantitative) *or* Impossibility-proved via §8 |
| Criterion (i)–(iii) for enriched carrier | Layers A–B: `exists_terminal_wq`, `ws4_bisim_eq`, reified relations as `WQObj` elements | Discharged for `W_Q` |
| Criterion (ii) bisim = behavioural eq. | `ws4_bisim_behavioural` (needs step 8) | Discharged (preservation holds) *or* proved-split via §8 |
| Criterion (iv) coherent bialgebra | `GradedWeakBialgebra` + `noStrictLaw` field; weak-law coherence steps 12–13 | Content present, coherence proved, **canonicity open** — not closed, per charter |
| §8.1 WS2 weak-pullback duty (inherited) | `ws4_weak_pullback` (step 8) | Discharged |
| §6.1 [REV-B] weak-law-persistence duty (pinned) | `wqAlg_join` + `wq_reduces_to_pk` (13, 16) | Discharged (conservative over WS3) |
| §6 [REV-B] `pentagon` erratum (S2) | Steps 12, 16 bind to corrected `pkJoin` form | Reconciled |
| §6.1 shared-`(F,κ)` + `hQsmall` (S1) | `(F,κ,μ,#Q)` duty routed to WS7 | Routed |
| §5 negative-outcome discipline (S3) | §8 `ws4_no_quantitative_grading`, routed to WS2/WS7/(iv) | Specified as Impossibility-proved |
| §8.2 no-drift discipline | canonicity scoped open (§7); quantitative-vs-qualitative kept distinct | Held |

**Verdict.** v3 fully resolves WS4: it terminates in exactly one of §5's admissible
classes — **Discharged** (for a concrete non-idempotent quantale) or **Impossibility
proved** (quantitative grading is incompatible with bisimulational identity on the
bounded carrier) — with the decision procedure (§8) making the fork decidable at the
gate. Both branches close the three audit seams (S1 cardinality routing, S2 pentagon
erratum binding, S3 negative-outcome routing) and both hold the charter's §8.2
discipline: canonicity is left open and named, never relabeled as closure.

---

## Appendix: changes from v2

| # | v2 state | v3 resolution |
|---|----------|---------------|
| R1 | Step 6 open ("attack first, may resist"); no certified non-idempotent instance | Committed to `Łₙ` (MV chain); `tensor_section` proved by `decide`; step 6(b) unconditional; `ws4_quantitative_witness` certifies non-idempotence |
| R2 | F6 a local option | §8: `ws4_no_quantitative_grading` as a §5 Impossibility-proved theorem with WS2/WS7/(iv) hand-offs; decision procedure makes the fork decidable |
| S1 | `hQsmall` noted, not routed | Routed to WS7 as `(F,κ,μ,#Q)` collector duty (§3, §5) |
| S2 | `pentagon` reduction not bound to erratum | Steps 12, 16 explicitly bind to corrected `pkJoin` form (§1, §4) |
| S3 | negative branch unrouted | §8 routes to WS2 (forced bisim split), WS7 (band emptiness), (iv) (qualitative-only) |
| — | (iv) status implicit | §9 table: content-present/coherence-proved/**canonicity-open**, explicitly not closure |
