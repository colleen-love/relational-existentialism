# WS1 — The valuation and `Converges₂` (typed, never evaluated). Design.

**Target (charter §2-WS1).** Define the VALUATION (a per-perspective valuation, typed, held as a quantified
parameter, never selected or read off) and `Converges₂` (the self's valuation carried to the other coheres with
the other's own). Prove it well-typed and non-vacuous, and prove the discipline: every theorem quantified over all
valuations, none evaluated (`ws1_no_orientation_evaluated`). This is the primitive.

## 1. Candidates

- **(A) Evaluated valuation.** A canonical `val : RCar → Or` fixed in the core. REJECTED: the central sin (audit
  (a)); a canonical valuation anywhere in the core, even leaking into a `∀`-obligation, is Series 12's feeling-side
  violation. The valuation must be a quantified parameter, witnesses only in existentials.
- **(B) `Converges₂` as `True`/`False`/reflexive.** `Converges₂ c x y := True`, or `:= (c.val x = c.val x)`.
  REJECTED: fails the strip test at the definition (decides the direction by fiat; the fork would be a tautology).
  `Converges₂` must be a genuine equation in `Or` depending on `c` AND on the target valuation.
- **(C, WINNER) A raising equation, `c.raise x y (c.val x) = c.val y`.** The valuation at `x`, raised toward `y`,
  agrees with the valuation at `y`. Depends on `c` genuinely; two-sided free (some `c` converge, some do not); the
  faithful sub-class makes it exactly `val x = val y`. This is Series 12's corrected `Converges` (PR2-S1),
  rebuilt fresh on the S2 pair with neutral names.

## 2. Triage (paper)

| Criterion | (C) verdict |
|---|---|
| Non-triviality | `Converges₂` is neither `True` nor `False`: `ws1_no_orientation_evaluated` exhibits `c₁` converging and `c₂` not, at `(slf, oth)`. |
| Strip test | Strips to a bare equation `raise x y (val x) = val y` in `Or`; under `Faithful₂` to `val x = val y`. No word load-bearing. |
| Audit (a) | No canonical valuation: `val`/`raise` are structure FIELDS quantified over `c`; witnesses `cUnif`/`cDiss` live only in existentials (WS4). |
| Audit (e) | `Valuation`/`val`/`raise`/`Converges₂`/`Faithful₂` carry no forbidden content-name (`\borientation\b`/`\bconvergence\b`/`\bcompass\b` do not match). |

## 3. Winning construction (typed signatures)

```lean
/-- The per-perspective valuation. `Or` an EXOGENOUS space the mathematics never inhabits canonically;
    `val` the per-relatum valuation, `raise` the per-edge raising. Both fields arbitrary; every theorem
    quantifies over `(Or)` and `(c : Valuation …)`. -/
structure Valuation (X Or : Type) where
  val   : X → Or
  raise : X → X → Or → Or

/-- `Converges₂ c x y`: the valuation at `x`, raised toward `y`, agrees with the valuation at `y`. A genuine
    equation in `Or`, depending on `c`; instantiated at `(slf, oth)`. -/
def Converges₂ {X Or : Type} (c : Valuation X Or) (x y : X) : Prop :=
  c.raise x y (c.val x) = c.val y

/-- The FAITHFUL class (the structural constraint, anti-PR1-S1): the raising carries the valuation unchanged. -/
def Faithful₂ {X Or : Type} (c : Valuation X Or) : Prop := ∀ x y : X, c.raise x y = id

/-- Under `Faithful₂`, convergence is exactly valuation-coherence. -/
theorem faithful_converges_iff {X Or : Type} (c : Valuation X Or) (hf : Faithful₂ c) (x y : X) :
    Converges₂ c x y ↔ c.val x = c.val y

/-- **WS1 — TYPED AND NON-VACUOUS.** A faithful valuation converging at `(slf, oth)` exists. -/
theorem ws1_converges_typed (hinf : ℵ₀ ≤ κ) :
    ∃ c : Valuation RCar (ULift.{0} Bool), Faithful₂ c ∧ Converges₂ c slf oth

/-- **WS1 — NO VALUATION EVALUATED (the strip test at the definition, audit (a)).** `Converges₂` fixes no
    valuation: a faithful valuation under which it holds AND a faithful valuation under which it fails both
    exist at `(slf, oth)`, so the relation is two-sided free (neither `True` nor `False` nor reflexive), and
    the core reads off no canonical valuation. -/
theorem ws1_no_orientation_evaluated (hinf : ℵ₀ ≤ κ) :
    ∃ c₁ c₂ : Valuation RCar (ULift.{0} Bool),
        Faithful₂ c₁ ∧ Faithful₂ c₂ ∧ Converges₂ c₁ slf oth ∧ ¬ Converges₂ c₂ slf oth
```

The witnesses are `cUnif := ⟨fun _ => ⟨true⟩, fun _ _ o => o⟩` (converges, `rfl`) and `cDiss := ⟨fun z => if z =
slf then ⟨true⟩ else ⟨false⟩, fun _ _ o => o⟩` (fails, `decide`: `val slf = ⟨true⟩ ≠ ⟨false⟩ = val oth`), both
`Faithful₂` by `rfl`. Defined in WS4 (their canonical home, shared with the fork); WS1 states the existentials.

## 4. Outcome classes

- **shapeDrawn contribution:** `Converges₂` typed and two-sided free (this WS).
- **disconnected:** if `Converges₂` could not be typed without evaluating a valuation (it can — (C)), WS1 fails
  and the verdict is `disconnected`. Pre-registered, not reached here.

## 5. Strip-test annotation

`ws1_no_orientation_evaluated` strips (delete "valuation"/"convergence") to: "there exist `c₁`, `c₂` with identity
raising such that `c₁.val slf = c₁.val oth` and `c₂.val slf ≠ c₂.val oth`" — a bare statement that the field
`val` is free to agree or disagree on `slf`, `oth`. Survives. No word is load-bearing.
