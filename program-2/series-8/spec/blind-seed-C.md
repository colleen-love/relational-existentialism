# Blind seed — Phase C (design review)

You are reviewing a set of Lean definitions and theorem signatures for internal coherence and non-vacuity. Judge ONLY what is written here. This is a DESIGN review: the code does not exist yet; assess whether each signature is coherent, non-vacuous, and whether the design as a whole meets the mechanical checks below.

## 1. The definitions under review

```
abbrev S : Type := Fin 3
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2

def attTri  : S → Finset S := fun x => if x = p0 then {p1} else if x = p1 then {p2} else {p0}
def attStar : S → Finset S := fun x => if x = p0 then {p1, p2} else {p0}

def knows (att : S → Finset S) (x y : S) : Prop := y ∈ att x

def incr (att : S → Finset S) (x y : S) : ℤ :=
  (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)

def recon (att : S → Finset S) (x y : S) : ℤ → ℤ := fun v => v + incr att x y

def valu (att : S → Finset S) : S → ℤ := fun y => incr att p0 y

def hol (att : S → Finset S) (x y z : S) : ℤ := incr att x y + incr att y z + incr att z x

def IsSection (att : S → Finset S) (s : S → ℤ) : Prop := ∀ x y, y ∈ att x → s y = s x + incr att x y

inductive Outcome | frustrated | gluable | shapeDrawn | pairwiseOnly | disconnected | partial' deriving DecidableEq

def verdict (nonTrivial pairwiseCoherent manyBody modelDerived frustReachable glueReachable : Bool) : Outcome :=
  if !nonTrivial then Outcome.disconnected
  else if !manyBody then Outcome.pairwiseOnly
  else if !pairwiseCoherent then Outcome.partial'
  else if !modelDerived then Outcome.partial'
  else if frustReachable && glueReachable then Outcome.frustrated
  else if glueReachable && !frustReachable then Outcome.gluable
  else if !glueReachable && !frustReachable then Outcome.shapeDrawn
  else Outcome.partial'
```

## 2. The theorem signatures under review

```
-- WS1
theorem ws1_nontrivial :
    valu attTri p1 ≠ valu attTri p2
  ∧ incr attTri p0 p2 ≠ incr attTri p1 p2

-- WS2
theorem ws2_pairwise_coherent (att : S → Finset S) (x y : S) (v : ℤ) :
    recon att y x (recon att x y v) = v
theorem ws2_reconciliation_nontrivial : recon attTri p0 p1 0 ≠ 0
-- supporting bridge to the imported single-edge datum (P2S3.Valuation / P2S3.Converges₂):
def valPop (att : S → Finset S) : P2S3.Valuation S ℤ := ⟨valu att, fun x y => recon att x y⟩
theorem ws2_bridge_converges (att : S → Finset S) (x y : S) :
    P2S3.Converges₂ (valPop att) x y ↔ valu att x + incr att x y = valu att y

-- WS3
theorem ws3_two_body_trivial (att : S → Finset S) (x y : S) :
    incr att x y + incr att y x = 0 ∧ hol att x y x = 0 ∧ hol att x x y = 0
theorem ws3_holonomy_model_derived :
    (∀ (att : S → Finset S) (x y : S),
        incr att x y = (if knows att x y then 1 else 0) - (if knows att y x then 1 else 0))
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y)

-- WS4
theorem ws4_frustrated_reachable :
    hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s
theorem ws4_gluable_reachable :
    hol attStar p0 p1 p2 = 0 ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)

-- WS5
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.frustrated
theorem ws5_verdict_discriminates :
    verdict false true true true true true  = Outcome.disconnected
  ∧ verdict true true false true true true  = Outcome.pairwiseOnly
  ∧ verdict true false true true true true  = Outcome.partial'
  ∧ verdict true true true true true true   = Outcome.frustrated
  ∧ verdict true true true true false true  = Outcome.gluable
  ∧ verdict true true true true false false = Outcome.shapeDrawn
theorem ws5_flags_justified :
    (valu attTri p1 ≠ valu attTri p2)
  ∧ (∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v)
  ∧ (∀ att : S → Finset S, ∀ x y : S, incr att x y + incr att y x = 0)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (hol attTri p0 p1 p2 = 3 ∧ ¬ ∃ s : S → ℤ, IsSection attTri s)
  ∧ (∃ s : S → ℤ, IsSection attStar s)
theorem ws5_audit_no_global :
    (¬ ∃ s : S → ℤ, IsSection attTri s)
  ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)
  ∧ (verdict true true true true false true = Outcome.gluable)
theorem ws5_audit_fork_genuine :
    (hol attTri p0 p1 p2 = 3) ∧ (hol attStar p0 p1 p2 = 0) ∧ (valu attTri p1 ≠ valu attTri p2)
theorem ws5_audit_many_body :
    (∀ att : S → Finset S, ∀ x y : S, hol att x y x = 0)
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) → ∀ x y z : S, hol att x y z = 0)
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y)
theorem ws5_audit_coherence_pervasive :
    ∀ (att : S → Finset S) (x y : S) (v : ℤ), recon att y x (recon att x y v) = v
theorem ws5_audit_names_not_terms : True
```

## 3. Success criteria (restated as mechanical requirements)

1. `valu attTri` is a non-constant `S → ℤ`, and `incr` is not symmetric across two source vertices (`incr att p0 p2 ≠ incr att p1 p2` on `attTri`).
2. `recon att y x ∘ recon att x y = id` for ALL `att, x, y` (pervasive), and `recon` is not the identity map on `attTri` (non-vacuous).
3. `hol` vanishes for every 2-vertex configuration (`hol att x y x = 0`, `incr att x y + incr att y x = 0`, for all `att`), and vanishes identically when `att` is symmetric; and `attTri` is genuinely directed.
4. There is a `att`, `x y z` with `hol = 3 ≠ 0` and no `s : S → ℤ` satisfying `IsSection` (frustrated), AND a `att` with `hol = 0` and an `s` satisfying `IsSection` (gluable).
5. `verdict` is a total `Bool⁶ → Outcome`; `verdict true true true true true true = frustrated`; the function reaches all six outcomes; and the six input flags are exactly the WS1–WS4 facts above (none hand-set).

## 4. The audit checks (mechanical — verify each against the signatures)

- **(a) No global assignment forced.** No theorem asserts `∃ s, IsSection attTri s` (the frustrated carrier). A section is asserted only for `attStar`. `gluable` is returned by `verdict` only under `glueReachable && !frustReachable`; check the honest flag row (`ws5_flags_justified` sets `frustReachable = true`) does NOT trigger it.
- **(b) The fork is not by fiat.** BOTH `hol attTri … = 3` and `hol attStar … = 0` are provable from the SAME `hol`/`incr` definitions; `valu` is non-trivial; `verdict` discriminates.
- **(c) The obstruction is a genuine many-body cocycle, not a single edge, not import-ness, not bolted on.** Check: (i) `hol` vanishes for two selves; (ii) `hol` vanishes identically when `att` is symmetric, so the obstruction depends on the DIRECTEDNESS of `att` and is a function of `att` alone; (iii) NO signature mentions `Recoverable`/`plainOf`/`AttentionDistinguishes` (import-ness); (iv) `incr` is defined purely from `∈ att`, with no free integer parameter and no `Finset.card`/`insert` counter disconnected from `incr`.
- **(d) Local coherence is pervasive.** `ws2_pairwise_coherent` / `ws5_audit_coherence_pervasive` are `∀`-quantified over `att, x, y, v`.
- **(e) Names-not-terms.** Grep the definitions/theorems for identifiers named as a whole word: `good`, `common`, `value`, `justice`, `consensus`, `ethics`, `self`, `import`, `god`, `love`, `compass`. There must be NONE as a proof term / definition / obligation name. (Note: `valu` and `IsSection` are NOT the whole words `value`/`self`; judge whole-word tokens honestly.)

## 5. Strip test

For each payoff, delete any interpretive gloss and check the bare statement still stands as a fact about `attTri`/`attStar`/`incr`/`hol`/`IsSection`:
- WS1 → an integer function on `Fin 3` takes two distinct values; a signed adjacency increment is not symmetric across two sources.
- WS2 → a translation composed with its reverse is the identity, pervasively; the translation is non-identity on the ring; the edge datum is `P2S3.Converges₂`.
- WS3 → a signed directed-adjacency sum vanishes for 2-cycles and for symmetric adjacency; the ring is genuinely directed.
- WS4 → the signed increment sum around a directed 3-ring is `3`, so no `ℤ`-labelling closes it; around the mutual star it is `0` and the constant labelling closes it.
- WS5 → a total `Bool⁶ → Outcome` computes `frustrated` on the earned flags and discriminates.

Report any payoff whose content does NOT survive its strip.

## 6. Grading rubric

- **SERIOUS:** a signature is vacuous or self-contradictory; the fork is a fiat; the obstruction rests on a single edge or on import-ness or on a counter disconnected from `incr`; a global section over `attTri` is asserted; a name is a forbidden term; the verdict is hand-set rather than computed from earned flags; or a success criterion is silently unmet.
- **REAL:** a genuine gap correctly labelled (an over-strong name, an assumed-and-returned hypothesis, a signature contentful but weaker than its heading claims).
- **COSMETIC / ACCEPTABLE:** a naming nit or nominal overclaim.

Return a structured list of findings, each with a stable ID (`Cn-Sm`), a grade, the exact location (theorem/def name), and the defect. If you find nothing SERIOUS, say so explicitly.
