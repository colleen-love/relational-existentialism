# WS3 design — interference, not accumulation (the anti-costume core)

**Target: DEFINE the WEIGHT of a combined contribution as its squared modulus, and prove genuine DESTRUCTIVE INTERFERENCE — a combined weight STRICTLY below the sum of the parts (`combinedWeight attTri = 0 < 2 = partsWeight attTri`) — the quantum signature no classical probability shows. And prove the sign EARNED (a function of the built `incr`/`hol`, no complex number). This WS carries the series' risk: the strict inequality is the whole content; the earnedness is the sharpest no-smuggling test in the program.**

## The construction (typed signatures)

```
def combinedWeight (att : S → Finset S) : ℤ := (directAmp + loopAmp att) ^ 2
def partsWeight    (att : S → Finset S) : ℤ := directAmp ^ 2 + (loopAmp att) ^ 2

-- THE PAYOFF: destructive interference on the frustrated cycle — combined weight strictly below parts.
theorem ws3_destructive :
    combinedWeight P2S8.attTri < partsWeight P2S8.attTri            -- 0 < 2

-- The anti-costume theorem: destructive IFF the signs cancel (each sign has unit weight, so parts = 2,
-- combined ∈ {0,4}); hence destructive is NOT relabelled addition, and happens exactly on odd relative holonomy.
theorem ws3_destructive_iff (m n : ℤ) :
    (amp m + amp n) ^ 2 < amp m ^ 2 + amp n ^ 2  ↔  amp m + amp n = 0

-- THE PAYOFF: the sign is EARNED — read off the built holonomy, no complex number (the no-smuggling gate).
theorem ws3_amp_earned :
    (∀ att : S → Finset S, loopAmp att = amp (P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2))
  ∧ (∀ (att : S → Finset S) (x y z : S),
        P2S8.hol att x y z = P2S8.incr att x y + P2S8.incr att y z + P2S8.incr att z x)
  ∧ (∀ (att : S → Finset S) (x y : S),
        P2S8.incr att x y = (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0))
```

## Paper check
- `combinedWeight attTri = (1 + (-1))^2 = 0`; `partsWeight attTri = 1^2 + (-1)^2 = 2`; `0 < 2`. ✓ (`norm_num` after WS1 sign rewrites.)
- `ws3_destructive_iff`: `amp m, amp n ∈ {±1}` (WS1 `amp_values`), so `amp m^2 = amp n^2 = 1`, RHS `= 2`; `amp m + amp n ∈ {-2,0,2}`, LHS `= (amp m + amp n)^2 ∈ {0,4}`. `(…)^2 < 2 ↔ (…)^2 = 0 ↔ amp m + amp n = 0`. (`amp_values`, `nlinarith`/`omega`.)
- `ws3_amp_earned`: three `rfl`/definitional facts — `loopAmp` unfolds to `amp (hol …)`; `hol` to the `incr`-sum; `incr` to the signed `knows` difference. No complex number anywhere.

## Outcome classes
- **destructive (WIN):** `combinedWeight attTri < partsWeight attTri` strictly → genuine interference. Toward INTERFERING.
- **ADDITIVE-ONLY:** if no carrier gave `combined < parts` → distinction only accumulates, the world classical. (Not reached: `attTri` gives `0 < 2`.)

## Strip test
Delete "phase"/"amplitude"/"interference"/"quantum": `ws3_destructive` is "`(a+b)^2 < a^2 + b^2` for the signs `a = directAmp`, `b = loopAmp attTri` read off the built holonomy"; the strict inequality is the whole content. A bare squared-sum inequality on the built holonomy. Survives.

## Audit clauses touched
- (a) earned not smuggled: `ws3_amp_earned` — the sign is a function of `hol`/`incr`, no complex number. THE clause the series lives on.
- (c) destructive not additive: `ws3_destructive` strict `<`; `ws3_destructive_iff` proves it is not a relabelled addition (destructive iff the signs cancel, impossible for a classical mixture where weights add).
