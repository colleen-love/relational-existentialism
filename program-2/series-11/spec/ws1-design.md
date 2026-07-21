# WS1 design — the model-derived sign (the ground)

**Target: DEFINE the sign `amp` read off Series 2.8's built holonomy, and prove it genuinely SIGNED (takes both `+1` and `-1` on the carriers). A function of the built `incr`/`hol` alone, no complex number. If no signed amplitude survives (the holonomy always even), the pre-registered obstruction is toward ADDITIVE-ONLY / DISCONNECTED.**

## Candidates and paper triage

| candidate | signed? | earned off `hol`? | verdict |
|---|---|---|---|
| `amp n = if n % 2 = 0 then 1 else -1` (parity sign of the holonomy) | YES (`-1` on odd `hol=3`, `+1` on even `hol=0`) | YES (function of `hol` alone) | **WIN** |
| `incr att x y` itself (`{-1,0,+1}`) | takes `0` too, not unit-modulus | earned | rejected (WS3 needs unit modulus; see de-risking §Rejected) |
| bolted-on `e^{iθ}`, `θ` free | — | NO (not read off model) | rejected (the smuggle) |
| `i^n : ℂ` (complex phase) | — | earned but complex | rejected (overclaims scope; forward-note) |

## The winning construction (typed signatures)

```
def amp (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1
def directAmp : ℤ := amp 0                                    -- +1
def loopAmp (att : S → Finset S) : ℤ := amp (P2S8.hol att P2S8.p0 P2S8.p1 P2S8.p2)

-- helper facts on the sign
theorem amp_values (n : ℤ) : amp n = 1 ∨ amp n = -1
theorem amp_sq (n : ℤ) : amp n ^ 2 = 1

-- THE PAYOFF: the sign is genuinely SIGNED — takes both values on the S2.8 carriers.
theorem ws1_amp_signed :
    loopAmp P2S8.attTri = -1 ∧ loopAmp P2S8.attStar = 1
```

## Outcome classes
- **signed (WIN):** `amp` takes both `+1` and `-1` → a real sign to cancel. Toward INTERFERING.
- **DISCONNECTED:** `amp` constant (no sign) → no cancellation possible. (Not reached: `hol attTri = 3` odd, `hol attStar = 0` even.)

## Strip test
Delete "phase"/"amplitude": the statement is "a `±1`-valued function of `hol` taking both values on the two carriers." A bare parity fact on the built holonomy. Survives.

## Audit clauses touched
- (a) earned: `amp` is a function of `hol` (definitional). (d) scope: `amp_values` — a real `±1`, not complex. (b) non-trivial: `ws1_amp_signed` takes both values.
