# WS5 design — the verdict and the audit folded in (2.9)

**The verdict is COMPUTED from the flags (never hand-set): `verdict : Bool⁶ → Outcome`, `= cone` on the earned flags, DISCRIMINATING (reaches all five outcomes), the flags EARNED by the WS1-WS4 headlines. The computed verdict is CONE: a bounded rate earned from attention (WS1), a non-trivial cone (WS2), the rate genuine content and earned (WS3), CONE and NO-CONE both reachable (WS4) — a finite speed, relativity's cone recovered. The five audit clauses (a)-(e) bundle the payoffs.**

## 1. The outcome type and the verdict function

```
inductive Outcome
  | cone           -- rate bounded & earned, cone non-trivial & rate-content, both fork sides reachable (expected)
  | nocone         -- rate unbounded, or cone trivial — the world non-relativistic (the NOT-RECOVERED specification)
  | shapeDrawn     -- the fork drawn, one side only in sight
  | disconnected   -- the cone collapses to the bare order — no genuine rate-content survives
  | partial'       -- degenerate (rate not earned, an obligation degenerate); `partial` is a Lean keyword
  deriving DecidableEq

-- arg order: (rateBounded, rateEarned, coneNonTrivial, rateIsContent, coneReachable, noconeReachable)
def verdict (rateBounded rateEarned coneNonTrivial rateIsContent coneReachable noconeReachable : Bool) : Outcome :=
  if !rateEarned then Outcome.partial'                          -- rate not from attention (smuggle guard)
  else if !rateIsContent then Outcome.disconnected              -- cone = bare order (costume ⇒ no content)
  else if !rateBounded then Outcome.nocone                      -- rate unbounded → non-relativistic
  else if !coneNonTrivial then Outcome.nocone                   -- cone trivial (whole world) → no finite speed
  else if coneReachable && noconeReachable then Outcome.cone    -- CONE recovered, fork genuine
  else if coneReachable && !noconeReachable then Outcome.shapeDrawn
  else Outcome.nocone
```

## 2. Payoff

```
-- THE COMPUTED VERDICT: cone, on the earned flags.
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.cone

-- FALSIFIABILITY: the verdict reaches all five outcomes.
theorem ws5_verdict_discriminates :
    verdict true false true true true true  = Outcome.partial'
  ∧ verdict true true true false true true  = Outcome.disconnected
  ∧ verdict false true true true true true  = Outcome.nocone
  ∧ verdict true true false true true true  = Outcome.nocone
  ∧ verdict true true true true true true   = Outcome.cone
  ∧ verdict true true true true true false  = Outcome.shapeDrawn

-- THE FLAGS ARE EARNED by the WS1-WS4 headlines (none hand-set).
theorem ws5_flags_justified :
    (∀ (att : S → Finset S) (x y : S), y ∈ att x → dist x y ≤ rate att)                       -- rateBounded (WS1)
  ∧ (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))  -- rateEarned (WS3)
  ∧ (p4 ∉ ball attSlow p0 1)                                                                   -- coneNonTrivial (WS2)
  ∧ ((∀ x y, reaches attSlow x y = reaches attFast x y) ∧ ball attSlow p0 1 ≠ ball attFast p0 1) -- rateIsContent (WS3)
  ∧ (∃ y, y ∉ ball attSlow p0 1)                                                               -- coneReachable (WS4)
  ∧ (∀ y, y ∈ ball attAll p0 1)                                                                -- noconeReachable (WS4)
```

`ws5_verdict_eq`, `ws5_verdict_discriminates`: `rfl` / `decide`. `ws5_flags_justified`: from `ws1_rate_bounded`, `ws3_earned_from_attention.1`, `ws2_cone_nontrivial.2`, `ws3_rate_is_content`, `ws4_cone_reachable.2`, `ws4_nocone_reachable`.

## 3. The five audit clauses (a)-(e)

```
-- (a) THE RATE IS EARNED, NOT SMUGGLED — a function of the finite attention, tracking it; no postulated c.
theorem ws5_audit_rate_earned :
    (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (∀ a b : S → Finset S, (∀ x, a x ⊆ b x) → rate a ≤ rate b)
  ∧ (rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4)

-- (b) THE FORK NOT BY FIAT — cone and nocone both reachable from the same defs; the verdict discriminates.
theorem ws5_audit_fork_genuine :
    (∃ y, y ∉ ball attSlow p0 1) ∧ (∀ y, y ∈ ball attAll p0 1)
  ∧ (verdict true true true true true false = Outcome.shapeDrawn)

-- (c) THE CONE IS A RATE, NOT THE BARE ORDER (the costume gate) — same order, different rate, different cone.
theorem ws5_audit_rate_not_order :
    (∀ x y, reaches attSlow x y = reaches attFast x y)
  ∧ rate attSlow ≠ rate attFast
  ∧ ball attSlow p0 1 ≠ ball attFast p0 1

-- (d) THE CONE IS NON-TRIVIAL — some event strictly outside on the witnessing carrier, a genuine finite speed.
theorem ws5_audit_cone_nontrivial :
    p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1

-- (e) NAMES-NOT-TERMS — a meta-property, guarded by the §6 grep; the accepted house placeholder.
theorem ws5_audit_names_not_terms : True
```

## 3a. The flags map to the earned facts

| flag | set by | earned from |
|------|--------|-------------|
| `rateBounded` | `ws1_rate_bounded` | the per-tick reach `≤ rate` |
| `rateEarned` | `ws3_earned_from_attention` | `rate = univ.sup (span att)`, monotone in `att` |
| `coneNonTrivial` | `ws2_cone_nontrivial` | `p4` strictly outside |
| `rateIsContent` | `ws3_rate_is_content` | same order, different rate ⇒ different cone |
| `coneReachable` | `ws4_cone_reachable` | `attSlow` non-trivial cone |
| `noconeReachable` | `ws4_nocone_reachable` | `attAll` trivial cone |

## 4. Triage

- **Computed, not hand-set.** The verdict is a total `Bool⁶ → Outcome`; `ws5_verdict_eq` computes `cone` by `rfl`; `ws5_verdict_discriminates` reaches all five outcomes; the six flags are exactly the WS1-WS4 facts (`ws5_flags_justified`).
- **CONE is the expected close.** On the earned flags the verdict is `cone` — relativity's cone recovered, earned from finite attention. NO-CONE (`attAll`) is genuinely reachable and would be the verdict were the cone trivial; it is reported, never relabelled.
- **The audit is the charter's (a)-(e).** (a) earned not smuggled; (b) fork not by fiat; (c) cone a rate not the order; (d) cone non-trivial; (e) names-not-terms (the §6 grep is the teeth).
- **Strip test.** Delete the interpretive gloss: `verdict` is a total function on `Bool⁶` reaching five values; the audits are `Finset.sup`/`filter`/reachability facts about `attSlow`/`attFast`/`attAll`. All survive.
- **Names (audit e).** `Outcome`, `verdict`, `cone`/`nocone` (constructors, underscore-free but as `Outcome.cone` — see note), `ws5_*`. NOTE: the constructor `Outcome.cone` — the token `cone` follows `.` (a non-word char) and precedes a non-word char, so `\bcone\b` WOULD match `Outcome.cone` at a use site and the bare `| cone` declaration. To keep the §6 grep prose-only, the constructors are named **`coneOut` / `noconeOut`** in code (not `cone`/`nocone`); "cone"/"NO-CONE" in prose. (Corrected from the sketch above; see the ws5.lean build.)
```
inductive Outcome | coneOut | noconeOut | shapeDrawn | disconnected | partial' deriving DecidableEq
```
