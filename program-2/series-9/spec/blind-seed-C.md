# Blind seed — Phase C (design review)

You are reviewing a set of Lean 4 (Mathlib) definitions and theorem signatures for internal coherence and non-vacuity. Judge ONLY what is written here. This is a DESIGN review: the code does not exist yet; assess whether each signature is coherent, non-vacuous, provable in principle from the definitions, and whether the design as a whole meets the mechanical checks below. The carrier `S = Fin 5` is a small finite type; assume the imported `P2S0.knows att x y := y ∈ att x` (`att : S → Finset S`).

## 1. The definitions under review

```
abbrev S : Type := Fin 5
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2 ; def p3 : S := 3 ; def p4 : S := 4

def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y   -- = (y ∈ att x)

-- a fixed lateral (spatial) metric, attention-independent
def dist (x y : S) : ℕ := Nat.dist x.val y.val                          -- = |x.val - y.val|

-- the per-tick reach and the rate, read off the attention Finset
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)

-- the rate-bounded ball (the "cone")
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)

-- decidable bounded reachability (the causal order)
def reachWithin (att : S → Finset S) : ℕ → S → S → Bool
  | 0,     x, y => x == y
  | (n+1), x, y => (x == y) || (att x).any (fun z => reachWithin att n z y)
def reaches (att : S → Finset S) (x y : S) : Bool := reachWithin att (Fintype.card S) x y

def attSlow : S → Finset S := fun x =>
  if x = 0 then {1} else if x = 1 then {2} else if x = 2 then {3} else if x = 3 then {4} else ∅
def attFast : S → Finset S := fun x =>
  if x = 0 then {1,2} else if x = 1 then {2,3} else if x = 2 then {3,4} else if x = 3 then {4} else ∅
def attAll : S → Finset S := fun _ => {0,1,2,3,4}

inductive Outcome | coneOut | noconeOut | shapeDrawn | disconnected | partial' deriving DecidableEq

-- arg order: (rateBounded, rateEarned, coneNonTrivial, rateIsContent, coneReachable, noconeReachable)
def verdict (rateBounded rateEarned coneNonTrivial rateIsContent coneReachable noconeReachable : Bool) : Outcome :=
  if !rateEarned then Outcome.partial'
  else if !rateIsContent then Outcome.disconnected
  else if !rateBounded then Outcome.noconeOut
  else if !coneNonTrivial then Outcome.noconeOut
  else if coneReachable && noconeReachable then Outcome.coneOut
  else if coneReachable && !noconeReachable then Outcome.shapeDrawn
  else Outcome.noconeOut
```

## 2. The theorem signatures under review

```
-- WS1 (the ground): the rate is bounded, earned from attention, tracks it
theorem ws1_rate_bounded (att : S → Finset S) : ∀ x y, y ∈ att x → dist x y ≤ rate att
theorem ws1_rate_earned_from_knows (att : S → Finset S) (x y : S) : knows att x y → dist x y ≤ rate att
theorem ws1_rate_monotone (a b : S → Finset S) (h : ∀ x, a x ⊆ b x) : rate a ≤ rate b
theorem ws1_rate_tracks_attention : rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4

-- WS2: the cone is the rate-bounded set, and non-trivial
theorem ws2_cone (att : S → Finset S) (x y : S) (depth : ℕ) :
    y ∈ ball att x depth ↔ dist x y ≤ rate att * depth
theorem ws2_cone_nontrivial : p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1

-- WS3 (anti-costume): same order, different rate, different cone; the rate earned
theorem ws3_rate_is_content :
    (∀ x y, reaches attSlow x y = reaches attFast x y)
  ∧ rate attSlow ≠ rate attFast
  ∧ ball attSlow p0 1 ≠ ball attFast p0 1
theorem ws3_earned_from_attention :
    (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (∀ a b : S → Finset S, (∀ x, a x ⊆ b x) → rate a ≤ rate b)

-- WS4 (the fork): CONE and NO-CONE both reachable
theorem ws4_cone_reachable : rate attSlow = 1 ∧ (∃ y, y ∉ ball attSlow p0 1)
theorem ws4_nocone_reachable : ∀ y, y ∈ ball attAll p0 1
theorem ws4_nocone_trivial : ball attAll p0 1 = Finset.univ

-- WS5: verdict + audit
theorem ws5_verdict_eq : verdict true true true true true true = Outcome.coneOut
theorem ws5_verdict_discriminates :
    verdict true false true true true true  = Outcome.partial'
  ∧ verdict true true true false true true  = Outcome.disconnected
  ∧ verdict false true true true true true  = Outcome.noconeOut
  ∧ verdict true true false true true true  = Outcome.noconeOut
  ∧ verdict true true true true true true   = Outcome.coneOut
  ∧ verdict true true true true true false  = Outcome.shapeDrawn
theorem ws5_flags_justified :
    (∀ (att : S → Finset S) (x y : S), y ∈ att x → dist x y ≤ rate att)
  ∧ (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (p4 ∉ ball attSlow p0 1)
  ∧ ((∀ x y, reaches attSlow x y = reaches attFast x y) ∧ ball attSlow p0 1 ≠ ball attFast p0 1)
  ∧ (∃ y, y ∉ ball attSlow p0 1)
  ∧ (∀ y, y ∈ ball attAll p0 1)
theorem ws5_audit_rate_earned :
    (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (∀ a b : S → Finset S, (∀ x, a x ⊆ b x) → rate a ≤ rate b)
  ∧ (rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4)
theorem ws5_audit_fork_genuine :
    (∃ y, y ∉ ball attSlow p0 1) ∧ (∀ y, y ∈ ball attAll p0 1)
  ∧ (verdict true true true true true false = Outcome.shapeDrawn)
theorem ws5_audit_rate_not_order :
    (∀ x y, reaches attSlow x y = reaches attFast x y)
  ∧ rate attSlow ≠ rate attFast
  ∧ ball attSlow p0 1 ≠ ball attFast p0 1
theorem ws5_audit_cone_nontrivial : p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1
theorem ws5_audit_names_not_terms : True
```

## 3. Success criteria (restated as mechanical requirements)

1. `rate att` is a `Finset.sup` over `att` (a function of the attention, no free numeric parameter); `ws1_rate_bounded` shows it bounds `dist x y` for every attended `y ∈ att x`; `ws1_rate_monotone` shows it is monotone in the attention.
2. `ball att x depth = {y | dist x y ≤ rate att * depth}` (the rate-bounded set), and it is non-trivial on `attSlow` (`p1` inside, `p4` strictly outside at depth 1).
3. `attSlow` and `attFast` have equal `reaches` (same causal order) but `rate attSlow ≠ rate attFast` and `ball attSlow p0 1 ≠ ball attFast p0 1` (the cone is not recoverable from the order).
4. There is a carrier with a non-trivial cone (`∃ y ∉ ball attSlow p0 1`) AND a carrier whose cone is everything (`∀ y ∈ ball attAll p0 1`).
5. `verdict` is a total `Bool⁶ → Outcome`; `verdict true true true true true true = coneOut`; the function reaches all five outcomes; and the six flags are exactly the WS1-WS4 facts above (none hand-set).

## 4. The audit checks (mechanical — verify each against the signatures)

- **(a) THE RATE IS EARNED, NOT SMUGGLED (press hardest here).** `rate` must be a `Finset.sup` over the attention `att` with NO postulated numeral: check `rate att = univ.sup (fun x => (att x).sup (fun y => dist x y))` (definitional) and that it is monotone in `att` (`ws1_rate_monotone`, `rate attSlow = 1 < 2 = rate attFast < 4 = rate attAll`). Is there any hidden constant `c` added to `ball`/`rate` independent of `att`? If the rate does not fall out of `att`, that is SERIOUS.
- **(c) THE CONE IS A RATE, NOT THE BARE ORDER (the costume gate).** Check that `attSlow`/`attFast` have the SAME `reaches` yet DIFFERENT `ball … p0 1`. If the "cone" could be rewritten as `{y | reaches att x y}` (the bare order) with no rate content, it would be equal on the two carriers, contradicting `ws3_rate_is_content`. Confirm the cone genuinely depends on `rate` (hence on `att`), not only on reachability.
- **(d) THE CONE IS NON-TRIVIAL.** Some event strictly outside on the witnessing carrier: `p4 ∉ ball attSlow p0 1`. A cone equal to `univ` (as on `attAll`) is the NO-CONE pole, never claimed to be a cone.
- **(b) THE FORK IS NOT BY FIAT.** BOTH `∃ y ∉ ball attSlow p0 1` and `∀ y ∈ ball attAll p0 1` from the SAME `ball`/`rate`/`dist`; `verdict` discriminates.
- **(e) NAMES-NOT-TERMS.** Grep the definitions/theorems for identifiers named as a whole word (`\b…\b`, where `_` is a word character): `light`, `cone`, `speed`, `relativity`, `spacetime`, `self`, `import`, `god`, `compass`. There must be NONE as a proof term / definition / obligation name. Note: `ball`, `rate`, `dist`, `span`, `reaches` are neutral; `Outcome.coneOut`/`noconeOut` — check whether `\bcone\b` matches `coneOut` (it does NOT, since `e` is followed by the word char `O`); the theorem names `ws2_cone`, `ws4_cone_reachable`, `ws4_nocone_reachable` are underscore-wrapped (`\bcone\b` does not match `_cone_`). Report any TRUE whole-word match.

## 5. Strip test

For each payoff, delete any interpretive gloss ("rate", "cone", "light", "speed") and check the bare statement still stands as a fact about `att`/`dist`/`rate`/`ball`/`reaches`:
- WS1 → a `sup` over a finite set bounds each member's `dist`; the `sup` is monotone in the set; it takes concrete values 1/2/4.
- WS2 → membership in a `filter` by `dist ≤ (sup)·depth`; a `univ` element (`p4`) fails the depth-1 filter while another (`p1`) passes.
- WS3 → two `att`s with equal bounded-reachability have unequal `dist`-`sup`s and unequal filters; the `sup` is a function of `att`, monotone in it.
- WS4 → a `univ` element fails one carrier's depth-1 filter; every `univ` element passes another carrier's depth-1 filter.
- WS5 → a total `Bool⁶ → Outcome` computes `coneOut` on the earned flags and reaches all five outcomes.

Report any payoff whose content does NOT survive its strip (i.e. is only interesting under the interpretive name).

## 6. Grading rubric

- **SERIOUS:** a signature is vacuous or self-contradictory; the rate is SMUGGLED (a postulated constant `c`, not a `sup` over `att` — audit a, the phase sin); the cone rests on the bare order (equal on `attSlow`/`attFast` — the costume, audit c); the cone is trivial on its witness (audit d); the fork is a fiat (one side excluded by construction); a name is a forbidden term (audit e); the verdict is hand-set rather than computed from earned flags; or a success criterion is silently unmet.
- **REAL:** a genuine gap correctly labelled (an over-strong name, an assumed-and-returned hypothesis, a signature contentful but weaker than its heading claims).
- **COSMETIC / ACCEPTABLE:** a naming nit or nominal overclaim.

Return a structured list of findings, each with a stable ID (`Cn-Sm`), a grade, the exact location (theorem/def name), and the defect. If you find nothing SERIOUS, say so explicitly.
