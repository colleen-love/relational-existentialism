# WS3 design — the cone is a rate, not the bare order (the anti-costume core) (2.9)

**Prove the cone is a genuine finite-SPEED structure, not a relabelling of Series 2.5's causal reachability. Two fronts: (i) the cone depends on the RATE, so two carriers with the SAME causal order but different rates have DIFFERENT cones (the rate is not recoverable from the order); (ii) the rate is a function of the finite attention (Series 2.0), not a `c` added to obtain the cone (the no-smuggling gate). The costume risk lives here: if the cone stripped to the bare order, it would be identical on the two carriers, and there would be no genuine rate.**

## 1. Objects (shared, `spec/README.md` §2)

```
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S := ...
def reaches (att : S → Finset S) (x y : S) : Bool := reachWithin att (Fintype.card S) x y
def attSlow : S → Finset S   -- rate 1     ; def attFast : S → Finset S   -- rate 2, SAME order as attSlow
```

## 2. Payoff

```
-- SAME CAUSAL ORDER, DIFFERENT RATE, DIFFERENT CONE (the rate is not recoverable from the order).
theorem ws3_rate_is_content :
    (∀ x y, reaches attSlow x y = reaches attFast x y)   -- same causal order (2.5, re-seated)
  ∧ rate attSlow ≠ rate attFast                          -- different rate
  ∧ ball attSlow p0 1 ≠ ball attFast p0 1                -- ⇒ different cone

-- THE RATE IS EARNED FROM THE ATTENTION (a function of `att`, monotone in it — not a postulated c).
theorem ws3_earned_from_attention :
    (∀ att : S → Finset S, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y)))
  ∧ (∀ a b : S → Finset S, (∀ x, a x ⊆ b x) → rate a ≤ rate b)
```

`ws3_rate_is_content`: `decide` on each conjunct (the reachability equality is `decide` over `Fin 5 × Fin 5`; the rate and cone facts compute `Finset.sup` / `Finset.filter`). `ws3_earned_from_attention`: first conjunct `rfl` (definitional); second is `ws1_rate_monotone`.

## 3. Triage

- **The cone is a genuine rate, not the bare order (audit c, the costume gate).** `attSlow` and `attFast` have IDENTICAL causal reachability (`reaches attSlow = reaches attFast` — both `{y | x ≤ y}` forward), yet their cones DIFFER (`{p0,p1}` vs `{p0,p1,p2}`) because their rates differ (1 vs 2). So the cone carries content the order does not: the rate is real. A cone that stripped to `{y | reaches att x y}` would be equal on the two carriers, contradicting the third conjunct.
- **Earned from attention (audit a, the no-smuggling gate).** `rate` is `univ.sup (span att)` — a function of `att` (rfl), monotone in `att`. The differing rates of `attSlow`/`attFast` are differing attentions (`attSlow x ⊆ attFast x`, strictly). No `c` is postulated.
- **Strip test.** Delete "cone"/"rate"/"speed": (i) is "two `att`s with equal bounded-reachability have unequal `dist`-`sup`s and so unequal `dist ≤ sup·depth` filters"; (ii) is "a `univ.sup (Finset.sup …)` is a function of `att`, monotone in `att`" — bare facts.
- **Outcome class.** Same-order-different-cone ⇒ `rateIsContent = true` ⇒ NOT `disconnected` (the cone does not collapse to the order); earned ⇒ `rateEarned = true` ⇒ NOT `partial'` (WS5).
- **Names (audit e).** `rate`, `reaches`, `ball`, `ws3_*` embed no forbidden content-word.
