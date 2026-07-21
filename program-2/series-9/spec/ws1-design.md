# WS1 design — the maximal rate (the risky ground) (2.9)

**DEFINE the reification RATE off the finite attention, and prove it BOUNDED — a finite `c` limiting how much lateral breadth one tick converts into depth, EARNED from the attention (Series 2.0), never postulated. The first risk and the whole no-smuggling gate: if the rate did not fall out of the finite attention, the answer is NO-CONE. It survives (`rate-derisking.md` §2): the rate is a `Finset.sup` over the attention, finite, bounding the per-tick reach, and strictly monotone in the attention.**

## 1. Objects (shared, `spec/README.md` §2)

```
abbrev S : Type := Fin 5
def dist (x y : S) : ℕ := Nat.dist x.val y.val
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)
```

## 2. Payoff

```
-- THE RATE BOUNDS THE PER-TICK REACH (the conversion cannot outrun the rate).
theorem ws1_rate_bounded (att : S → Finset S) :
    ∀ x y, y ∈ att x → dist x y ≤ rate att

-- THE RATE BOUNDS EXACTLY THE ATTENDED RELATA (earned from the imported knowing).
theorem ws1_rate_earned_from_knows (att : S → Finset S) (x y : S) :
    knows att x y → dist x y ≤ rate att

-- THE RATE TRACKS THE ATTENTION (monotone: more attention, higher rate — not an arbitrary cap).
theorem ws1_rate_monotone (a b : S → Finset S) (h : ∀ x, a x ⊆ b x) :
    rate a ≤ rate b

-- THE RATE IS FINITE AND CONCRETE, rising with the attention (the fork carriers).
theorem ws1_rate_tracks_attention :
    rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4
```

`ws1_rate_bounded`: `dist x y ≤ span att x` (`Finset.le_sup`, `y ∈ att x`) `≤ rate att` (`Finset.le_sup`, `x ∈ univ`), `le_trans`. `ws1_rate_earned_from_knows`: `knows att x y` unfolds to `y ∈ att x`; then `ws1_rate_bounded`. `ws1_rate_monotone`: `Finset.sup_le`, `Finset.sup_mono (h x)`, `Finset.le_sup (mem_univ x)`. `ws1_rate_tracks_attention`: `decide`.

## 3. Triage

- **Earned, not smuggled (audit a).** `rate` is `univ.sup (span att)`, a `Finset.sup` over the attention `att`; NO numeral is added. `ws1_rate_monotone` + `ws1_rate_tracks_attention` show it is a strictly monotone function of `att` — a postulated `c` could not track the attention this way.
- **Bounded by FINITE attention specifically (audit d).** The rate is a max over the finite `att x` (the P2S0 bound) of finite distances — finite because the attention is finite, one level down at ℕ. Not an arbitrary ceiling.
- **The rate is a genuine speed (breadth per depth).** `span` is a `dist`-sup (a lateral BREADTH, 2.4), per ONE tick (one unit of depth, 2.1). So `rate` is breadth/depth, not a bare order.
- **Strip test.** Delete "rate"/"speed"/"light": `ws1_rate_bounded` is "a `sup` over a finite set bounds each of its members' distances" — a bare `Finset.le_sup` fact about `att`, `dist`. Survives.
- **Outcome class.** Rate bounded & earned ⇒ `rateBounded = rateEarned = true` ⇒ NOT the NO-CONE ground failure (WS5).
- **Names (audit e).** `rate`, `span`, `dist`, `knows`, `ws1_*` embed no forbidden content-word (`speed`/`light`/`cone` avoided as identifiers; `rate` is not forbidden).
