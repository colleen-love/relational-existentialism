# WS2 design — The weak continuity (recoverable, or import?) (2.6)

**Define a WEAK continuity — a successor-continuity lift over the relating, coarser than the rank lift that fixes
strict identity — and prove the fork's substance: it is RECOVERABLE from the plain relating on the MERGED carrier
(an endogenous succession the structure carries) and an IMPORT on the CUT carrier (non-recoverable, a grace from
outside). Prove it is GENUINELY WEAKER than strict identity: on the merged carrier the rank lift (strict) separates
the two moments while the continuity lift (weak) relates them recoverably. This is where the series lives (charter
§2 WS2): not that the self changes (trivial, WS1), but whether the sense of continuity over the change is carried
or imported. The weak continuity must be non-vacuous and genuinely weaker than strict identity, or the fork is
empty (audit b).**

## 1. Candidate constructions

1. **The weak continuity = plain bisimilarity.** REJECTED: on an atomless carrier the collapse engine makes every
   pair plain-bisimilar, so "recoverable plain continuity" is vacuously true everywhere — no fork.
2. **The weak continuity = strict (rank) identity, renamed.** REJECTED: that is the costume/fiat (audit b); strict
   identity fails across every tick, so "the weak continuity" would be empty. The weak continuity must be a
   COARSER lift that can hold where strict fails.
3. **The weak continuity = recoverability of a coarse continuity LIFT, forked merged-vs-cut (CHOSEN).** The
   continuity lift `contLift : X → LkObj κ Q X` tags each edge with the continuity mark (the directional knowing
   that binds one moment to the next). Its recoverability is the fork:
   - **MERGED carrier** (`m0 ⇄ m1`, mutual attention, one stream): the continuity mark is UNIFORM, so every plain
     bisimulation is already a continuity-bisimulation — `Recoverable`. Proved by the general lemma
     `const_first_recoverable`. The continuity is endogenous.
   - **CUT carrier** (`c0 → c1`, one-way attention, cut stream): the continuity mark distinguishes the
     plain-bisimilar pair — NOT `Recoverable`. Proved via `AttentionDistinguishes ⇒ ¬ Recoverable`. The continuity
     is an import (the `ws3_direction_not_recoverable` mechanism, reworked fresh).

   Coarser than rank (so it can hold where strict fails), forked genuinely by the shape of the attention stream.

## 2. Triage

- **Genuinely weaker than strict, not a fiat (audit b).** `ws2_weaker_than_strict`: on the SAME merged carrier and
  the SAME plain relating, the rank lift separates `m1`,`m0` (strict identity fails, `AttentionDistinguishes`) while
  the continuity lift is `Recoverable` and relates them. So the weak continuity holds where strict fails: it is a
  genuine intermediate, not strict relabelled. SEVERED is reachable (the cut carrier), so the fork is not by fiat.
- **No costume (audit c).** The fork is powered by the recoverability test (merged uniform vs cut asymmetric), the
  diagonal/import machinery, NOT by "strict identity fails" (which is WS1, walled out of the verdict).
- **Strip test.** `ws2_cont_recoverable` → "a lift with one edge-label value is `Recoverable`";
  `ws2_cont_is_import` → "a lift separating a plain-bisimilar pair is not `Recoverable`"; `ws2_weaker_than_strict`
  → "on one relating the rank lift separates a pair the continuity lift relates recoverably." Bare `Recoverable` /
  `AttentionDistinguishes` facts.
- **Names-not-terms (audit e).** `mergeLift`, `cutLift`, `contLift`, `MCar`, `CCar`, `ws2_cont_recoverable`,
  `ws2_cont_is_import`, `ws2_weaker_than_strict` embed no forbidden content-word.

## 3. Winning construction — typed signatures

```
-- General lemma: the plain reduct of a rank-style lift forgets the label.
lemma plainOf_rankLift_gen {X : Type} (dest : X → PkObj κ X) (lab : X → ℕ) :
    plainOf (rankLift dest lab) = dest

-- General lemma (the RECOVERABLE horn): a lift all of whose edge-labels equal one constant is Recoverable.
theorem const_first_recoverable {Q X : Type} (destL : X → LkObj κ Q X) (c : Q)
    (hconst : ∀ x, ∀ p ∈ (destL x).1, p.1 = c) : Recoverable destL

-- General lemma (the IMPORT horn): a lift separating a plain-bisimilar pair is not Recoverable.
theorem distinguishes_not_recoverable {Q X : Type} (destL : X → LkObj κ Q X) (x y : X)
    (h : AttentionDistinguishes destL x y) : ¬ Recoverable destL

-- The MERGED carrier (m0 ⇄ m1, mutual attention; the woven stream).
abbrev MCar : Type := Fin 2
def m0 : MCar := 0 ; def m1 : MCar := 1
def attendsM : MCar → Finset MCar := fun x => if x = m0 then {m1} else {m0}
def rankM : MCar → ℕ := fun x => if x = m0 then 0 else 1        -- m1 the reified successor, rank 1
def mergeLift (hinf : ℵ₀ ≤ κ) : MCar → LkObj κ Bool MCar :=      -- uniform continuity mark `true`
  fun x => if x = m0 then pkSingle hinf (true, m1) else pkSingle hinf (true, m0)
lemma ws_mcar_SHNE (hinf : ℵ₀ ≤ κ) (x : MCar) : SHNE (outDest hinf attendsM) x

-- The CUT carrier (c0 → c1, one-way; the severed stream).
abbrev CCar : Type := Bool
def c0 : CCar := true ; def c1 : CCar := false
def cutAttends : CCar → Finset CCar := fun x => if x = c0 then {c1} else ∅
def cutLift (hinf : ℵ₀ ≤ κ) : CCar → LkObj κ CCar CCar :=        -- directional knowing: c0 knows c1, c1 not c0
  fun x => if x = c0 then pkSingle hinf (c0, c1) else pkSingle hinf (c1, c0)

-- The RECOVERABLE horn (WOVEN): the merged continuity is recoverable.
theorem ws2_cont_recoverable (hinf : ℵ₀ ≤ κ) : Recoverable (mergeLift hinf)

-- The IMPORT horn (SEVERED): the cut continuity is not recoverable (an import).
theorem ws2_cont_is_import (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (cutLift hinf)

-- GENUINELY WEAKER THAN STRICT (audit b): on the merged carrier, over one relating, the rank lift separates the
-- two moments (strict identity fails) while the continuity lift is recoverable and relates them.
theorem ws2_weaker_than_strict (hinf : ℵ₀ ≤ κ) :
    AttentionDistinguishes (rankLift (outDest hinf attendsM) rankM) m1 m0
  ∧ Recoverable (mergeLift hinf)
```

Both `mergeLift` and `rankLift (outDest hinf attendsM) rankM` sit over the SAME plain relating `outDest hinf
attendsM` (`plainOf (mergeLift hinf) = outDest hinf attendsM = plainOf (rankLift (outDest hinf attendsM) rankM)`),
so the weaker-than-strict comparison is one pair, one relating, two lifts.

`cutLift`'s plain reduct is the SYMMETRIC relating `c0 — c1` (both `SHNE`), on which `c0`,`c1` are plain-bisimilar;
`cutLift` separates them (`c0`'s edge carries mark `c0`, `c1`'s carries `c1`): `AttentionDistinguishes`, hence not
`Recoverable`. This is the `P2S0.ws3_direction_not_recoverable` mechanism built fresh.

## 4. Why the fork is genuine (no fiat, no costume)

Two carriers, one question (is the coarse continuity recoverable). On the merged carrier the continuity is uniform
and recoverable (WOVEN); on the cut carrier it distinguishes a plain-bisimilar pair and is an import (SEVERED).
Because the recoverable continuity relates rank-distinct moments (`ws2_weaker_than_strict`), it is genuinely
weaker than strict identity, not strict relabelled. Because SEVERED is reachable, WOVEN is not a fiat. The fork is
powered by the recoverability test (the import boundary), not by strict identity failing (the costume).

## 5. Outcome classes

- **WOVEN reachable:** `ws2_cont_recoverable` — a recoverable weak continuity exists.
- **SEVERED reachable:** `ws2_cont_is_import` — a non-recoverable weak continuity (an import) exists.
- Both reachable ⇒ the recoverability is SELF-RELATIVE (WS4/WS5); the honest verdict is SHAPE-DRAWN.

## 6. Strip annotation

- `const_first_recoverable` → "a labelled lift with one edge-label value has every plain bisimulation a
  label bisimulation."
- `ws2_cont_recoverable` → "a uniform-label lift is `Recoverable`."
- `ws2_cont_is_import` → "a lift separating a plain-bisimilar pair is not `Recoverable`."
- `ws2_weaker_than_strict` → "over one relating a coarse lift is recoverable while the rank lift separates the
  same pair."
