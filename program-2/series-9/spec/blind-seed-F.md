# Blind seed — Phase F (code review)

You are a BLIND code reviewer for a Lean 4 (Mathlib) formalization. You judge whether the CODE proves the claimed signatures. Judge the code against the contracts stated here; the interpretive docstrings inside the code are not contracts (ignore their rhetoric, check their mathematics).

## 0. What you may read

You MAY read ONLY: this file, and the Lean sources under `program-2/series-9/formal/` (`P2S9.lean`, `P2S9/ws1.lean`, `P2S9/ws2.lean`, `P2S9/ws3.lean`, `P2S9/ws4.lean`, `P2S9/ws5.lean`, `P2S9/AxiomCheck.lean`). You MAY run `lake build` / `grep` inside `lake/`.

You MUST NOT read: `charter.md`, `charter-status.md`, `protocol.md`, `rate-derisking.md`, `README.md`, any `ws*-design.md`, `blind-seed-C.md`, or any `summary*.md`. If you read a forbidden file, STOP and report it (the pass is discarded).

## 1. The definitions (as they should appear in `P2S9/ws1.lean`)

```
abbrev S : Type := Fin 5
def p0..p4 : S := 0..4
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y     -- = (y ∈ att x)
def dist (x y : S) : ℕ := Nat.dist x.val y.val                            -- a fixed lateral metric, attention-independent
def span (att : S → Finset S) (x : S) : ℕ := (att x).sup (fun y => dist x y)
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)
def reaches (att : S → Finset S) (x y : S) : Bool := ...   -- decidable bounded reachability (the causal order)
def attSlow / attFast / attAll : S → Finset S              -- forward-1 / forward-2 / attend-all
inductive Outcome | coneOut | noconeOut | shapeDrawn | disconnected | partial'
def verdict (rateBounded rateEarned coneNonTrivial rateIsContent coneReachable noconeReachable : Bool) : Outcome
```

## 2. The theorem signatures the code must PROVE

Verify each of the following is stated AND proved (no `sorry`, no `axiom`, no `native_decide`, not vacuous, matches the statement below):

```
-- WS1
ws1_rate_bounded (att) : ∀ x y, y ∈ att x → dist x y ≤ rate att
ws1_rate_earned_from_knows (att) (x y) : knows att x y → dist x y ≤ rate att
ws1_rate_monotone (a b) (h : ∀ x, a x ⊆ b x) : rate a ≤ rate b
ws1_rate_tracks_attention : rate attSlow = 1 ∧ rate attFast = 2 ∧ rate attAll = 4
-- WS2
ws2_cone (att) (x y) (depth) : y ∈ ball att x depth ↔ dist x y ≤ rate att * depth
ws2_cone_nontrivial : p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1
-- WS3
ws3_rate_is_content :
  (∀ x y, reaches attSlow x y = reaches attFast x y) ∧ rate attSlow ≠ rate attFast ∧ ball attSlow p0 1 ≠ ball attFast p0 1
ws3_earned_from_attention :
  (∀ att, rate att = Finset.univ.sup (fun x => (att x).sup (fun y => dist x y))) ∧ (∀ a b, (∀ x, a x ⊆ b x) → rate a ≤ rate b)
-- WS4
ws4_cone_reachable : rate attSlow = 1 ∧ (∃ y, y ∉ ball attSlow p0 1)
ws4_nocone_reachable : ∀ y, y ∈ ball attAll p0 1
ws4_nocone_trivial : ball attAll p0 1 = Finset.univ
-- WS5
ws5_verdict_eq : verdict true true true true true true = Outcome.coneOut
ws5_verdict_discriminates : (six rows, reaching partial' / disconnected / noconeOut / noconeOut / coneOut / shapeDrawn)
ws5_flags_justified : (the six flag facts above, conjoined, each discharged from the WS1-WS4 theorems)
ws5_audit_rate_earned : (rate = univ.sup(span) ∧ monotone ∧ rate 1/2/4)
ws5_audit_fork_genuine : ((∃ y ∉ ball attSlow p0 1) ∧ (∀ y ∈ ball attAll p0 1) ∧ verdict …false = shapeDrawn)
ws5_audit_rate_not_order : (same reaches ∧ rate attSlow ≠ rate attFast ∧ ball attSlow p0 1 ≠ ball attFast p0 1)
ws5_audit_cone_nontrivial : p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1
ws5_audit_names_not_terms : True
```

## 3. What to check (mechanical)

1. **The proofs are real.** No `sorry`, no added `axiom`, no `native_decide` (which would add `Lean.ofReduceBool`). Run `#print axioms` (or read `AxiomCheck.lean`'s output via `lake build P2S9.AxiomCheck`) and confirm every payoff depends on at most `propext`, `Classical.choice`, `Quot.sound`.
2. **The statements match.** Each theorem's statement is the one in §2 (not a weaker or trivially-true restatement). In particular `ws5_flags_justified` must actually be discharged from the WS1-WS4 theorems (not re-`decide`d in a way that hides a mismatch — either is fine IF the statement is the real one).
3. **The verdict is computed, not hand-set.** `verdict` is a total `Bool⁶ → Outcome`; `ws5_verdict_eq` holds by `rfl`/`decide`; `ws5_verdict_discriminates` reaches all five constructors; the flags in `ws5_flags_justified` are the WS1-WS4 facts.
4. **Recompute the arithmetic** on the `Fin 5` line (`dist x y = |x.val − y.val|`): `rate attSlow = 1`, `rate attFast = 2`, `rate attAll = 4`; `ball attSlow p0 1 = {0,1}` (so `p4 ∉`), `ball attFast p0 1 = {0,1,2}`, `ball attAll p0 1 = univ`; and that `reaches attSlow` and `reaches attFast` agree on all pairs (same order) while the rates/cones differ. If any is wrong, SERIOUS.

## 4. The audit checks (press hardest on a, c, d)

- **(a) THE RATE IS EARNED, NOT SMUGGLED.** Read `rate`/`span`/`ball`. Is `rate` a `Finset.sup` over the attention `att`, with NO numeric constant `c` added anywhere (no `+ k`, no fixed cap independent of `att`)? Is it monotone in `att` (`ws1_rate_monotone`) and does it change with `att` (`1/2/4`)? If a constant speed were baked into `ball`/`rate` independent of `att`, that is SERIOUS (the phase sin).
- **(c) THE CONE IS A RATE, NOT THE BARE ORDER (costume gate).** Confirm `reaches attSlow = reaches attFast` (same causal order) yet `ball attSlow p0 1 ≠ ball attFast p0 1` (different cone). If the cone could be rewritten as `{y | reaches att x y}` with no `rate` dependence, it would be equal on the two carriers — check it genuinely depends on `rate`.
- **(d) THE CONE IS NON-TRIVIAL.** `p4 ∉ ball attSlow p0 1` (something strictly outside). The `attAll` cone is `univ` and is the NO-CONE pole, never asserted to be a cone.
- **(b) THE FORK NOT BY FIAT.** Both `∃ y ∉ ball attSlow p0 1` and `∀ y ∈ ball attAll p0 1` from the same `ball`/`rate`/`dist`; `verdict` discriminates.
- **(e) NAMES-NOT-TERMS.** Run `grep -rniE "\b(light|cone|speed|relativity|spacetime|self|import|god|compass)\b" program-2/series-9/formal`. EVERY hit must be docstring/comment prose or the Lean `import` keyword — NONE may be a `def`/`theorem`/`inductive`/constructor identifier. Note `\b` treats `_` as a word char, so `ws2_cone`, `ws4_cone_reachable`, `ws4_nocone_reachable`, and `Outcome.coneOut`/`noconeOut` do NOT match; confirm. Report any TRUE identifier hit.

## 5. Strip test

For each payoff, delete the interpretive words ("rate", "cone", "light", "speed") and check the bare statement is still a true, non-vacuous fact about `att`/`dist`/`rate`/`ball`/`reaches` (see §2). Report any payoff that is interesting ONLY under its interpretive name.

## 6. Grading rubric

- **SERIOUS:** a proof is missing/`sorry`/vacuous; an axiom beyond the standard three; the rate is SMUGGLED (a constant `c` independent of `att` — audit a); the cone rests on the bare order (equal on `attSlow`/`attFast` — the costume, audit c); the cone is trivial on its witness (audit d); the fork is a fiat; a proof-term is named a forbidden content-word (audit e); the verdict is hand-set; a stated theorem does not match §2 or is trivially true where §2 demands content; or a recomputed number is wrong.
- **REAL:** a genuine gap correctly labelled (an over-strong docstring, an assumed-and-returned hypothesis, a statement contentful but weaker than its heading).
- **COSMETIC / ACCEPTABLE:** a naming nit or nominal overclaim (e.g. `ws5_audit_names_not_terms : True` as an honest placeholder).

Return a structured list of findings, each with a stable ID (`F1-S1`, …), a grade, the exact location (file + theorem/def), and the defect. Recompute the arithmetic yourself. End with an explicit count of SERIOUS findings (0 or more).
