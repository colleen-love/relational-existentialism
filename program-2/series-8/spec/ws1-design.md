# WS1 design — the population and the good (the ground) (2.8)

**BUILD a lateral population of three selves fresh on the world, and DEFINE the GOOD: a self-relative valuation read off the self's directed attention. Prove it well-defined and NON-TRIVIAL — non-constant AND perspectival (two selves value a common relatum oppositely, which no view-from-nowhere valuation can), so the good is not a metric relabel and not a view from nowhere. The first risk: if no non-trivial self-relative good survives, DISCONNECTED. It survives (`frustration-derisking.md` §2).**

## 1. Objects (shared, `spec/README.md` §2)

```
abbrev S : Type := Fin 3
def p0 : S := 0 ; def p1 : S := 1 ; def p2 : S := 2
def attTri : S → Finset S := fun x => if x = p0 then {p1} else if x = p1 then {p2} else {p0}
def incr (att : S → Finset S) (x y : S) : ℤ := (if y ∈ att x then 1 else 0) - (if x ∈ att y then 1 else 0)
def valu (att : S → Finset S) : S → ℤ := fun y => incr att p0 y     -- the good, from the self p0's frame
```

`valu attTri = (p0 ↦ 0, p1 ↦ +1, p2 ↦ -1)` on the ring (§ de-risking §2).

## 2. Payoff

```
-- THE GOOD IS NON-TRIVIAL AND GENUINELY SELF-RELATIVE (WS1).
theorem ws1_nontrivial :
    valu attTri p1 ≠ valu attTri p2                       -- (i) non-constant: two selves valued differently
  ∧ incr attTri p0 p2 ≠ incr attTri p1 p2                 -- (ii) perspectival: p2 valued oppositely by p0, p1
```

`(i)` `valu attTri p1 = +1 ≠ -1 = valu attTri p2` — the good is not constant (not a view from nowhere). `(ii)` `incr attTri p0 p2 = -1` while `incr attTri p1 p2 = +1` — the same relatum `p2` is valued with opposite sign from two frames. Both by `decide`.

## 3. Triage

- **Non-trivial (audit b).** `(i)` is the "a function taking two distinct values" strip-test residue: `valu attTri` is non-constant.
- **Self-relative, not a metric (WS1 costume watch).** `(ii)` is antisymmetric/observer-indexed. A symmetric metric `d(x,y)=d(y,x)` (2.4's `reachIn`/`latW`) values a target the same from every frame and cannot satisfy `(ii)`; `Converges₂` (2.3) is a `Prop`, not a ℤ-valuation. The good is neither relabelled.
- **Model-derived.** `valu` reads off `incr`, a function of `attTri` (the directed attention) alone — no free parameter.
- **Strip test.** Delete "good"/"value": `(i)` is "an integer function on `Fin 3` taking two distinct values"; `(ii)` is "the signed adjacency increment is not symmetric across two source vertices." Bare facts about `attTri`.
- **Outcome class.** Good non-trivial ⇒ `nonTrivial = true` ⇒ NOT `disconnected` (WS5).
- **Names (audit e).** `valu`, `incr`, `attTri`, `p0/p1/p2`, `ws1_nontrivial` embed no forbidden content-word (`good`/`value` avoided as identifiers).
