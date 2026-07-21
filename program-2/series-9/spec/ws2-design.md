# WS2 design — the cone (2.9)

**DEFINE the cone of a source at a given depth — the events reachable at the rate — and prove it is EXACTLY the rate-bounded reachable set, and NON-TRIVIAL on the witnessing carrier (some events inside, some strictly outside — a genuine finite speed). A cone that is the whole world is the NO-CONE pole, not a cone.**

## 1. Objects (shared, `spec/README.md` §2)

```
abbrev S : Type := Fin 5
def p0 : S := 0 ; def p1 : S := 1 ; def p4 : S := 4
def dist (x y : S) : ℕ := Nat.dist x.val y.val
def rate (att : S → Finset S) : ℕ := Finset.univ.sup (fun x => span att x)
def ball (att : S → Finset S) (x : S) (depth : ℕ) : Finset S :=
  Finset.univ.filter (fun y => dist x y ≤ rate att * depth)
def attSlow : S → Finset S      -- rate 1
```

## 2. Payoff

```
-- THE CONE IS EXACTLY THE RATE-BOUNDED REACHABLE SET.
theorem ws2_cone (att : S → Finset S) (x y : S) (depth : ℕ) :
    y ∈ ball att x depth ↔ dist x y ≤ rate att * depth

-- THE CONE IS NON-TRIVIAL: some event inside, some strictly OUTSIDE (causally disconnected within one tick).
theorem ws2_cone_nontrivial :
    p1 ∈ ball attSlow p0 1 ∧ p4 ∉ ball attSlow p0 1
```

`ws2_cone`: `simp [ball, Finset.mem_filter, Finset.mem_univ]`. `ws2_cone_nontrivial`: `decide` (rate attSlow = 1; `dist p0 p1 = 1 ≤ 1`, `dist p0 p4 = 4 > 1`).

## 3. Triage

- **The cone is the rate-bounded set (charter WS2).** `ws2_cone` is the membership characterization: within `rate × depth` is in, beyond is out.
- **Non-trivial, a genuine finite speed (audit d).** `p4` at `dist 4` is strictly outside the depth-1 cone of `p0` on `attSlow` (rate 1): the far event lies in an elsewhere no single tick reaches. Some event inside (`p1`), some outside (`p4`).
- **Not the whole world (the NO-CONE watch).** The cone here is `{p0, p1}`, not `univ`; the `univ` case is `attAll` (WS4, the NO-CONE pole), never asserted to be a cone.
- **Strip test.** Delete "cone"/"light": `ws2_cone` is "membership in a `filter` by `dist ≤ rate·depth`"; `ws2_cone_nontrivial` is "an element of `univ` fails the filter" — bare facts about `ball`, `dist`, `rate`.
- **Outcome class.** Cone non-trivial ⇒ `coneNonTrivial = true` ⇒ NOT NO-CONE-by-triviality (WS5).
- **Names (audit e).** The cone's definition is `ball`, not `cone`; the theorem names `ws2_cone` are underscore-wrapped (grep-safe). No forbidden identifier.
