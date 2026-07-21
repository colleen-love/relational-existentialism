# WS3 design — the obstruction is genuinely many-body (the anti-costume core) (2.8)

**DEFINE the HOLONOMY / cocycle of the reconciliations around a cycle of selves, and prove it is a GENUINE many-body phenomenon: (i) it VANISHES for two selves — no cycle, no obstruction, so this is NOT Series 2.3 replayed; and (ii) the reconciliations are DERIVED FROM THE MODEL — the directed attention — so the holonomy is a cocycle over the network, NOT a bolted-on gadget and NOT import-ness. This is where the Series 2.7 lesson (T1-S1) bites: the obstruction must not be a disconnected counter; the strip test must leave a bare cocycle fact about the built directed population.**

## 1. Objects (shared, `spec/README.md` §2)

```
def hol (att : S → Finset S) (x y z : S) : ℤ := incr att x y + incr att y z + incr att z x
def knows (att : S → Finset S) (x y : S) : Prop := P2S0.knows att x y     -- the imported directed knowing
```

`hol att x y z` is the net translation of `recon att z x ∘ recon att y z ∘ recon att x y` (each `recon` adds its `incr`), the amount by which a value fails to return to itself around the triangle `x → y → z → x`.

## 2. Payoffs

```
-- (i) THE HOLONOMY VANISHES FOR TWO SELVES — genuinely many-body, not a single edge (WS3).
theorem ws3_two_body_trivial (att : S → Finset S) (x y : S) :
    incr att x y + incr att y x = 0                    -- antisymmetry: every edge round-trips to 0
  ∧ hol att x y x = 0                                  -- any 2-body cycle (revisiting x) has no holonomy
  ∧ hol att x x y = 0

-- (ii) THE HOLONOMY IS MODEL-DERIVED: carried by the DIRECTEDNESS of the attention, not bolted on (WS3).
theorem ws3_holonomy_model_derived :
    (∀ (att : S → Finset S) (x y : S),                 -- incr is the signed `knows` difference (definitional bridge)
        incr att x y = (if knows att x y then 1 else 0) - (if knows att y x then 1 else 0))
  ∧ (∀ (att : S → Finset S), (∀ x y : S, x ∈ att y ↔ y ∈ att x) →   -- kill the direction …
        ∀ x y z : S, hol att x y z = 0)                             -- … and ALL holonomy vanishes
  ∧ (∃ x y : S, y ∈ attTri x ∧ x ∉ attTri y)          -- the frustrating carrier is genuinely directed
```

`ws3_two_body_trivial`: `incr att x y + incr att y x = 0` (the two `if`s cancel; `ring`); `hol att x y x = incr att x y + incr att y x + incr att x x = 0`. For ALL `att` — the obstruction is invisible for two selves. `ws3_holonomy_model_derived`: conjunct 1 is `rfl` (`incr` IS the signed `knows` difference — `knows` reduces to membership, `decKnows` is the membership instance); conjunct 2 shows a SYMMETRIC attention has every `incr = 0` (each `if` matches its partner via `hsym`) hence `hol = 0`; conjunct 3 exhibits `p0 → p1` with no return (`by decide`).

## 3. Triage

- **Not a single edge / not 2.3 replayed (audit c, first front).** `ws3_two_body_trivial`: the holonomy is `0` for every two-selves configuration; it can only be alive for three (the ring's `3`, WS4). The obstruction is genuinely many-body.
- **Not bolted on / model-derived (audit c/d, the T1-S1 lesson).** `ws3_holonomy_model_derived` conjunct 2 is the decisive certificate: make the directed attention symmetric and the obstruction vanishes identically. A bolted-on gadget (a free permutation, a `Finset.card` counter) would be indifferent to the symmetry of `att`; this holonomy lives in the DIRECTEDNESS of the built attention. Conjunct 1 ties `incr` to `P2S0.knows` definitionally — no free parameter.
- **Not import-ness (audit c, second front).** `hol` never mentions `Recoverable`/`¬Recoverable`; it is the δ-sum around a cycle, a network/axis engine, not "that edge is an import."
- **Strip test.** Delete "good"/"reconciliation"/"holonomy": "the signed directed-adjacency sum around a 3-cycle is `0` whenever the adjacency is symmetric, and vanishes for any 2-cycle." A bare cocycle fact about `attTri`/`knows`.
- **Outcome class.** Two-body-trivial + three-body-alive (WS4) ⇒ `manyBody = true` ⇒ NOT `pairwiseOnly` (WS5).
- **Names (audit e).** `hol`, `knows`, `ws3_*` embed no forbidden content-word.
