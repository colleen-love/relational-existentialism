# WS4 design — the frustration knot (the fork) (2.8)

**Prove the fork on gluing, both sides genuinely reachable on directed-attention carriers, neither by fiat. FRUSTRATED-REACHABLE: a concrete pairwise-coherent population (the directed 3-ring) whose triangle holonomy is NON-TRIVIAL, so NO global section exists though every pair reconciles. GLUABLE-REACHABLE: a concrete population (the mutual star) whose holonomy VANISHES, so a global good exists and restricts to each self's local good. The knot: does local coherence GLUE or FRUSTRATE? The costume watch (doubled): the payoff rests on the many-body cocycle (`hol`), not a single edge, not import-ness; the strip test leaves a bare cocycle / global-section fact.**

## 1. Objects (shared, `spec/README.md` §2)

```
def attStar : S → Finset S := fun x => if x = p0 then {p1, p2} else {p0}    -- p0↔p1, p0↔p2 (mutual)
def IsSection (att : S → Finset S) (s : S → ℤ) : Prop :=
  ∀ x y, y ∈ att x → s y = s x + incr att x y
```

## 2. Payoffs

```
-- FRUSTRATED-REACHABLE: the directed ring has non-trivial holonomy and NO global section (WS4).
theorem ws4_frustrated_reachable :
    hol attTri p0 p1 p2 = 3                             -- non-trivial triangle holonomy
  ∧ ¬ ∃ s : S → ℤ, IsSection attTri s                  -- no global good, though every pair reconciles (WS2)

-- GLUABLE-REACHABLE: the mutual star has vanishing holonomy and a global section (WS4).
theorem ws4_gluable_reachable :
    hol attStar p0 p1 p2 = 0                            -- vanishing holonomy
  ∧ (∃ s : S → ℤ, IsSection attStar s ∧ s p0 = valu attStar p0)   -- a global good, restricting to the self's local good
```

`ws4_frustrated_reachable`: `hol attTri p0 p1 p2 = 1+1+1 = 3` (`decide`). No section: from `s : IsSection attTri s`, the ring edges (`p1∈attTri p0`, `p2∈attTri p1`, `p0∈attTri p2`, all `by decide`) give `s p1 = s p0 + 1`, `s p2 = s p1 + 1`, `s p0 = s p2 + 1`; substituting, `s p0 = s p0 + 3`, i.e. `0 = 3`, contradiction (`omega`). `ws4_gluable_reachable`: `hol attStar p0 p1 p2 = 0` (`decide`); the section `s := fun _ => 0` satisfies every star edge (each present edge has `incr attStar = 0`, by `fin_cases`+`decide`), and `s p0 = 0 = valu attStar p0` (`decide`).

## 3. Triage

- **Both sides genuine, no fiat (audit b).** Frustration is not built into `hol` (`attStar` gives `0`); gluing is not built in (`attTri` gives `3`). Same `incr`, same `recon`, same `hol` — only the directed attention differs. The fork is a fact about which world you are in.
- **No global good asserted (audit a).** The frustrated side asserts `¬ ∃` section; the gluable side asserts a section only where the holonomy vanishes, restricting to the self's LOCAL good (`valu`). No globally forced good.
- **Genuine many-body cocycle (audit c).** The obstruction is `hol` (the δ-sum), two-body-trivial (WS3) and alive here for three; the no-section proof turns on `0 = 3`, a cycle-level fact, not a single edge and not `Recoverable`.
- **Model-derived.** Both carriers are directed attentions; `hol` reads off `incr` off `knows`. The frustration is the directed ring failing to close (T1-S1 foreclosed).
- **Strip test.** Delete "good"/"gluing"/"frustration": "the signed increment sum around the directed 3-ring is `3`, so no `ℤ`-labelling `s` has `s y = s x + incr(x,y)` on all three edges; around the mutual star it is `0` and the constant labelling works." Bare cocycle / global-section facts about `attTri`/`attStar`.
- **Outcome class.** Frustrated reachable AND gluable reachable ⇒ `frustReachable = glueReachable = true` ⇒ `frustrated` (WS5): local coherence does not FORCE a global good.
- **Names (audit e).** `attStar`, `IsSection`, `ws4_*` embed no forbidden content-word.
