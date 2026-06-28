/-
# The loop bridge — step 3: from resource threshold to fixed point

> **Status note.** This module is the **uniform, conserved, depleting special case** of
> attention (a private scalar budget `β` drawn down at fixed per-return cost). The
> general, structurally-derived account — attention as the co-directed eigenstructure of
> the relational coupling, with the self an eigenform `νΦ` and finiteness constitutive
> rather than budgeted — is `Scratch/Attention.lean` (see `docs/spec/01-signature.md
> §1.3`). This file remains valid and is what makes the threshold↔fixed-point bridge
> quantitative in the depleting regime.

This module discharges the gap flagged in
[`docs/archive/03.7-sparsity.md`](../../docs/archive/03.7-sparsity.md):
the sparsity lemmas count with a *threshold* ("a self costs at least `m`"), but
[A3](../../docs/spec/02-axioms.md) defines a self as a **fixed point** of budgeted,
iterated self-relation (`loop_R(e) = e`). Step 3 connects the two.

We model self-relation as an **abstract** operator `σ : X → X` (one attended return) — a *bare
endomap*, **not** the relational `Φ_c` of `Scratch/Attention.lean`. Tying this `σ` to the actual
co-directed operator is the modeling step this file does *not* take — but
`Scratch/Convergence.lean` now does, for the depth: it instantiates `σ := Φ_c = couplingOp c` and
*derives* `StabilizesAt` (the depth structure below) from the convergence of `Φ_c`'s orbit
(`convergesAt_imp_stabilizesAt`), running the bridge below over the genuine operator. A seed `x` **stabilizes at
depth `d`** when iterating `σ` from `x` reaches an eigenform after exactly `d` returns
(`StabilizesAt`). The budget `β`, with per-return cost `λ`, funds `N = ⌊β/λ⌋` returns, and
`loop_R x := σ^N x`. The bridge is then:

    loop_R(x) is an eigenform  ⟺  N ≥ d  ⟺  d · λ ≤ β.

**Be clear about how little this is.** The left `⟺` is `StabilizesAt` *unfolded* at `n := N` — the
definition with the iteration count plugged in. The right `⟺` is a single arithmetic lemma
(`Nat.le_div_iff_mul_le`). (We work additively over `Nat`, the log-scale of the spec's multiplicative
`ε^n ≤ β`: take `λ := log ε`, `β := log` budget.)

And the capstone `stab_card_le_half_of_depths` **relocates** the sparsity floor, it does not derive
it: `two_le_selfCost` gets `2 ≤ d·λ` from `2 ≤ d` (trivial, since `λ ≥ 1`), so the load-bearing posit
is the **depth floor `d ≥ 2`** ("a self needs genuine return, not a one-off"; A3). That is arguably a
cleaner home for the posit than "cost ≥ 2", but nothing here *forces* `d ≥ 2`: it is a hypothesis,
and even the witness `matarN_stabilizesAt` builds `d` in by construction (its dynamics caps at `d`).
The genuinely structural rarity — selves *nowhere dense*, with the sharp dichotomy — is the Agda
result (`agda/RelExist/Sparsity.agda`), which needs no cost model and which this counting bound
cannot reach. Pure `Nat`/iteration; no mathlib.
-/
import RelExist.Sparsity

namespace RelExist

universe u
variable {X : Type u}

/-- `e` is an **eigenform** of self-relation `σ`: a fixed point, `σ e = e`. -/
def IsEigen (σ : X → X) (e : X) : Prop := σ e = e

/-- `iter σ n x` — the state after `n` attended returns (iterating `σ` from `x`). -/
def iter (σ : X → X) : Nat → X → X
  | 0,     x => x
  | n + 1, x => σ (iter σ n x)

/-- A seed `x` **stabilizes at depth `d`**: iterating self-relation from `x` is an
eigenform after exactly `d` returns, and not before. (A forming self matures one notch
per attended return, becoming a stable eigenform precisely once returned to `d` times.) -/
def StabilizesAt (σ : X → X) (x : X) (d : Nat) : Prop :=
  ∀ n, IsEigen σ (iter σ n x) ↔ d ≤ n

/-- The number of returns a budget `β` funds when each return costs `λ`: `⌊β/λ⌋`. -/
def fundedReturns (lam beta : Nat) : Nat := beta / lam

/-- The budget funds at least `d` returns iff it covers their total cost `d · λ`. -/
theorem le_fundedReturns_iff (lam beta d : Nat) (hlam : 0 < lam) :
    d ≤ fundedReturns lam beta ↔ d * lam ≤ beta := by
  unfold fundedReturns
  exact Nat.le_div_iff_mul_le hlam

/-- **The budgeted self-relation loop**: iterate `σ` as many times as the budget funds. -/
def loopR (σ : X → X) (lam beta : Nat) (x : X) : X := iter σ (fundedReturns lam beta) x

/-- **Bridge, middle form: `loop_R(e) = e ⟺ N(e) ≥ d(e)`.** A stabilizing seed's
budgeted loop is an eigenform iff the budget funds at least the depth-many returns. -/
theorem loopR_isEigen_iff_le_fundedReturns (σ : X → X) (x : X) (d lam beta : Nat)
    (hstab : StabilizesAt σ x d) :
    IsEigen σ (loopR σ lam beta x) ↔ d ≤ fundedReturns lam beta := by
  unfold loopR
  exact hstab (fundedReturns lam beta)

/-- **Bridge, resource form: `loop_R(e) = e ⟺ d·λ ≤ β`.** The budgeted loop is an
eigenform iff the budget covers the cost of reaching the depth. This is the equivalence
that joins A3's fixed-point self to the threshold the sparsity lemmas count with. -/
theorem loopR_isEigen_iff (σ : X → X) (x : X) (d lam beta : Nat) (hlam : 0 < lam)
    (hstab : StabilizesAt σ x d) :
    IsEigen σ (loopR σ lam beta x) ↔ d * lam ≤ beta := by
  rw [loopR_isEigen_iff_le_fundedReturns σ x d lam beta hstab]
  exact le_fundedReturns_iff lam beta d hlam

/-- The attention cost of a self of depth `d`, per-return cost `λ`: the total spent
reaching its eigenform. -/
def selfCost (d lam : Nat) : Nat := d * lam

/-- **Bridge, cost form.** `loop_R(x)` is an eigenform iff the budget covers the self's
cost: `loop_R(x) = x ⟺ selfCost d λ ≤ β`. -/
theorem loopR_isEigen_iff_selfCost (σ : X → X) (x : X) (d lam beta : Nat) (hlam : 0 < lam)
    (hstab : StabilizesAt σ x d) :
    IsEigen σ (loopR σ lam beta x) ↔ selfCost d lam ≤ beta := by
  unfold selfCost
  exact loopR_isEigen_iff σ x d lam beta hlam hstab

/-- A self's cost is at least its depth (each of the `d` returns costs `≥ 1`). -/
theorem depth_le_selfCost (d lam : Nat) (hlam : 1 ≤ lam) : d ≤ selfCost d lam := by
  have h : d * 1 ≤ d * lam := Nat.mul_le_mul (Nat.le_refl d) hlam
  simpa using h

/-- **The cost floor, downstream of the depth posit.** With A3's depth floor `d ≥ 2` and per-return
cost `λ ≥ 1`, every self costs at least `2`. This is **not** a derivation of the floor — it relocates
it: the content is the posit `d ≥ 2` (genuine return, not a one-off), and `2 ≤ d·λ` then follows by
trivial arithmetic. -/
theorem two_le_selfCost (d lam : Nat) (hd : 2 ≤ d) (hlam : 1 ≤ lam) :
    2 ≤ selfCost d lam :=
  Nat.le_trans hd (depth_le_selfCost d lam hlam)

/-! ### A concrete witness: the depth-`d` maturation dynamics

To show `StabilizesAt` is inhabited (the bridge is not vacuous), here is a transparent
model: a forming self at "maturity level" `k ∈ Nat` advances one notch per return,
capping at the eigenform level `d`. -/

/-- Iterating maturation from level `0` reaches `min n d` after `n` returns. -/
theorem iter_matarN (d n : Nat) : iter (fun k => min (k + 1) d) n 0 = min n d := by
  induction n with
  | zero => simp only [iter]; omega
  | succ n ih => simp only [iter, ih]; omega

/-- The maturation dynamics genuinely **stabilizes at depth `d`**: iterating from `0`
is an eigenform iff at least `d` returns have happened. So `StabilizesAt` is inhabited. -/
theorem matarN_stabilizesAt (d : Nat) : StabilizesAt (fun k => min (k + 1) d) 0 d := by
  intro n
  unfold IsEigen
  simp only [iter_matarN]
  omega

/-! ### Capstone: the sparsity cost-floor is now discharged -/

/-- **Step 3, relocating the floor.** A finite collection of selves, each given by its depth
`dᵢ ≥ 2` and per-return cost `λᵢ ≥ 1`, whose total maintenance cost fits the budget `β`, numbers at
most `β / 2`. The floor-`2` hypothesis of `stab_card_le_half` is supplied by `two_le_selfCost` — so
the sparsity bound rests on the **depth posit `dᵢ ≥ 2`** rather than a separately-assumed cost floor.
The depth posit itself is *not* derived here. -/
theorem stab_card_le_half_of_depths (selves : List (Nat × Nat)) (beta : Nat)
    (hd : ∀ p ∈ selves, 2 ≤ p.1) (hlam : ∀ p ∈ selves, 1 ≤ p.2)
    (hbudget : totalSpend (selves.map (fun p => selfCost p.1 p.2)) ≤ beta) :
    selves.length ≤ beta / 2 := by
  have hcost : ∀ c ∈ selves.map (fun p => selfCost p.1 p.2), 2 ≤ c := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact two_le_selfCost p.1 p.2 (hd p hp) (hlam p hp)
  have h := stab_card_le_half (selves.map (fun p => selfCost p.1 p.2)) beta hcost hbudget
  rwa [List.length_map] at h

end RelExist
