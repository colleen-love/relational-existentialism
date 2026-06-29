/-
# Handoff XII — faithful A2: relation-primacy *as priority* (no bare carrier)

A2's *text* is an ontological **priority** claim — relation is prior to the related; there is no bare
carrier beneath the relational unfolding; a state *is* its relating, with no residue. Its previous
mechanization was `≈ ⊊ ≅` (`Archive/Scratch/Identity.lean`) — the strict containment of two equivalence
relations. **Those are not the same claim.** `≈ ⊊ ≅` is a *downstream signature* of priority (one step
removed), and it is even compatible with a bare carrier: hidden state finer than `≈` reads the strictness as
"behaviour under-determines identity," the *opposite* of no-bare-carrier. So that mechanization can hold in a
world A2's text rules out.

This file formalizes the **priority itself** — "no bare carrier" — directly, as the **strong extensionality**
(final-coalgebra property) of the world of selves `𝔼 = D/≈`, built on `We.bisim` (`≈ := νΘ`).

## What "no bare carrier" means here, and its status

The behaviour functor's unfolding is `Θ` (`We.Step`); `≈ := νΘ` is behavioural equality (bisimilarity). The
world of selves `𝔼 = D/≈` (`We.World`) carries the **quotient coalgebra** `(obsQ, stepQ)` — `Θ` descends to
`≈`-classes (`obsQ_mk`, `stepQ` defined `≈`-saturated). "No bare carrier — a state *is* its behaviour, no
residue" is then exactly:

> **`bisim_quotient_eq`** : on `𝔼 = D/≈`, bisimilarity *is* equality — `bisim obsQ stepQ p q ↔ p = q`.

This is **strong extensionality**: in the world of selves, every behavioural identity is a literal identity
and every distinction is a behavioural distinction — there is no individuation finer than `≈`, no bare
carrier underneath. It is the defining property of a **final coalgebra**; `𝔼` is the minimal realization into
which every coalgebra maps with kernel exactly `≈`.

**Status (Part B's honest report).** Priority here is:

* **(a) definitional** in that *choosing* `𝔼 = D/≈` as the space of selves already *is* the no-bare-carrier
  commitment (you have identified states with their behaviours); **and**
* **(b) derivable** in that this choice is *canonical*, not arbitrary: `bisim_quotient_eq` proves `𝔼` is
  strongly extensional (a final-coalgebra property), so nothing finer than `≈` survives — the commitment is
  coherent and forced, **not** (c) an extra posit. It holds for **every** `(obs, step)` (`priority_universal`).

## Part C — the surplus does **not** follow from priority

`≈ ⊊ ≅` is about the gap *above* `≈` (restricted observation `≅` is lossy); priority is about what lies
*below* `≈`. They are independent: priority (`bisim_quotient_eq`) holds **universally**, yet `≈ ⊊ ≅` **fails**
for deterministic systems (`Identity.deterministic_bisim_iff_obsEq`: there `≈ = ≅`). A claim that holds always
cannot entail one that sometimes fails. So the surplus needs an **independent premise** — that `≅` fails to be
a bisimulation (`Identity.surplus_iff_obsEq_not_isBisimulation`) — which priority does not supply.

## Part D — the seam supplies the lossiness, not priority

The premise Part C needs — `≅` is lossy (not a bisimulation) — is exactly the **seam** (3.3,
`KnowingFeeling`): *you cannot completely view from outside what you relate to.* So A2 faithfully modelled is
**two named pieces**: priority (this file, the bottom) **+** the seam supplying the surplus from above — not
one claim. Outcome **2 (clarified-as-two)**, with the bridge named: `≈ ⊊ ≅` is sourced from the seam, never
from priority. See [`docs/spec/02-axioms.md`](../../docs/spec/02-axioms.md) for the A2a/A2b split.
-/
import Theory.We

namespace Theory.Priority

open Theory.We

variable {X O : Type*}

/-! ### One-step destructors for `≈` (from `bisim_unfold`) -/

/-- Bisimilar states share the immediate observation. -/
theorem bisim_obs {obs : X → O} {step : X → X → Prop} {a b : X} (h : bisim obs step a b) :
    obs a = obs b := by rw [← bisim_unfold] at h; exact h.1

/-- Forward matching: a successor of `a` is matched by a `≈`-related successor of `b`. -/
theorem bisim_fwd {obs : X → O} {step : X → X → Prop} {a b a' : X} (h : bisim obs step a b)
    (ha' : step a a') : ∃ b', step b b' ∧ bisim obs step a' b' := by
  rw [← bisim_unfold] at h; exact h.2.1 a' ha'

/-- Backward matching: a successor of `b` is matched by a `≈`-related successor of `a`. -/
theorem bisim_bwd {obs : X → O} {step : X → X → Prop} {a b b' : X} (h : bisim obs step a b)
    (hb' : step b b') : ∃ a', step a a' ∧ bisim obs step a' b' := by
  rw [← bisim_unfold] at h; exact h.2.2 b' hb'

/-! ### The quotient coalgebra on the world of selves `𝔼 = D/≈` -/

/-- The self of a state — its `≈`-class in `𝔼 = D/≈`. -/
abbrev selfOf (obs : X → O) (step : X → X → Prop) (a : X) : World obs step :=
  Quotient.mk (bisimSetoid obs step) a

/-- The observation descends to selves: bisimilar states agree on `obs` (`bisim_obs`), so `obsQ` is
well-defined on `𝔼`. -/
def obsQ (obs : X → O) (step : X → X → Prop) : World obs step → O :=
  Quotient.lift obs (fun _ _ h => bisim_obs h)

@[simp] theorem obsQ_mk (obs : X → O) (step : X → X → Prop) (a : X) :
    obsQ obs step (selfOf obs step a) = obs a := rfl

/-- The transition descends to selves, `≈`-saturated: `⟦a⟧ → ⟦b⟧` iff some representatives step. This is the
quotient coalgebra structure `Θ` carries on `𝔼` — the behaviour functor lives on `D/≈` directly. -/
def stepQ (obs : X → O) (step : X → X → Prop) (p q : World obs step) : Prop :=
  ∃ a b, selfOf obs step a = p ∧ selfOf obs step b = q ∧ step a b

theorem stepQ_mk {obs : X → O} {step : X → X → Prop} {a b : X} (h : step a b) :
    stepQ obs step (selfOf obs step a) (selfOf obs step b) := ⟨a, b, rfl, rfl, h⟩

/-! ### No bare carrier: `𝔼` is strongly extensional -/

/-- **No bare carrier (priority).** On the world of selves `𝔼 = D/≈`, bisimilarity *is* equality. A self is
exactly its behaviour, with no residue beneath `≈`: every behavioural identity is a literal identity, and
there is no individuation finer than `≈`. This is the **strong extensionality / final-coalgebra** property —
`𝔼` is the minimal realization, with kernel exactly `≈`. Priority is thus not a separate posit but the
*canonical coherence* of taking `𝔼 = D/≈` as the space of selves (`bisim_unfold` makes `≈` the greatest
bisimulation, and `𝔼` inherits no finer one). -/
theorem bisim_quotient_eq (obs : X → O) (step : X → X → Prop) (p q : World obs step) :
    bisim (obsQ obs step) (stepQ obs step) p q ↔ p = q := by
  constructor
  · -- the pulled-back relation on `X` is a bisimulation, hence below `≈ := νΘ`
    have hbis : ∀ x y,
        bisim (obsQ obs step) (stepQ obs step) (selfOf obs step x) (selfOf obs step y) →
        (Step obs step)
          (fun x y => bisim (obsQ obs step) (stepQ obs step) (selfOf obs step x) (selfOf obs step y))
          x y := by
      intro x y hxy
      rw [← bisim_unfold] at hxy
      obtain ⟨hobs, hf, hb⟩ := hxy
      refine ⟨hobs, ?_, ?_⟩
      · -- forward: a step of `x` is matched by a step of `y`, up to `≈`
        intro x' hx'
        obtain ⟨Q, hQ, hQbis⟩ := hf (selfOf obs step x') (stepQ_mk hx')
        obtain ⟨y0, y', hy0, hQ', hstep⟩ := hQ
        have hy0y : bisim obs step y0 y := Quotient.exact hy0
        obtain ⟨y'', hyy'', hbis''⟩ := bisim_fwd hy0y hstep
        refine ⟨y'', hyy'', ?_⟩
        show bisim (obsQ obs step) (stepQ obs step) (selfOf obs step x') (selfOf obs step y'')
        have hQeq : selfOf obs step y'' = Q := by
          rw [← hQ']; exact Quotient.sound (bisim_symm obs step hbis'')
        rw [hQeq]; exact hQbis
      · -- backward, symmetric
        intro y' hy'
        obtain ⟨P, hP, hPbis⟩ := hb (selfOf obs step y') (stepQ_mk hy')
        obtain ⟨x0, x', hx0, hP', hstep⟩ := hP
        have hx0x : bisim obs step x0 x := Quotient.exact hx0
        obtain ⟨x'', hxx'', hbis''⟩ := bisim_fwd hx0x hstep
        refine ⟨x'', hxx'', ?_⟩
        show bisim (obsQ obs step) (stepQ obs step) (selfOf obs step x'') (selfOf obs step y')
        have hPeq : selfOf obs step x'' = P := by
          rw [← hP']; exact Quotient.sound (bisim_symm obs step hbis'')
        rw [hPeq]; exact hPbis
    intro hpq
    obtain ⟨a, rfl⟩ := Quotient.exists_rep p
    obtain ⟨b, rfl⟩ := Quotient.exists_rep q
    exact Quotient.sound (bisim_of_bisimulation obs step hbis hpq)
  · rintro rfl; exact bisim_refl _ _ _

/-- **Priority is universal.** Strong extensionality of `𝔼 = D/≈` holds for *every* coalgebra `(obs, step)`:
no-bare-carrier is not a property of special systems but the structure of the behavioural quotient itself.
(This is exactly why it cannot, alone, force the system-dependent surplus `≈ ⊊ ≅` — Part C.) -/
theorem priority_universal (obs : X → O) (step : X → X → Prop) :
    ∀ p q : World obs step, bisim (obsQ obs step) (stepQ obs step) p q ↔ p = q :=
  bisim_quotient_eq obs step

end Theory.Priority
