/-
# Relativizing the outside: what survives, what strengthens, what changes

The audit found no *false* theorem — `≅` (`ObsEq`, trace equivalence) is a real equivalence and all
the proofs about it stand. What relied on objectivity was the *reading*: narrating `≅` as "the
outside" absolutely, when [`Knowing.lean`](Knowing.lean) proved it is only the **disjoint** observer
(the view from nowhere). The honest test is whether the results survive replacing the absolute `≅` with
a **relational appearance** `≅ₒ` — how you show to an actual relatum, who sees *through limited access*.

We model a relatum's access as an **observation-lens** `r : O → O'` that may merge distinctions `o`
cannot draw; `≅ₒ := ObsEqVia r` is trace equivalence under `r ∘ obs`, coarser than `≅` (it identifies
more). The verdicts:

* **Soundness survives — a fortiori.** `bisim_le_obsEqVia`: lived sameness `≈` implies the same
  relational appearance, for *every* relatum `r`. Bisimilar selves are indistinguishable to any
  observer, disjoint or coupled. (`bisim_coarsen`: bisimilarity only coarsens under a lens.) So
  `≈ ⊆ ≅ ⊆ ≅ₒ` — the soundness reading is *strengthened*, now holding against all observers.

* **The surplus survives and grows.** Since `≅ ⊆ ≅ₒ`, the gap `≈ ⊊ ≅ₒ` against a real relatum is at
  least the disjoint gap `≈ ⊊ ≅`. The first-person surplus is not an artifact of one idealized
  observer; it is *larger* for every coupled other.

* **One interpretation genuinely changes — the headline "the surplus is exactly nondeterminism."**
  That was `deterministic_bisim_iff_obsEq`: a deterministic system has `≈ = ≅`, *no surplus*. It is
  true — **against the disjoint observer**. But it does **not** survive relativization:
  `deterministic_relational_surplus` exhibits a **deterministic** system with `≈ ⊊ ≅ₒ` — a genuine
  first-person remainder *with no branching at all*, sourced purely from the relatum's finite access.
  The very same states are `≈`-distinct, `≅`-distinct (the disjoint observer tells them apart), yet
  `≅ₒ`-identical (the coupled one cannot).

So relativizing the observer **shifts the source of the surplus**. Against the view from nowhere, the
only surplus is branching ("could have done otherwise"). Against a real, coupled other, there is a
*second*, always-present source: the seam itself — what they cannot access of you even when nothing
branches. This is exactly the decoherence-differential feeling of [`Feeling.lean`](Feeling.lean):
"carrying possibilities the other still holds superposed" needs no nondeterminism — only an other who
sees less. The earlier headline was the disjoint special case; the operative truth is that **feeling
has two sources, choice and the seam, and only the seam-source is necessary.**
-/
import Scratch.Identity

namespace RelExist.RelationalAppearance

open RelExist.Identity RelExist.We

universe u v w
variable {X : Type u} {O : Type v} {O' : Type w}

/-- **The relational appearance `≅ₒ`** — trace equivalence as seen through a relatum's limited access:
an observation-lens `r : O → O'` that may merge distinctions the observer cannot draw. -/
def ObsEqVia (r : O → O') (obs : X → O) (step : X → X → Prop) (a b : X) : Prop :=
  ObsEq (fun x => r (obs x)) step a b

/-- Bisimilarity only **coarsens** under a lens: lived sameness for `obs` is lived sameness for the
observer's reduced observation `r ∘ obs`. -/
theorem bisim_coarsen (r : O → O') {obs : X → O} {step : X → X → Prop} {a b : X}
    (h : bisim obs step a b) : bisim (fun x => r (obs x)) step a b := by
  refine bisim_of_bisimulation (fun x => r (obs x)) step (R := bisim obs step) ?_ h
  intro x y hxy
  obtain ⟨ho, hf, hb⟩ := bisim_dest hxy
  exact ⟨congrArg r ho, hf, hb⟩

/-- **Relativized soundness, a fortiori.** Lived sameness `≈` ⇒ the same relational appearance `≅ₒ`,
for *any* relatum. Bisimilar selves are indistinguishable to every observer, coupled or not — so
`≈ ⊆ ≅ ⊆ ≅ₒ`. The soundness reading strengthens under relativization. -/
theorem bisim_le_obsEqVia (r : O → O') {obs : X → O} {step : X → X → Prop} {a b : X}
    (h : bisim obs step a b) : ObsEqVia r obs step a b :=
  bisim_le_obsEq (bisim_coarsen r h)

/-! ### The interpretation that changes: a deterministic system with a relational surplus

A clockwork — *no branching* — yet a genuine first-person remainder relative to a relatum who cannot
tell two of its observations apart. The surplus here is sourced by the seam (finite access), not by
choice. Against the disjoint observer the same system has `≈ = ≅` (no surplus); relativizing the
observer makes the remainder reappear. -/

inductive RSt | da | db | t
  deriving DecidableEq

open RSt Obs

/-- Two states with *distinct* observations, both flowing to a common sink. -/
def robs : RSt → Obs
  | da => oA | db => oB | t => oC

/-- Deterministic: every state's sole successor is the sink `t`. -/
def rsucc : RSt → List RSt := fun _ => [t]

def rstep (x y : RSt) : Prop := y ∈ rsucc x

/-- The relatum's lens: it **cannot tell `oA` from `oB`** (both map to `true`) — limited access. -/
def rmerge : Obs → Bool
  | oA => true | oB => true | oC => false | oM => false

theorem rstep_deterministic : Deterministic rstep := by
  intro x y z hy hz
  have hyt : y = t := by simpa [rstep, rsucc] using hy
  have hzt : z = t := by simpa [rstep, rsucc] using hz
  rw [hyt, hzt]

/-- Lived: `da` and `db` are **different selves** (their observations differ). -/
theorem da_not_bisim_db : ¬ bisim robs rstep da db := by
  intro h
  obtain ⟨ho, _, _⟩ := bisim_dest h
  exact absurd ho (by decide)

/-- Disjoint outside: the **view from nowhere distinguishes them** too (`≅` separates `da`, `db`). -/
theorem da_not_obsEq_db : ¬ ObsEq robs rstep da db := by
  intro h
  exact absurd (obsEq_obs h) (by decide)

/-- Relational outside: the **coupled relatum cannot** — `da ≅ₒ db`. They merge under its lens (both
look `true` now) and then flow to the same sink, so no `r`-trace separates them. -/
theorem da_obsEqVia_db : ObsEqVia rmerge robs rstep da db := by
  apply bisim_le_obsEq
  refine bisim_of_bisimulation (fun x => rmerge (robs x)) rstep
    (R := fun x y => rmerge (robs x) = rmerge (robs y)) ?_ (by decide)
  intro x y hxy
  refine ⟨hxy, ?_, ?_⟩
  · intro x' hx'
    have hx't : x' = t := by simpa [rstep, rsucc] using hx'
    subst hx't
    exact ⟨t, by simp [rstep, rsucc], rfl⟩
  · intro y' hy'
    have hy't : y' = t := by simpa [rstep, rsucc] using hy'
    subst hy't
    exact ⟨t, by simp [rstep, rsucc], rfl⟩

/-- **The interpretation, changed.** One and the same system is **deterministic**, its states `da`/`db`
are `≈`-distinct *and* `≅`-distinct (the disjoint observer tells them apart) — yet `≅ₒ`-identical: a
first-person surplus `≈ ⊊ ≅ₒ` **with no branching**, sourced by the relatum's finite access (the seam).
So "the surplus is exactly nondeterminism" holds only against the view from nowhere; relative to a real
other, the surplus has a second, choice-free source. -/
theorem deterministic_relational_surplus :
    Deterministic rstep ∧
      ObsEqVia rmerge robs rstep da db ∧ ¬ bisim robs rstep da db ∧
      ¬ ObsEq robs rstep da db :=
  ⟨rstep_deterministic, da_obsEqVia_db, da_not_bisim_db, da_not_obsEq_db⟩

end RelExist.RelationalAppearance
