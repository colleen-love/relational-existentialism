/-
# A concrete non-trivial reflexive object: Pω, the Plotkin–Scott graph model

This is the construction route 1 needed and `ReflexiveModel` flagged as `[open]`: a **non-trivial**
reflexive object — `[D →cont D]` a genuine retract of `D` — built concretely in Lean. Following
Plotkin and Scott (1970s), the carrier is `Pω := Set ℕ`, with application

    a · b = { n | ∃ finite e ⊆ b, ⟨e, n⟩ ∈ a }

(a finite "input approximant" `e` produces output `n` if `a` records that, and `e` is contained in the
argument `b`). The **graph** of a function packages it back into a set,

    Graph f = { ⟨e, n⟩ | n ∈ f ↑e },

and the heart of the model is the **retraction** `app (Graph f) = f` for **continuous** `f`
(`app_graph_of_continuous`): every continuous self-map of `Pω` *is* `app a` for a concrete `a` — so the
continuous functions are a retract of `Pω`. That is a reflexive object (for continuous maps).

**What is built (turns 1–2).** The **reflexive object itself**: `app`/`Graph` exhibit the continuous
self-maps as a *retract* of `Pω` (`app_graph_of_continuous`, `app_continuous`,
`app_pointSurjective_onContinuous`), and every continuous endomap has a fixed point
(`continuous_hasFixpoint`) — GoI's `Y` on a concrete infinite domain. This is the non-trivial reflexive
object `ReflexiveModel` flagged as the `[open]` part of route 1, now constructed.

**Honest scope.** A known construction (Plotkin–Scott, a rederivation) and a substantial *mechanization*.
It is a reflexive object for **continuous** maps only — *not* all set-functions (Cantor bars that; cf.
`ReflexiveModel`). By the duality of `ReflexiveModel`, it realizes the **construction** side (it hosts
`Y` / least fixed points of continuous maps — and indeed *every* continuous endomap *settles*, so there
is no obstruction here), **not** the seam — the seam is the non-existence of a reflexive observation
into a *settling-refusing* target, which is already a theorem and which Pω, being a construction, does
not touch. What is **not** built: full combinatory completeness (`S`, `K`, interpreting arbitrary
λ-terms) and an explicit embedding of `Pω` as an object of a traced SMC — the reflexive object is done;
the full λ-algebra / categorical packaging is further work.
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

namespace RelExist.GraphModel

open Set

/-- The carrier of the graph model: sets of naturals. -/
abbrev Pω : Type := Set ℕ

/-- Code a finite input-approximant `e` and an output `n` as a single natural `⟨e, n⟩`. -/
def code (e : Finset ℕ) (n : ℕ) : ℕ := Nat.pair (Encodable.encode e) n

/-- The coding is injective. -/
theorem code_inj {e e' : Finset ℕ} {n n' : ℕ} (h : code e n = code e' n') : e = e' ∧ n = n' := by
  rw [code, code, Nat.pair_eq_pair] at h
  exact ⟨Encodable.encode_injective h.1, h.2⟩

/-- **Application** — the graph model's `·`: `n ∈ a · b` iff some finite approximant `e ⊆ b` has
`⟨e, n⟩` recorded in `a`. -/
def app (a b : Pω) : Pω := {n | ∃ e : Finset ℕ, (↑e ⊆ b) ∧ code e n ∈ a}

@[simp] theorem mem_app {a b : Pω} {n : ℕ} :
    n ∈ app a b ↔ ∃ e : Finset ℕ, (↑e ⊆ b) ∧ code e n ∈ a := Iff.rfl

/-- **The graph (section)**: package a function back into a set of `⟨e, n⟩` codes. -/
def Graph (f : Pω → Pω) : Pω := {m | ∃ (e : Finset ℕ) (n : ℕ), m = code e n ∧ n ∈ f (↑e)}

/-- Membership in a graph is decoding: `⟨e, n⟩ ∈ Graph f ↔ n ∈ f ↑e`. -/
theorem mem_graph {f : Pω → Pω} {e : Finset ℕ} {n : ℕ} :
    code e n ∈ Graph f ↔ n ∈ f (↑e) := by
  constructor
  · rintro ⟨e', n', heq, hmem⟩
    obtain ⟨rfl, rfl⟩ := code_inj heq
    exact hmem
  · intro h; exact ⟨e, n, rfl, h⟩

/-- **Scott continuity** (the algebraic form): a function is determined by its values on finite
approximants — `n ∈ f x` iff `n ∈ f ↑e` for some finite `e ⊆ x`. -/
def IsContinuous (f : Pω → Pω) : Prop :=
  ∀ (x : Pω) (n : ℕ), n ∈ f x ↔ ∃ e : Finset ℕ, (↑e ⊆ x) ∧ n ∈ f (↑e)

/-- **The retraction — the heart of the model.** For continuous `f`, `app (Graph f) = f`: every
continuous self-map of `Pω` *is* application of a concrete element (`Graph f`). So the continuous
functions are a **retract** of `Pω` — `Pω` is a reflexive object for continuous maps. -/
theorem app_graph_of_continuous {f : Pω → Pω} (hf : IsContinuous f) (x : Pω) :
    app (Graph f) x = f x := by
  ext n
  rw [mem_app]
  simp only [mem_graph]
  exact (hf x n).symm

/-- **Application yields continuous functions.** Every `app a` is continuous — so the image of `app`
is exactly the continuous self-maps, and with the retraction the continuous functions are precisely the
retract `[Pω →cont Pω] ◁ Pω`. -/
theorem app_continuous (a : Pω) : IsContinuous (app a) := by
  intro x n
  simp only [mem_app]
  constructor
  · rintro ⟨e, hex, hcode⟩
    exact ⟨e, hex, e, subset_rfl, hcode⟩
  · rintro ⟨e, hex, e', he'e, hcode⟩
    exact ⟨e', he'e.trans hex, hcode⟩

/-! ### Turn 2: the construction side — point-surjectivity onto continuous maps, and the fixpoint -/

/-- Continuity implies monotonicity (more input can only add output). -/
theorem IsContinuous.monotone {f : Pω → Pω} (hf : IsContinuous f) : Monotone f := by
  intro x y hxy n hn
  obtain ⟨e, hex, hfe⟩ := (hf x n).mp hn
  exact (hf y n).mpr ⟨e, hex.trans hxy, hfe⟩

/-- **`app` is point-surjective onto the continuous maps.** Every continuous `f` is `app (Graph f)` —
the precise sense in which `Pω` is a reflexive object: `[Pω →cont Pω]` is a retract, with section
`Graph` and retraction `app`. -/
theorem app_pointSurjective_onContinuous {f : Pω → Pω} (hf : IsContinuous f) :
    ∃ a : Pω, ∀ x, app a x = f x :=
  ⟨Graph f, app_graph_of_continuous hf⟩

/-- **The construction side, realized — GoI's `Y` on a real domain.** Every continuous self-map of
`Pω` has a fixed point (Knaster–Tarski on the complete lattice `Set ℕ`, since continuous ⇒ monotone).
This is the reflexive object *doing its work*: it hosts fixed points of every continuous endomap — the
`Y`-combinator made concrete. (By `ReflexiveModel`'s duality, this is the *construction*, not the seam:
every continuous endomap *settles*, so there is no obstruction here, exactly as expected.) -/
theorem continuous_hasFixpoint {f : Pω → Pω} (hf : IsContinuous f) : ∃ x : Pω, f x = x :=
  ⟨OrderHom.lfp ⟨f, hf.monotone⟩, OrderHom.map_lfp ⟨f, hf.monotone⟩⟩

end RelExist.GraphModel
