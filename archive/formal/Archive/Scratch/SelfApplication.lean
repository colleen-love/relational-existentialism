/-
# The fixed-point combinator via self-application — Lawvere's diagonal as the trace, made concrete

[`ReflexiveSeam`](../RelExist/ReflexiveSeam.lean) proved *abstractly* that on a reflexive object the
Lawvere fixed point **is** the self-application `app a a` (GoI's `Y` — the diagonal and the
trace/feedback are literally the same map). [`GraphModel`](GraphModel.lean) built a concrete non-trivial
reflexive object `Pω` and showed *every continuous endomap has a fixed point* via Knaster–Tarski — but
that fixed point was the **external** least fixed point `OrderHom.lfp`, not the **internal** combinator.
This module closes that last gap: it constructs the genuine **`Y` combinator inside `Pω` by
self-application**, exactly the classical `Y = λf.(λx. f (x x)) (λx. f (x x))`, and proves the
fixed-point law `app f (Y f) = Y f` — with the fixed point produced by the self-application
`app (W f) (W f)`, no external fixpoint operator.

The technical heart is that the **diagonal is Scott-continuous**:

* `selfApp_continuous` — `fun x => app x x` is continuous. The reflexive object *supports
  self-application*: feeding an element to itself is a legitimate continuous operation (the witness
  `insert (code e n) e` packages the one extra code point self-application needs).
* `IsContinuous.comp` — continuity is closed under composition (a finite-`biUnion` pull-back of the
  approximants). So `fun x => app f (app x x)` is continuous, and `Graph` packages it into an element.
* `Wcomb` / `Ycomb` / `Ycomb_fixed` — `W f := Graph (λx. f (x x))`, `Y f := app (W f) (W f)`, and
  `app f (Y f) = Y f`. The fixed point is **literally** the self-application `app (W f) (W f)`: Lawvere's
  diagonal realized as the trace, on a real domain.

**What this settles, and the honest cartesian caveat.** This realizes `fixpoint_is_selfApplication`
concretely and confirms `ReflexiveModel`'s duality from the *construction* side: where a reflexive
object exists, the diagonal **constructs** `Y` (it does not obstruct — the seam is the reflexive
object's *absence*). But be precise about *which* firewall face this is. `Pω` is a model of the
**untyped λ-calculus**, which is **cartesian**: it lives in the cartesian-closed category of domains,
and the self-application `app x x` uses the ambient cartesian diagonal `Δ` to feed `x` to both slots.
So this is the **cartesian** self-application route, not a non-cartesian one. The genuinely
*non-cartesian* reflexive object — a compact/linear one in the GoI/`Int`-construction sense, where `Y`
comes from the **trace** with no cartesian copy — is a different, harder object, and the firewall
constrains it sharply: by `Compact.collapse` a non-trivial compact-closed reflexive object **cannot**
also be cartesian (it would go thin), so the linear `Y` there must be the trace, not a diagonal. That
construction is not built here; `Pω` is the cartesian witness.

**The Bridge B tie.** This is the other end of the bridge from
[`QuantumSeamTrace`](QuantumSeamTrace.lean). The reflexive/self-application route to a Lawvere fixed
point *exists and is constructive* — but it **requires a reflexive object**, which the finite quantum
`ptrace` cannot supply (Cantor bars it in finite/Set models), and which cannot be made compact +
cartesian (the firewall). So the quantum partial-trace seam is left with the *other* face —
no-broadcasting — exactly as mechanized there. Reflexive settings get `Y`-by-self-application
(constructive); compact-finite settings get no-broadcasting (the seam). One firewall, two faces, both
now concrete.

**Honest scope.** A rederivation (the graph-model `Y` is Plotkin–Scott / standard λ-model theory) with
a real mechanization: the diagonal's continuity and the internal combinator's fixed-point law. It does
**not** build the non-cartesian/linear reflexive object, nor full combinatory completeness (`S` is still
absent; `K` is in `GraphModel`).
-/
import Scratch.GraphModel

namespace RelExist.SelfApplication

open Set RelExist.GraphModel

/-- **Composition preserves Scott-continuity.** If `g` and `h` are continuous then so is `g ∘ h`: the
forward direction pulls each finite approximant of `g`'s input back, via `h`'s continuity, to a finite
`biUnion` of approximants of `x`. The fundamental closure property the self-application combinator
needs. -/
theorem IsContinuous.comp {g h : Pω → Pω} (hg : IsContinuous g) (hh : IsContinuous h) :
    IsContinuous (fun x => g (h x)) := by
  intro x n
  constructor
  · intro hn
    obtain ⟨e', he'hx, hne'⟩ := (hg (h x) n).mp hn
    have hchoose : ∀ m ∈ e', ∃ d : Finset ℕ, (↑d ⊆ x) ∧ m ∈ h (↑d) := by
      intro m hm
      exact (hh x m).mp (he'hx (Finset.mem_coe.mpr hm))
    choose! D hDx hmD using hchoose
    refine ⟨e'.biUnion D, ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_biUnion] at hk
      obtain ⟨m, hm, hkm⟩ := hk
      exact hDx m hm (Finset.mem_coe.mpr hkm)
    · have hsub : (↑e' : Set ℕ) ⊆ h (↑(e'.biUnion D)) := by
        intro m hm
        rw [Finset.mem_coe] at hm
        have hmono : ↑(D m) ⊆ (↑(e'.biUnion D) : Set ℕ) := by
          intro k hk
          rw [Finset.mem_coe] at hk ⊢
          exact Finset.mem_biUnion.mpr ⟨m, hm, hk⟩
        exact hh.monotone hmono (hmD m hm)
      exact hg.monotone hsub hne'
  · rintro ⟨e, hex, hne⟩
    exact hg.monotone (hh.monotone hex) hne

/-- **The diagonal is Scott-continuous: the reflexive object supports self-application.** `fun x =>
app x x` is continuous — `app x x` is determined by finite approximants of `x`. Feeding an element to
itself as both function and argument is a legitimate continuous operation; this is what lets the `Y`
combinator be packaged as an element. -/
theorem selfApp_continuous : IsContinuous (fun x => app x x) := by
  intro x n
  show n ∈ app x x ↔ ∃ e : Finset ℕ, (↑e ⊆ x) ∧ n ∈ app (↑e) (↑e)
  constructor
  · rintro ⟨e, hex, hcode⟩
    refine ⟨insert (code e n) e, ?_, ?_⟩
    · rw [Finset.coe_insert]; exact Set.insert_subset hcode hex
    · refine ⟨e, ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.subset_insert _ _
      · rw [Finset.coe_insert]; exact Set.mem_insert _ _
  · rintro ⟨d, hdx, e', he'd, hcode⟩
    exact ⟨e', he'd.trans hdx, hdx hcode⟩

/-- The **doubling former** `λx. f (x x)` is continuous (composition of `app f` with the diagonal), so
it has a graph as a concrete element of `Pω`. -/
theorem doubler_continuous (f : Pω) : IsContinuous (fun x => app f (app x x)) :=
  IsContinuous.comp (app_continuous f) selfApp_continuous

/-- **`W f := λx. f (x x)`**, the self-application kernel of the `Y` combinator, as a concrete element. -/
def Wcomb (f : Pω) : Pω := Graph (fun x => app f (app x x))

/-- **The fixed-point combinator on `f`** — `Y f := (λx. f (x x)) (λx. f (x x)) = app (W f) (W f)`. The
fixed point is produced by **self-application** of `W f` to itself, with no external operator. -/
def Ycomb (f : Pω) : Pω := app (Wcomb f) (Wcomb f)

/-- **The fixed-point law, by self-application.** `app f (Y f) = Y f`: `Y f` is a fixed point of
`app f`, and it *is* the self-application `app (W f) (W f)`. Unfolding `W f`'s graph once (the
retraction `app (Graph k) = k` on the continuous `k = λx. f (x x)`) turns `app (W f) (W f)` into
`app f (app (W f) (W f))`. This is Lawvere's diagonal realized as the trace, concretely in `Pω`. -/
theorem Ycomb_fixed (f : Pω) : app f (Ycomb f) = Ycomb f :=
  (app_graph_of_continuous (doubler_continuous f) (Wcomb f)).symm

/-- **`Y f` is genuinely a fixed point** (the symmetric reading), tying the internal combinator to the
existence guaranteed externally by `GraphModel.continuous_hasFixpoint`: the self-application combinator
exhibits a concrete fixed point of every `app f`, not merely asserts one. -/
theorem Ycomb_isFixed (f : Pω) : Ycomb f = app f (Ycomb f) :=
  (Ycomb_fixed f).symm

end RelExist.SelfApplication
