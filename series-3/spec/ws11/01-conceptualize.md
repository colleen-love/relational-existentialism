# WS11 — Phase 1: Conceptualize (blind register source)

*Output is charter-free by construction; this document is the BR for WS11's blind phases. Timestamp + hash the selected candidate(s) at Phase-2 commit.*

## The mathematical object at stake

Fix an infinite cardinal `κ` and the bounded-powerset endofunctor `PkObj κ : Type u → Type u` (subsets of size `< κ`). For a coalgebra `C : Coalg κ` (a set `C.X` with `C.str : C.X → PkObj κ C.X`), two independent pieces of data are attached to each state `x`:

- **downward data:** the unfolding `C.str x` (the successor set);
- **upward data:** the in-neighbourhood `UpView C x := {z | x ∈ (C.str z).1}` (which states contain `x`).

The question: **can state identity depend non-redundantly on the upward data?** Precisely: characterize the coalgebras in which `str` alone fails to be injective while `str` together with `UpView` jointly separates states — and determine whether any such coalgebra can be strongly extensional (bisimilarity implies equality). Non-trivial because on the terminal coalgebra `νPk κ`, Lambek's lemma makes `str` bijective, so downward data determines identity outright; whether that is an artifact of terminality or a consequence of extensionality in general is exactly what must be decided.

## Shared definitions (all candidates)

```lean
def DownwardDetermined (C : Coalg κ) : Prop :=
  ∀ x y : C.X, C.str x = C.str y → x = y

def UpView (C : Coalg κ) (x : C.X) : Set C.X := {z | x ∈ (C.str z).1}

def StronglyExtensional (C : Coalg κ) : Prop :=
  ∀ R, Bisim C R → ∀ x y, R x y → x = y

def JointlyDetermined (C : Coalg κ) : Prop :=
  ∀ x y : C.X, C.str x = C.str y → UpView C x = UpView C y → x = y

/-- Upward data is load-bearing: downward alone insufficient, joint data sufficient. -/
def UpwardLoadBearing (C : Coalg κ) : Prop :=
  (¬ DownwardDetermined C) ∧ JointlyDetermined C
```

Ambient theory for every candidate: Lean 4 + Mathlib (pinned v4.15.0); the type-theoretic `Cofix`-of-QPF encoding (no set-theoretic AFA axiom); `F = PkObj κ`; no monad `T` and no distributive law are involved.

## Candidates

### K1 — Downward determination on the terminal carrier (record-level)

```lean
theorem ws11_downward_determined (κ : Cardinal.{u}) :
    ∀ x y : (νPk κ).X, (νPk κ).str x = (νPk κ).str y → x = y
```
**Strategy:** `(lambek (νPk_terminal κ)).injective`. One line.
**Success:** compiles. **Failure:** impossible (would refute Lambek); listed only as the anchor fact the other candidates generalize or exploit.

### K2 — The schema: strong extensionality forces downward determination

```lean
theorem ws11_extensional_downward (C : Coalg κ)
    (hext : StronglyExtensional C) : DownwardDetermined C
```
**Strategy:** show `R := fun a b => C.str a = C.str b` is a `Bisim C R`. The Aczel–Mendler witness: for a related pair `⟨(a,b), hab⟩` take `ζ` to be the diagonal copy of the shared successor set (each successor `v` pairs with itself; `R v v` holds by reflexivity of equality of unfoldings). Both projections of `ζ` recover the shared set, so the two projection laws hold definitionally. Then `hext R` finishes.
**Success:** the theorem, at full generality in `C`.
**Failure condition:** the diagonal `ζ` cannot be given the exact shape `Bisim`'s fields demand (would indicate the structure requires more than projection-compatibility; fall back to proving the statement for `νPk κ` only via `ws2_bisim_eq`, reported as Partial-in-generality).

### K3 — Redundancy corollary

```lean
theorem ws11_upward_redundant (C : Coalg κ) (hext : StronglyExtensional C) :
    JointlyDetermined C
```
**Strategy:** immediate from K2 (downward alone suffices, so the joint hypothesis is never needed). Low standalone value; a free corollary that states the redundancy explicitly.
**Failure:** none beyond K2's.

### K4 — The incompatibility (the negative deliverable)

```lean
theorem ws11_no_upward_identity (C : Coalg κ)
    (hext : StronglyExtensional C) : ¬ UpwardLoadBearing C
```
**Strategy:** unfold; the first conjunct of `UpwardLoadBearing` contradicts K2.
**Success:** proved — **strong extensionality and load-bearing upward identity are jointly unsatisfiable**, for every coalgebra of the functor, not only the terminal one.
**Failure condition:** exhibiting a strongly extensional coalgebra with non-injective `str` — believed impossible (it would contradict K2's bisimulation argument); if K2 falls to its fallback, K4 inherits the same scope reduction.

### K5 — The positive witness (the existence deliverable)

```lean
theorem ws11_upward_witness (hinf : ℵ₀ ≤ κ) :
    ∃ C : Coalg κ, UpwardLoadBearing C
```
**Strategy:** the three-state coalgebra on `ULift (Fin 3)` with states `a, b, p`:
`str a = ∅`, `str b = ∅`, `str p = {a}`. Then `str a = str b` with `a ≠ b` (downward fails); `UpView a = {p} ≠ ∅ = UpView b` separates the one bad pair, and all other pairs are separated by `str` — so `JointlyDetermined` holds by finite case analysis (`decide`-friendly after unfolding; cardinality side conditions `0, 1 < κ` from `hinf`).
**Success:** proved — upward-load-bearing identity is *coherent*; by K4 it lives only outside the strongly extensional class.
**Failure condition:** none mathematical; a failure indicates a definitional error in `UpView`/`JointlyDetermined`, to be surfaced, not patched around.

### K6 — The collapse mechanism (what the terminal map does to upward distinctions)

```lean
def IsCoalgHom (C : Coalg κ) (f : C.X → (νPk κ).X) : Prop :=
  ∀ z, (νPk κ).str (f z) = PkMap κ f (C.str z)

theorem ws11_terminal_identifies (C : Coalg κ) {x y : C.X}
    (h : C.str x = C.str y) :
    ∀ f : C.X → (νPk κ).X, IsCoalgHom C f → f x = f y
```
**Strategy:** naturality: `str (f x) = PkMap f (str x) = PkMap f (str y) = str (f y)`, then K1. Applied to K5's witness: the unique map into the terminal coalgebra identifies `a` and `b` — **the terminal quotient erases exactly the distinctions that only upward data carried.**
**Success:** proved; gives the mechanism, not just the fact.
**Failure:** none (elementary naturality); risk is only binding to the exact `∃!`-shape of `IsTerminalCoalg`.

### K7 — Exact characterization via quotient reflection (rejected at conceptualize)

Characterize `UpwardLoadBearing` coalgebras as precisely those whose extensional reflection is non-injective on `str`-fibres. Subsumes K2/K6 but requires building the reflection (quotient by largest bisimulation) as infrastructure. **Rejected:** high cost, no additional decision content over K2 + K5 + K6; noted for a future workstream if the reflection is built for other reasons.

## Trade-off summary

K1/K3 are free but decide nothing alone. K2+K4 decide the negative direction at full generality; K5 decides the positive direction concretely; K6 explains the interaction. K7 buys generality nobody consumes. The natural bundle is {K2, K4, K5, K6} with K1, K3 as corollaries — a two-sided resolution: the property is impossible inside the strongly extensional class and realized outside it, with the terminal morphism as the exact destruction mechanism.
