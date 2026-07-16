/-
`series-06/formal/ws1.lean`

WS1 — **The process and its gate.** Series 06, blocking workstream.

This file is SELF-CONTAINED: it carries its own copy of the finite-approximation
carrier (the final ω-chain of the κ-bounded powerset functor `P_κ`, `Approx κ n`),
the un-quotiented stagewise process `Proc κ`, the process Ω (`omegaProc`), and the
liveness notion of genuine global atomlessness (`Productive`). Nothing is imported
from `series-04/`, `series-05/`, or `archive/`.

Design doc: `series-06/spec/ws1-design.md`; shared objects `series-06/spec/README.md` §2.
Winning candidate C2 (stagewise un-quotiented process over `νPk`), stagewise identity.

BUILD FINDING (recorded in `charter-status.md`, routed to the WS1 design). The gate
`ws1_productive_plurality` (a productive plurality on `Proc`) is **NOT** deliverable on
C2: each `Approx κ n` is *finite*, and hereditary non-emptiness (honest global
atomlessness) forces the *unique* value `omegaApprox κ n` at every stage. Hence Ω is the
**unique** productive thread (`ws1_productive_unique`) and productive plurality is
impossible (`ws1_no_productive_plurality`). This is the pre-registered WS1-D2 failure
clause — the Static Collapse reappearing inside every founded approximation — an
**Impossibility proved** for the stagewise encoding, triggering the charter's carrier-home
escalation (guarded → metric → pro-object). The metric home C4 is owed, not built here.

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` /
`Quot.sound`.
-/
import Mathlib

universe u

namespace Series06.WS1

open Cardinal

variable {κ : Cardinal.{u}}

/-! ## The κ-bounded powerset functor `P_κ` (carrier foundation, transcribed) -/

/-- `PkObj κ X` — the subsets of `X` of cardinality `< κ`. -/
def PkObj (κ : Cardinal.{u}) (X : Type u) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}

/-- The functorial action of `P_κ` on maps. -/
def PkMap (κ : Cardinal.{u}) {X Y : Type u} (f : X → Y) (s : PkObj κ X) : PkObj κ Y :=
  ⟨f '' s.1, lt_of_le_of_lt Cardinal.mk_image_le s.2⟩

@[simp] lemma PkMap_val {X Y : Type u} (f : X → Y) (s : PkObj κ X) :
    (PkMap κ f s).1 = f '' s.1 := rfl

lemma mk_empty_lt {α : Type u} (hinf : ℵ₀ ≤ κ) : Cardinal.mk (↥(∅ : Set α)) < κ := by
  haveI : IsEmpty (↥(∅ : Set α)) := ⟨fun x => (Set.mem_empty_iff_false _).mp x.2⟩
  rw [Cardinal.mk_eq_zero]
  exact lt_of_lt_of_le Cardinal.aleph0_pos hinf

lemma mk_singleton_lt {α : Type u} (hinf : ℵ₀ ≤ κ) (a : α) :
    Cardinal.mk (↥({a} : Set α)) < κ := by
  rw [Cardinal.mk_singleton]
  exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf

/-! ## The finite-approximation tower (README §2)

`Approx κ n` is the `n`-fold `P_κ` over the closed bud `PUnit`; `trunc` (the final-chain
projection `π_n`) forgets the deepest layer. Every `Approx κ n` is a **founded** object. -/

/-- The final ω-chain of `P_κ`: `A 0 = PUnit` (the closed bud), `A (n+1) = P_κ (A n)`. -/
def Approx (κ : Cardinal.{u}) : ℕ → Type u
  | 0     => PUnit.{u+1}
  | (n+1) => PkObj κ (Approx κ n)

/-- The truncation `π_n : A (n+1) → A n`, forgetting the deepest layer. -/
def trunc (κ : Cardinal.{u}) : (n : ℕ) → Approx κ (n+1) → Approx κ n
  | 0     => fun _ => PUnit.unit
  | (n+1) => fun s => PkMap κ (trunc κ n) s

/-! ## Finiteness of every approximation — the load-bearing structural fact

`Approx κ n` is finite (its cardinality is a tower of exponentials, `2 ↑↑ n`). This is
why (a) the Cantor residue realises as a concrete bounded element (WS3), and (b) hereditary
non-emptiness collapses to a single value (the gate finding below). -/

instance : Finite (Approx κ 0) := by show Finite PUnit.{u+1}; infer_instance
instance : Subsingleton (Approx κ 0) := by show Subsingleton PUnit.{u+1}; infer_instance

instance approx_finite : ∀ n, Finite (Approx κ n)
  | 0 => by show Finite PUnit.{u+1}; infer_instance
  | (n+1) => by
      haveI : Finite (Approx κ n) := approx_finite n
      haveI : Finite (Set (Approx κ n)) := inferInstance
      show Finite (PkObj κ (Approx κ n))
      exact Finite.of_injective (fun s : PkObj κ (Approx κ n) => s.1)
        (fun a b h => Subtype.ext h)

/-- On a finite base, every set is `< κ`-bounded (`κ ≥ ℵ₀`), so it is a genuine `P_κ`
element. This is the realisation map turning any subset into a stage-`(n+1)` element. -/
noncomputable def toPk (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) : PkObj κ X :=
  ⟨s, by
    haveI : Finite (↥s) := Subtype.finite
    exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite (↥s)) hinf⟩

@[simp] lemma toPk_val (hinf : ℵ₀ ≤ κ) {X : Type u} [Finite X] (s : Set X) :
    (toPk hinf s).1 = s := rfl

/-! ## The process carrier `Proc` (README §2, WS1 candidate C2) -/

/-- A **process**: a compatible thread of founded approximations. Kept **un-quotiented**
(stagewise identity); we do NOT pass to the terminal-coalgebra behavioral quotient — that
quotient is exactly the completion the Static Collapse (WS2) is a fact about. -/
def Proc (κ : Cardinal.{u}) : Type u :=
  { x : (n : ℕ) → Approx κ n // ∀ n, trunc κ n (x (n+1)) = x n }

/-- **D1 — stagewise identity.** Two processes are equal iff they agree at every finite
stage. Finer than bisimulation (history-distinguishing), coarser than raw intensional
junk. Plurality, where it exists, lives in this gap. -/
theorem proc_ext (x y : Proc κ) : x = y ↔ ∀ n, x.1 n = y.1 n := by
  constructor
  · rintro rfl n; rfl
  · intro h; exact Subtype.ext (funext h)

/-- Alias with the design's name. -/
theorem ws1_stagewise_id (x y : Proc κ) : x = y ↔ ∀ n, x.1 n = y.1 n := proc_ext x y

/-- **D2 (non-collapse half) — differ at a stage ⇒ distinct.** Immediate from `proc_ext`;
crucially it needs *no* refutation of a bisimulation, because `Proc` carries none. -/
theorem ws1_no_collapse (x y : Proc κ) (n : ℕ) (h : x.1 n ≠ y.1 n) : x ≠ y := by
  intro he; exact h (by rw [he])

/-! ## Ω as a process, and its productivity -/

/-- Ω's depth-`n` approximation: the truncated self-loop `{Ω}`. -/
noncomputable def omegaApprox (hinf : ℵ₀ ≤ κ) : (n : ℕ) → Approx κ n
  | 0     => PUnit.unit
  | (n+1) => ⟨{omegaApprox hinf n}, mk_singleton_lt hinf _⟩

lemma omegaApprox_succ (hinf : ℵ₀ ≤ κ) (n : ℕ) :
    (omegaApprox hinf (n+1) : Approx κ (n+1)) = ⟨{omegaApprox hinf n}, mk_singleton_lt hinf _⟩ :=
  rfl

/-- Ω is a compatible thread. -/
theorem omega_compat (hinf : ℵ₀ ≤ κ) :
    ∀ n, trunc κ n (omegaApprox hinf (n+1)) = omegaApprox hinf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show PkMap κ (trunc κ n) (omegaApprox hinf (n+2)) = omegaApprox hinf (n+1)
      apply Subtype.ext
      rw [omegaApprox_succ, PkMap_val]
      show (trunc κ n) '' ({omegaApprox hinf (n+1)} : Set (Approx κ (n+1))) = {omegaApprox hinf n}
      rw [Set.image_singleton, ih]

/-- **Ω as a process.** The canonical inhabitant. -/
noncomputable def omegaProc (hinf : ℵ₀ ≤ κ) : Proc κ :=
  ⟨omegaApprox hinf, omega_compat hinf⟩

/-- **D1 — the process exists.** -/
theorem ws1_process_exists (hinf : ℵ₀ ≤ κ) : Nonempty (Proc κ) := ⟨omegaProc hinf⟩

/-! ## Genuine global atomlessness = productivity (README §2)

`allNonempty n s` says the depth-`n` tree `s` has a nonempty successor set at every node
(no leaf, no atom, hereditarily). `Productive x` demands it at every stage — the honest
"no leaf anywhere" liveness. -/

/-- Hereditary non-emptiness of a depth-`n` approximation. -/
def allNonempty (κ : Cardinal.{u}) : (n : ℕ) → Approx κ n → Prop
  | 0,     _ => True
  | (n+1), s => s.1.Nonempty ∧ ∀ t ∈ s.1, allNonempty κ n t

/-- **Productivity** — genuine global atomlessness: every founded approximation is
hereditarily nonempty (no atom anywhere). -/
def Productive (x : Proc κ) : Prop := ∀ n, allNonempty κ n (x.1 n)

/-- Ω is hereditarily nonempty at every stage. -/
theorem omega_allNonempty (hinf : ℵ₀ ≤ κ) :
    ∀ n, allNonempty κ n (omegaApprox hinf n) := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [omegaApprox_succ]; exact ⟨omegaApprox hinf n, rfl⟩
      · intro t ht
        rw [omegaApprox_succ] at ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact ih

/-- **D3 — Ω recovered as the productive self-loop.** -/
theorem ws1_omega_process (hinf : ℵ₀ ≤ κ) : Productive (omegaProc hinf) :=
  omega_allNonempty hinf

/-- **D3 — Ω never closes.** Ω is self-membered (complete in extent) yet has a nonempty
successor set at every stage: closed at no depth. -/
theorem ws1_omega_nonclosing (hinf : ℵ₀ ≤ κ) :
    ∀ n, (omegaApprox hinf (n+1) : Approx κ (n+1)).1.Nonempty := by
  intro n; exact ⟨omegaApprox hinf n, rfl⟩

/-! ## THE GATE — and its collapse (the WS1 finding)

Hereditary non-emptiness forces a **unique** value at every stage. So the only productive
thread is Ω, and productive plurality is impossible on `Proc`. This is the Static Collapse
(WS2) reappearing inside the founded approximations: the honestly atom-free finite carrier
cannot host a plurality either. Pre-registered WS1-D2 failure clause; **Impossibility
proved** for C2. -/

/-- The load-bearing structural collapse: at every stage there is a **unique** hereditarily
nonempty approximation, namely Ω's. -/
theorem allNonempty_unique (hinf : ℵ₀ ≤ κ) :
    ∀ (n) (s : Approx κ n), allNonempty κ n s → s = omegaApprox hinf n := by
  intro n
  induction n with
  | zero => intro s _; exact Subsingleton.elim (α := Approx κ 0) s (omegaApprox hinf 0)
  | succ n ih =>
      rintro s ⟨hne, hall⟩
      apply Subtype.ext
      rw [omegaApprox_succ]
      apply Set.Subset.antisymm
      · intro t ht; rw [Set.mem_singleton_iff]; exact ih t (hall t ht)
      · intro t ht
        rw [Set.mem_singleton_iff] at ht; subst ht
        obtain ⟨t₀, ht₀⟩ := hne
        rw [← ih t₀ (hall t₀ ht₀)]; exact ht₀

/-- **The gate returns Impossibility.** Ω is the *unique* productive thread on `Proc`. -/
theorem ws1_productive_unique (hinf : ℵ₀ ≤ κ) (x : Proc κ) (hx : Productive x) :
    x = omegaProc hinf := by
  rw [proc_ext]; intro n
  exact allNonempty_unique hinf n (x.1 n) (hx n)

/-- **Productive plurality is impossible on C2** — the pre-registered gate failure. The
honestly atom-free stagewise process collapses to the single point Ω, exactly as the
finished object does (WS2). The escape must relocate to a richer carrier home (metric C4 /
guarded), which this session does not build. -/
theorem ws1_no_productive_plurality (hinf : ℵ₀ ≤ κ) :
    ¬ ∃ x y : Proc κ, x ≠ y ∧ Productive x ∧ Productive y := by
  rintro ⟨x, y, hne, hx, hy⟩
  exact hne (by rw [ws1_productive_unique hinf x hx, ws1_productive_unique hinf y hy])

end Series06.WS1
