/-
# Space — the coupling-graph pre-geometry (Part 1 of the space/energy spec)

The spec's **Part 1**: space is not a background the relations sit inside, it is the *geometry
of the coupling*. From the coupling graph implicit in `Φ_c` / `copyDefect` (sites `A`, directed
edge weights `w_{ij}` = coupling strength) we read off a **distance**: `d(i,j)` is the length of
the strongest multiplicative coupling path, `d(i,j) = min_paths Σ −log w`. We mechanize this
**additively** — taking edge *lengths* `len i j = −log w_{ij} ∈ [0,∞]` as primitive (`∞` = zero
coupling) — so that `d` is a genuine shortest-path distance and the `−log` is absorbed into the
edge length. The construction is **relation-primary**: the only data is the coupling `len`; the
distance, the separations, and the propagation bound are all consequences of it.

This file is independent of the complex/CPTP model extension that Parts 2–3 require: it lives
entirely in the present real model, and every target below is mechanized sorry-free.

## What is proved

* **§1 The path metric.** `Coupling A` = edge lengths `len : A → A → ℝ≥0∞` with `len i i = 0`.
  A **walk** `i → mids → j` has length `walkLen` (the chain sum of edge lengths); the **distance**
  `dist i j = ⨅ walks` is the infimum over all walks. Then `[proved]`:
    - `dist_self` : `d(i,i) = 0`;
    - `dist_le_len` : `d(i,j) ≤ len i j` — *a direct morphism bounds the distance by its weight*;
    - `dist_triangle` : `d(i,k) ≤ d(i,j) + d(j,k)` — from path concatenation.
  Distance is **not** symmetric in general (the coupling `c` is asymmetric): `dist_asymmetric`
  exhibits a two-site coupling with `d(a,b) ≠ d(b,a)`. So `dist` is a genuine **quasi-pseudometric**;
  the asymmetry is a feature of relational space, stated, not smoothed away.

* **§2 Separability ⟺ infinite distance.** `dist_eq_top_iff` : `d(i,j) = ∞` iff *every* connecting
  walk passes through a zero-coupling (`∞`-length) edge. The witness `dist_sep` : two ⊗-coexisting
  relata with no coupling are at `d = ∞`; together with `dist_le_len` (a single finite edge bounds
  the distance) this makes **"space = coexistence minus connection"** a theorem.

* **§3 The influence bound (the payoff — reuses the `TimeFlow` engine).** A *weighted* dephasing
  flow `wDephase w` shrinks each coherence `M i j` by its edge retention `w i j` per step
  (`copyDefect_wDephase_iterate` : the `(i,j)` coherence after `n` steps is `(w i j)^n · M i j` —
  the same geometric decay `TimeFlow` proved, now edge-resolved). Taking the retention to be
  `w i j = exp(−len i j)`, `influence_bound` shows the coherence between `i,j` after `n` closures is
  bounded by `exp(−n · d(i,j)) · |M i j|`: **influence propagates no faster than coupling distance
  permits.** Strongly-coupled (small `d`) sites retain influence; weakly-coupled (large `d`) sites
  lose it fast. A finite-propagation bound, governed by the path metric of §1.

## Honest scope (`[reading]` vs `[proved]`)

What is **proved** is a weighted **quasi-pseudometric pre-geometry** with a distance-controlled
propagation bound. What stays a `[reading]` is that this quasi-metric *is* space. This is **not**
dimension, smoothness, a manifold, or a signature; the "lightcone" is a propagation *bound* only,
not a Lorentzian structure. The effective-resistance / graph-Laplacian distance (the richer
refinement, whose Laplacian is the same generator Parts 2–3 use) is left as the named open frontier.
-/
import Scratch.Decoherence
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RelExist.Space

open scoped ENNReal
open RelExist.Decoherence Matrix

/-! ## §1 The coupling graph and its path metric -/

variable {A : Type*}

/-- The length of a **walk** `i → mids → j`: the chain sum of edge lengths along the walk, where
`mids` is the (possibly empty) list of intermediate sites visited. The empty walk `i → [] → j` is
the direct edge, of length `len i j`. -/
noncomputable def walkLen (len : A → A → ℝ≥0∞) : A → List A → A → ℝ≥0∞
  | i, [], j => len i j
  | i, x :: xs, j => len i x + walkLen len x xs j

@[simp] lemma walkLen_nil (len : A → A → ℝ≥0∞) (i j : A) : walkLen len i [] j = len i j := rfl

@[simp] lemma walkLen_cons (len : A → A → ℝ≥0∞) (i x : A) (xs : List A) (j : A) :
    walkLen len i (x :: xs) j = len i x + walkLen len x xs j := rfl

/-- **Walk lengths concatenate.** Splicing a walk `i → m1 → j` with a walk `j → m2 → k` (through the
shared waypoint `j`) gives a walk `i → (m1 ++ j :: m2) → k` whose length is the sum. This is the
engine of the triangle inequality. -/
lemma walkLen_concat (len : A → A → ℝ≥0∞) (i : A) (m1 : List A) (j : A) (m2 : List A) (k : A) :
    walkLen len i (m1 ++ j :: m2) k = walkLen len i m1 j + walkLen len j m2 k := by
  induction m1 generalizing i with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, walkLen_cons]
      rw [ih x, ← add_assoc]

/-- **A coupling.** The only datum of relational space: a directed edge length `len i j ∈ [0,∞]`
(the `−log` of the coupling strength `w_{ij}`; `∞` = no coupling), with `len i i = 0` (a site is at
no distance from itself). Everything else — distance, separation, propagation — is read off this. -/
structure Coupling (A : Type*) where
  /-- edge length `= −log(coupling strength)`; `∞` means the two sites are uncoupled -/
  len : A → A → ℝ≥0∞
  /-- a site couples to itself at zero length -/
  len_self : ∀ i, len i i = 0

/-- **The coupling distance.** `d(i,j)` is the length of the strongest coupling path: the infimum,
over all walks `i → mids → j`, of the walk length. (Relation-primary: `d` is *defined from* the
coupling, not a background metric the coupling lives in.) -/
noncomputable def Coupling.dist (C : Coupling A) (i j : A) : ℝ≥0∞ :=
  ⨅ mids : List A, walkLen C.len i mids j

lemma Coupling.dist_def (C : Coupling A) (i j : A) :
    C.dist i j = ⨅ mids : List A, walkLen C.len i mids j := rfl

/-- **`d(i,i) = 0`** — the first quasi-pseudometric law: the empty walk witnesses zero self-distance. -/
theorem Coupling.dist_self (C : Coupling A) (i : A) : C.dist i i = 0 := by
  refine le_antisymm ?_ (zero_le _)
  calc C.dist i i ≤ walkLen C.len i [] i := iInf_le (fun mids => walkLen C.len i mids i) []
    _ = C.len i i := rfl
    _ = 0 := C.len_self i

/-- **A direct morphism bounds the distance by its weight**: `d(i,j) ≤ len i j` — the single-edge
walk is one of the walks competed over. This is the "connection shortens space" half of §2. -/
theorem Coupling.dist_le_len (C : Coupling A) (i j : A) : C.dist i j ≤ C.len i j :=
  iInf_le (fun mids => walkLen C.len i mids j) []

/-- **The triangle inequality** `d(i,k) ≤ d(i,j) + d(j,k)` — the second quasi-pseudometric law,
straight from `walkLen_concat`: any pair of walks `i → j` and `j → k` splices to a walk `i → k`,
and the infimum distributes over the sum in `ℝ≥0∞`. -/
theorem Coupling.dist_triangle (C : Coupling A) (i j k : A) :
    C.dist i k ≤ C.dist i j + C.dist j k := by
  have key : C.dist i j + C.dist j k
      = ⨅ m1 : List A, ⨅ m2 : List A, (walkLen C.len i m1 j + walkLen C.len j m2 k) := by
    rw [C.dist_def, C.dist_def, ENNReal.iInf_add]
    simp_rw [ENNReal.add_iInf]
  rw [key]
  refine le_iInf₂ (fun m1 m2 => ?_)
  calc C.dist i k ≤ walkLen C.len i (m1 ++ j :: m2) k :=
        iInf_le (fun mids => walkLen C.len i mids k) (m1 ++ j :: m2)
    _ = walkLen C.len i m1 j + walkLen C.len j m2 k := walkLen_concat C.len i m1 j m2 k

/-! ### Asymmetry — the coupling distance is a *quasi*-metric, not a metric

The coupling `c` is asymmetric (`copyDefect`/`Φ_c` need not be symmetric), so `d(i,j) ≠ d(j,i)` in
general. We exhibit it concretely: a two-site coupling where `a → b` costs `1` but `b → a` is
uncoupled (`∞`). This is a feature of relational space — direction matters — stated as a theorem. -/

/-- Two sites, for the concrete witnesses. -/
inductive Site | a | b

/-- An **asymmetric** coupling: `a → b` has length `1`, but `b → a` is uncoupled (`∞`). -/
noncomputable def lenAsym : Site → Site → ℝ≥0∞
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => 1
  | .b, .a => ⊤

noncomputable def couplingAsym : Coupling Site := ⟨lenAsym, fun s => by cases s <;> rfl⟩

/-- Every walk from `b` to `a` is infinite: to *leave* `b` you must pay the uncoupled edge `b → a = ∞`
(the only non-`b` step out of `b`), so no finite walk reaches `a`. -/
lemma walkLen_b_a (mids : List Site) : walkLen lenAsym Site.b mids Site.a = ⊤ := by
  induction mids with
  | nil => rfl
  | cons x xs ih =>
      rw [walkLen_cons]
      cases x with
      | a => rw [show lenAsym Site.b Site.a = (⊤ : ℝ≥0∞) from rfl, top_add]
      | b => rw [show lenAsym Site.b Site.b = (0 : ℝ≥0∞) from rfl, zero_add, ih]

theorem couplingAsym_dist_b_a : couplingAsym.dist Site.b Site.a = ⊤ := by
  rw [Coupling.dist_def]; exact iInf_eq_top.2 walkLen_b_a

theorem couplingAsym_dist_a_b_le_one : couplingAsym.dist Site.a Site.b ≤ 1 :=
  couplingAsym.dist_le_len Site.a Site.b

/-- **The coupling distance is genuinely asymmetric**: `d(a,b) ≠ d(b,a)` (one is `≤ 1`, the other is
`∞`). So `Coupling.dist` is a quasi-pseudometric — `dist_self` + `dist_triangle` hold, but symmetry
provably fails. -/
theorem dist_asymmetric :
    couplingAsym.dist Site.a Site.b ≠ couplingAsym.dist Site.b Site.a := by
  rw [couplingAsym_dist_b_a]
  intro h
  have h1 : couplingAsym.dist Site.a Site.b ≤ 1 := couplingAsym_dist_a_b_le_one
  rw [h] at h1
  simp at h1

/-! ## §2 Separability ⟺ infinite distance

"Space = coexistence minus connection." Two relata can co-exist (live in the same `A`) yet be at
infinite distance — exactly when no walk of finite length connects them. The general criterion, then
the ⊗-coexistence witness. -/

/-- **Separability criterion.** `d(i,j) = ∞` iff *every* walk connecting `i` to `j` runs through a
zero-coupling (`∞`-length) edge. (Just `iInf_eq_top` on the path metric — but it is the precise
statement of separation: there is no finite channel of influence between `i` and `j`.) -/
theorem Coupling.dist_eq_top_iff (C : Coupling A) (i j : A) :
    C.dist i j = ⊤ ↔ ∀ mids : List A, walkLen C.len i mids j = ⊤ := by
  rw [C.dist_def]; exact iInf_eq_top

/-- A **fully separated** coupling: the two sites co-exist but have *zero* coupling in either
direction (`a ↔ b` both `∞`). -/
noncomputable def lenSep : Site → Site → ℝ≥0∞
  | .a, .a => 0
  | .b, .b => 0
  | _, _ => ⊤

noncomputable def couplingSep : Coupling Site := ⟨lenSep, fun s => by cases s <;> rfl⟩

/-- Every walk from `a` to `b` is infinite — there is no finite path through a zero-coupling cut. -/
lemma walkLen_sep_a_b (mids : List Site) : walkLen lenSep Site.a mids Site.b = ⊤ := by
  induction mids with
  | nil => rfl
  | cons x xs ih =>
      rw [walkLen_cons]
      cases x with
      | a => rw [show lenSep Site.a Site.a = (0 : ℝ≥0∞) from rfl, zero_add, ih]
      | b => rw [show lenSep Site.a Site.b = (⊤ : ℝ≥0∞) from rfl, top_add]

/-- **⊗-coexisting relata with zero coupling are at `d = ∞`.** With `dist_le_len` (a single finite
edge bounds the distance), this makes "space is coexistence minus connection" a theorem: distance is
finite exactly to the extent the coupling connects. -/
theorem couplingSep_dist : couplingSep.dist Site.a Site.b = ⊤ :=
  (couplingSep.dist_eq_top_iff Site.a Site.b).2 walkLen_sep_a_b

/-! ## §3 The influence bound — finite propagation, governed by the coupling distance

The payoff, reusing the `TimeFlow` engine. We refine the uniform partial-dephasing flow into a
**weighted** one, `wDephase w`, that shrinks each coherence `M i j` by its own edge retention
`w i j` per step. Then the `(i,j)` coherence after `n` steps is exactly `(w i j)^n · M i j` — the
same geometric decay `TimeFlow` proved, now resolved per edge. Taking `w i j = exp(−len i j)` ties
the decay rate to the coupling length, and the path-metric bound `d ≤ len` gives:

  coherence between `i,j` after `n` closures ≤ `exp(−n · d(i,j)) · |M i j|`

— influence cannot outrun the coupling distance. -/

section Influence
variable {A : Type} [Fintype A] [DecidableEq A]

/-- **The weighted dephasing flow** (the edge-resolved refinement of `TimeFlow.partialDephase`):
multiply each entry by its edge retention, `M i j ↦ w i j · M i j`. With `w i j = exp(−len i j)`,
strongly-coupled edges (small `len`, `w ≈ 1`) retain coherence; weakly-coupled edges (large `len`,
`w ≈ 0`) shed it. -/
def wDephase (w : A → A → ℝ) (M : Matrix A A ℝ) : Matrix A A ℝ := fun i j => w i j * M i j

/-- One step scales the `(i,j)` coherence by the edge retention `w i j`. -/
lemma copyDefect_wDephase (w : A → A → ℝ) (M : Matrix A A ℝ) (i j : A) :
    copyDefect (wDephase w M) i j = w i j * copyDefect M i j := by
  rcases eq_or_ne i j with e | e
  · subst e; simp [copyDefect_apply]
  · simp [copyDefect_apply, wDephase, e]

/-- **The edge-resolved geometric decay.** The `(i,j)` coherence after `n` closures of the loop is
`(w i j)^n · M i j` exactly — `TimeFlow`'s geometric monovariant, now per edge. (The uniform flow is
the case `w i j ≡ 1 − p`.) -/
lemma copyDefect_wDephase_iterate (w : A → A → ℝ) (M : Matrix A A ℝ) (n : ℕ) (i j : A) :
    copyDefect ((wDephase w)^[n] M) i j = (w i j) ^ n * copyDefect M i j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', copyDefect_wDephase, ih, pow_succ]; ring

/-- The edge retentions `w i j = exp(−len i j) ∈ (0,1]` derived from a coupling. -/
noncomputable def expWeight (C : Coupling A) : A → A → ℝ :=
  fun i j => Real.exp (-(C.len i j).toReal)

@[simp] lemma expWeight_apply (C : Coupling A) (i j : A) :
    expWeight C i j = Real.exp (-(C.len i j).toReal) := rfl

/-- **The influence bound — finite propagation governed by the coupling distance.** Under the
weighted dephasing flow with retentions `exp(−len)`, the coherence between coupled sites `i,j`
(`len i j < ∞`) after `n` closures of the feedback loop is bounded by

  `|coherence_n(i,j)| ≤ exp(−n · d(i,j)) · |coherence_0(i,j)|`.

The bound decays with the **coupling distance** `d(i,j)` of §1: strongly-coupled (small `d`) sites
retain influence, weakly-coupled (large `d`) sites lose it geometrically fast. Influence propagates
no faster than the coupling distance permits — a finite-propagation bound, the `[reading]` "lightcone"
of this pre-geometry, proved by reusing the `TimeFlow` decay engine (`copyDefect_wDephase_iterate`)
and the path-metric edge bound (`dist_le_len`). -/
theorem influence_bound (C : Coupling A) (M : Matrix A A ℝ) (n : ℕ) (i j : A)
    (hfin : C.len i j ≠ ⊤) :
    |copyDefect ((wDephase (expWeight C))^[n] M) i j|
      ≤ Real.exp (-(n : ℝ) * (C.dist i j).toReal) * |copyDefect M i j| := by
  have hpos : (0 : ℝ) < expWeight C i j := by rw [expWeight_apply]; exact Real.exp_pos _
  rw [copyDefect_wDephase_iterate, abs_mul, abs_pow, abs_of_pos hpos]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hdle : C.dist i j ≤ C.len i j := C.dist_le_len i j
  have hdfin : C.dist i j ≠ ⊤ := ne_top_of_le_ne_top hfin hdle
  have hle : (C.dist i j).toReal ≤ (C.len i j).toReal :=
    (ENNReal.toReal_le_toReal hdfin hfin).2 hdle
  calc expWeight C i j ^ n
      = Real.exp ((n : ℝ) * (-(C.len i j).toReal)) := by
        rw [expWeight_apply, ← Real.exp_nat_mul]
    _ ≤ Real.exp ((n : ℝ) * (-(C.dist i j).toReal)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hle]) (Nat.cast_nonneg n))
    _ = Real.exp (-(n : ℝ) * (C.dist i j).toReal) := by congr 1; ring

end Influence

end RelExist.Space
