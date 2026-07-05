/-
Spec 2.4e — the Lambek-free infinitude of Ω_R, and T16 at the ω-tier (2-4-mechanization-c).

Normative source: `series-2/2-4.md` and the work order `2-4-mechanization-c.md`. Continues
`Spec24d.lean` (Ω_C carved; `EqDepthR`; `hostedC`). Specs win. No declaration consults §8.

Route C (the primary, Lambek-free path to `Infinite Ω_R`): a `tower : ℕ → Ω_R` whose `n`-th
element reaches an object-sorted endpoint at exactly depth `n`, so distinct indices are separated
by the same `HasObjEndpointΩ` observation that proved `elt2 ≠ elt3`. No `mk` needed — only
`Cofix.corec`, `Cofix.dest`, `dest_corec`.

File is `Spec24e.lean` (new root) per the order's primary target.
-/
import Spec24d

open RelEx.Trials (RawC PfNe)

namespace RelEx.Corrected

/-! ## Stage 0, Route C — `Infinite Ω_R`, Lambek-free (2-4-mechanization-c §0; FP-C1) -/

/-- The tower coalgebra on `ℕ`: index 0 unfolds to an object-sorted self-pair (profile (O,O));
index `n+1` to a pure R–R self-pair on its predecessor `n`. A spine reaching the object profile at
exactly depth `n`. -/
def towerCoalg : ℕ → HC ℕ
  | 0 => s(Sum.inl (⟨{0}, Set.finite_singleton 0, Set.singleton_nonempty 0⟩ : PfNe ℕ),
           Sum.inl (⟨{0}, Set.finite_singleton 0, Set.singleton_nonempty 0⟩ : PfNe ℕ))
  | n + 1 => s(Sum.inr n, Sum.inr n)

/-- The tower: `tower n := νHC`-corecursion of `towerCoalg` at `n`. -/
noncomputable def tower (n : ℕ) : ΩR := QPF.Cofix.corec towerCoalg n

/-- The object endpoint of `tower 0`'s unfolding: the `corec`-image of the base pattern `{0}`. -/
noncomputable def towerObj0 : ΩO :=
  ⟨QPF.Cofix.corec towerCoalg '' {0}, (Set.finite_singleton 0).image _,
    (Set.singleton_nonempty 0).image _⟩

/-- `tower 0`'s unfolding is the object-sorted self-pair `s(inl towerObj0, inl towerObj0)`. -/
theorem dest_tower_zero :
    ZΩC.endpoints (tower 0) = s(Sum.inl towerObj0, Sum.inl towerObj0) := by
  show QPF.Cofix.dest (tower 0) = _
  rw [tower, QPF.Cofix.dest_corec]
  show HC.map (QPF.Cofix.corec towerCoalg) (towerCoalg 0) = _
  rw [show towerCoalg 0 =
        s(Sum.inl (⟨{0}, Set.finite_singleton 0, Set.singleton_nonempty 0⟩ : PfNe ℕ),
          Sum.inl (⟨{0}, Set.finite_singleton 0, Set.singleton_nonempty 0⟩ : PfNe ℕ)) from rfl,
      HC.map, Sym2.map_pair_eq]
  rfl

/-- `tower 0`'s unfolding carries an object endpoint (profile (O,O) at depth 0). -/
theorem hasObj_tower_zero : HasObjEndpointΩ (tower 0) :=
  ⟨towerObj0, by rw [dest_tower_zero]; exact Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- `tower (n+1)`'s unfolding is pure R–R on its predecessor: `s(inr (tower n), inr (tower n))`. -/
theorem dest_tower_succ (n : ℕ) :
    ZΩC.endpoints (tower (n + 1)) = s(Sum.inr (tower n), Sum.inr (tower n)) := by
  show QPF.Cofix.dest (tower (n + 1)) = _
  rw [tower, QPF.Cofix.dest_corec]
  show HC.map (QPF.Cofix.corec towerCoalg) (towerCoalg (n + 1)) = _
  rw [show towerCoalg (n + 1) = s(Sum.inr n, Sum.inr n) from rfl, HC.map, Sym2.map_pair_eq]
  rfl

/-- `tower (n+1)` has NO object endpoint (pure R–R). -/
theorem not_hasObj_tower_succ (n : ℕ) : ¬ HasObjEndpointΩ (tower (n + 1)) := by
  rintro ⟨o, ho⟩
  rw [dest_tower_succ, Sym2.mem_iff] at ho
  rcases ho with h | h <;> exact absurd h (by simp)

/-- Successor step: equal successors have equal predecessors (the spine descends injectively). -/
theorem tower_succ_inj (j k : ℕ) (h : tower (j + 1) = tower (k + 1)) : tower j = tower k := by
  have hd : ZΩC.endpoints (tower (j + 1)) = ZΩC.endpoints (tower (k + 1)) := by rw [h]
  rw [dest_tower_succ, dest_tower_succ, Sym2.eq_iff] at hd
  rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact Sum.inr.inj h1

/-- The tower is injective: distinct indices give distinct elements (separated at the depth where
the object profile appears — the `HasObjEndpointΩ` technique that proved `elt2 ≠ elt3`). -/
theorem tower_eq_imp : ∀ m n, tower m = tower n → m = n
  | 0, 0, _ => rfl
  | 0, k + 1, h => absurd (h ▸ hasObj_tower_zero) (not_hasObj_tower_succ k)
  | j + 1, 0, h => absurd (h.symm ▸ hasObj_tower_zero) (not_hasObj_tower_succ j)
  | j + 1, k + 1, h => congrArg (· + 1) (tower_eq_imp j k (tower_succ_inj j k h))

/-- FP-C1 — CONFIRMED: **Ω_R is infinite**, Lambek-free. The tower injects `ℕ` into `Ω_R`, so the
corrected relation carrier has no finite bound — the depth-observation separator (`HasObjEndpointΩ`
along the spine) does the whole job, needing no `mk`/Lambek. -/
theorem omegaR_infinite : Infinite ΩR :=
  Infinite.of_injective tower (fun m n => tower_eq_imp m n)

/-! ## Stage 1 — T16_ω (2-4-mechanization-c §1 = order b Stage 2; FP-B3) -/

/-- FP-B3 — CONFIRMED: **T16 at the ω-tier.** No object of the corrected universe has a total
pattern: `pat x` is finite (ω-tier boundedness, `bounded_ZΩC`) while `Ω_R` is infinite
(`omegaR_infinite`), so `pat x` cannot be all of `Ω_R`.

HONESTY CAVEAT (mandatory, 2-4-mechanization-c §1): this is **scaffold-assisted** T16 — the
finiteness that proves it is the D4 κ-loan's ω-instance, *not* an intrinsic bound. The intrinsic
T16 still owes T11 (or the Adámek–Trnková fallback). `T16_ω` is real and usable at this tier; it is
not the loan's discharge, and any downstream theorem consuming it inherits this caveat by
citation. -/
theorem T16_ω (x : ΩO) : ZΩC.pat x ≠ (Set.univ : Set ΩR) := by
  intro h
  have hfin : (ZΩC.pat x).Finite := bounded_ZΩC x
  rw [h] at hfin
  haveI : Infinite ZΩC.R := omegaR_infinite
  exact Set.infinite_univ hfin

end RelEx.Corrected

/-! ## Axiom audit -/
section AxiomAudit
open RelEx.Corrected
#print axioms omegaR_infinite
#print axioms T16_ω
end AxiomAudit
