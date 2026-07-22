/-
`program-3/series-2/formal/P3S2/ws2.lean`

WS2 - The region laws: the exact flux law and its three faces. Program 3 Series 2 (3.2), the ledger.

The heart of the series. Under any transport, a region's ledger changes by precisely the flux terms of the
exchange partners it contains, and by nothing else:

- `ws2_region_flux`: the exact accounting, for every region and every non-degenerate move;
- `ws2_region_interior`: both partners inside, the ledger conserved;
- `ws2_region_exterior`: both partners outside, conserved;
- `ws2_boundary_flux`: one partner inside, the change is that partner's charge change exactly.

Conservation is local and relative to the region; it fails only at the boundary, and there by an exact
accounting. The `y ≠ z` hypothesis excludes only the identity move (`transport_self`).

Sorry-free; axiom-clean beyond Mathlib's standard `propext` / `Classical.choice` / `Quot.sound`.
-/
import P3S2.ws1

namespace P3S2

open P3S0 P3S1

set_option linter.unusedVariables false

/-- The exact flux law: under any transport, a region's ledger changes by precisely the flux terms of the
exchange partners it contains. Everyone else is a bystander and contributes nothing. -/
theorem ws2_region_flux (x y z : Fin 3) (g : G) (r : Finset (Fin 3)) (hyz : y ≠ z) :
    regionCharge (transport x y z g) r - regionCharge g r
      = (if y ∈ r then charge (transport x y z g) y - charge g y else 0)
      + (if z ∈ r then charge (transport x y z g) z - charge g z else 0) := by
  by_cases hy : y ∈ r <;> by_cases hz : z ∈ r
  · rw [if_pos hy, if_pos hz]
    have hz' : z ∈ r.erase y := Finset.mem_erase.mpr ⟨hyz.symm, hz⟩
    unfold regionCharge
    rw [← Finset.add_sum_erase r (charge (transport x y z g)) hy,
        ← Finset.add_sum_erase r (charge g) hy,
        ← Finset.add_sum_erase _ (charge (transport x y z g)) hz',
        ← Finset.add_sum_erase _ (charge g) hz']
    have hs : ∑ w ∈ (r.erase y).erase z, charge (transport x y z g) w
        = ∑ w ∈ (r.erase y).erase z, charge g w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (ws2_exchange_zero_sum x y z g).1 w
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw)
    rw [hs]; ring
  · rw [if_pos hy, if_neg hz]
    unfold regionCharge
    rw [← Finset.add_sum_erase r (charge (transport x y z g)) hy,
        ← Finset.add_sum_erase r (charge g) hy]
    have hs : ∑ w ∈ r.erase y, charge (transport x y z g) w = ∑ w ∈ r.erase y, charge g w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (ws2_exchange_zero_sum x y z g).1 w (Finset.ne_of_mem_erase hw)
        (fun h => hz (h ▸ Finset.mem_of_mem_erase hw))
    rw [hs]; ring
  · rw [if_neg hy, if_pos hz]
    unfold regionCharge
    rw [← Finset.add_sum_erase r (charge (transport x y z g)) hz,
        ← Finset.add_sum_erase r (charge g) hz]
    have hs : ∑ w ∈ r.erase z, charge (transport x y z g) w = ∑ w ∈ r.erase z, charge g w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (ws2_exchange_zero_sum x y z g).1 w
        (fun h => hy (h ▸ Finset.mem_of_mem_erase hw)) (Finset.ne_of_mem_erase hw)
    rw [hs]; ring
  · rw [if_neg hy, if_neg hz]
    unfold regionCharge
    have hs : ∑ w ∈ r, charge (transport x y z g) w = ∑ w ∈ r, charge g w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (ws2_exchange_zero_sum x y z g).1 w (fun h => hy (h ▸ hw)) (fun h => hz (h ▸ hw))
    rw [hs]; ring

/-- Both exchange partners inside the region: its ledger is conserved. -/
theorem ws2_region_interior (x y z : Fin 3) (g : G) (r : Finset (Fin 3)) (hyz : y ≠ z)
    (hy : y ∈ r) (hz : z ∈ r) :
    regionCharge (transport x y z g) r = regionCharge g r := by
  have hflux := ws2_region_flux x y z g r hyz
  rw [if_pos hy, if_pos hz] at hflux
  have hpair := (ws2_exchange_zero_sum x y z g).2
  omega

/-- Both exchange partners outside the region: its ledger is conserved. -/
theorem ws2_region_exterior (x y z : Fin 3) (g : G) (r : Finset (Fin 3)) (hyz : y ≠ z)
    (hy : y ∉ r) (hz : z ∉ r) :
    regionCharge (transport x y z g) r = regionCharge g r := by
  have hflux := ws2_region_flux x y z g r hyz
  rw [if_neg hy, if_neg hz] at hflux
  omega

/-- One exchange partner inside: the region's ledger changes by exactly that partner's charge change. The
boundary is where conservation gives way, and there the accounting is exact. -/
theorem ws2_boundary_flux (x y z : Fin 3) (g : G) (r : Finset (Fin 3)) (hyz : y ≠ z)
    (hy : y ∈ r) (hz : z ∉ r) :
    regionCharge (transport x y z g) r - regionCharge g r
      = charge (transport x y z g) y - charge g y := by
  have hflux := ws2_region_flux x y z g r hyz
  rw [if_pos hy, if_neg hz] at hflux
  omega

end P3S2
