/-
# Scratch — mathlib-dependent work area

This module (and the `Scratch` lib target) is where mathlib-backed formalization
lands, kept out of the default build so the dependency-free core (`RelExist`) stays
fast. Compiling this is what triggers the one-time mathlib build.

First target: the greatest-fixed-point machinery for `≈ := νΘ` (axiom A5). In
mathlib, the `ν`-modality we actually need is Knaster–Tarski — the greatest fixed
point of a monotone operator on a complete lattice — i.e. `OrderHom.gfp`. The import
below is the smoke test that mathlib is installed and that API is reachable.
-/
import Mathlib.Order.FixedPoints

open OrderHom

-- Smoke test: the greatest-fixed-point operator on a complete lattice exists and
-- has its defining post-fixed-point property. This is the categorical `ν` we use
-- to define observational identity `≈` (spec A5) as a bisimilarity.
example {α : Type} [CompleteLattice α] (f : α →o α) : f (gfp f) = gfp f :=
  (map_gfp f)
