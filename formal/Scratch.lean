/-
# Scratch — mathlib-dependent work area

Mathlib-backed formalization, kept out of the default build so the dependency-free
core (`RelExist`) stays fast. Compiling this is what triggers the mathlib build.

* `Scratch.We`          — `≈ := νΘ` and the shared world `𝔼 := D/≈` (axiom A5),
                          via `OrderHom.gfp` (Knaster–Tarski). ✅ verified.
* `Scratch.SparsityReal` — the ℝ-valued sparsity bound and density-→-0 statement
                          (the analytic upgrade of Lemmas 3.1/3.2). Imported once its
                          analysis-slice build is verified on this branch.
-/
import Scratch.We
-- import Scratch.SparsityReal  -- re-enabled after its (heavier) analysis build verifies
