/-
# Scratch — mathlib-dependent work area

Mathlib-backed formalization, kept out of the default build so the dependency-free
core (`RelExist`) stays fast. Compiling this is what triggers the mathlib build.

* `Scratch.We`          — `≈ := νΘ` and the shared world `𝔼 := D/≈` (axiom A5),
                          via `OrderHom.gfp` (Knaster–Tarski). ✅ verified.
* `Scratch.Attention`   — attention as the co-directed eigenstructure of the relational
                          coupling (a consequence of structure, not a bolted-on budget);
                          the self as an eigenform `νΦ`. ✅ verified.
* `Scratch.Trace`       — A2/A3: trace as feedback (`selfTrace`) and the Conway
                          parameterized fixed-point operator (`Tr`). ✅ verified.
* `Scratch.KnowingFeeling` — the A6 contrast: knowing (Lawvere-obstructed) vs feeling
                          (`≈`, whole). ✅ verified.
* `Scratch.SparsityReal` — the ℝ-valued sparsity bound and density-→-0 statement
                          (the analytic upgrade of Lemmas 3.1/3.2). ✅ verified.
-/
import Scratch.We
import Scratch.Attention
import Scratch.Trace
import Scratch.KnowingFeeling
import Scratch.SparsityReal
