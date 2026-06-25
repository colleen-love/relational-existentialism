/-
# Scratch — mathlib-dependent work area

Mathlib-backed formalization, kept out of the default build so the dependency-free
core (`RelExist`) stays fast. Compiling this is what triggers the mathlib build.

* `Scratch.We`          — `≈ := νΘ` and the shared world `𝔼 := D/≈` (theorem T2),
                          via `OrderHom.gfp` (Knaster–Tarski). ✅ verified.
* `Scratch.Attention`   — attention as the co-directed eigenstructure of the relational
                          coupling (a consequence of structure, not a bolted-on budget);
                          the self as an eigenform `νΦ`. ✅ verified.
* `Scratch.Trace`       — D1/T1: trace as feedback (`selfTrace`) and the Conway
                          parameterized fixed-point operator (`Tr`). ✅ verified.
* `Scratch.KnowingFeeling` — the T3 contrast: knowing (Lawvere-obstructed) vs feeling
                          (`≈`, whole). ✅ verified.
* `Scratch.Chemistry`   — Layer 4, first domain functor: autocatalytic sets as
                          eigenforms (`νΦ`); the functor is definitional. ✅ verified.
* `Scratch.Biology`     — Layer 4, biology: Rosen's (M,R)-systems; closure to efficient
                          causation = the organism `ν(repair ∘ metabolize)`; the functor
                          is definitional. ✅ verified.
* `Scratch.Rel`         — `Rel` (sets & relations) as a genuine multi-object `TracedSMC`
                          instance: the full JSV axiom set, validated non-trivially.
                          ✅ verified.
* `Scratch.RelCoherence` — `Rel` promoted to a `CoherentTracedSMC`: the eight monoidal
                          coherence laws (pentagon, triangle, hexagon, naturalities,
                          symmetry), validated in a genuine multi-object model. ✅ verified.
* `Scratch.Recurrence`  — Layer 4, AI: recurrence/Geometry-of-Interaction. Feedback **is**
                          the trace (in `Rel`); sustained recurrence is the eigenform `νΦ`;
                          a self-consistent hidden state is sustained. ✅ verified.
* `Scratch.PartialTrace` — Layer 4, physics: the quantum **partial trace** on matrices and
                          its defining properties (linearity, vanishing-II, yanking,
                          full-trace compatibility). ✅ verified.
* `Scratch.MatrixModel` — Layer 4, physics: **the literal traced SMC** — finite types &
                          matrices, `⊗` = Kronecker, trace = partial trace, associators as
                          permutation matrices; the full JSV axiom set. `matTracedSMC`.
                          The named frontier, closed. ✅ verified.
* `Scratch.MatrixCoherence` — the matrix model promoted to a `CoherentTracedSMC`: all eight
                          coherence laws, via functoriality of permutation matrices. ✅ verified.
* `Scratch.Compact`     — Layer 4, categorical: compact closure, the firewall collapse
                          theorem, and categorical no-cloning (physics). ✅ verified.
* `Scratch.NoCloning`   — Layer 4, physics: the concrete (linear-algebra) no-cloning
                          theorem — cloning is nonlinear. ✅ verified.
* `Scratch.SparsityReal` — the ℝ-valued sparsity bound and density-→-0 statement
                          (the analytic upgrade of Lemmas 3.1/3.2). ✅ verified.
* `Scratch.Decoherence`  — Layer 4, physics: the quantum→classical passage in the matrix model
                          — `dephase`, the classical fragment, copyability ⟺ commutativity, and
                          the continuous `copyDefect`/`defectSq`. ✅ verified.
* `Scratch.Classical`    — the abstract (typeclass) companion: `DaggerCategory` and a
                          `Decoherence` structure, validated by the matrix instance. ✅ verified.
* `Scratch.Distribution` — self-in-other quantified in a Banach algebra: `distributed`/`total`,
                          the living regime `0<‖x‖<1`, the bound, and the quantitative
                          eigenform `sustained` (unique by contraction). ✅ verified.
* `Scratch.Feedback`     — the two sustained selves unified at the ν-modality
                          (`CoDirectedSelf`): lattice `νΦ` and Banach `sustained` as instances.
                          ✅ verified.
* `Scratch.Attending`    — directed attention as **selective decoherence**: `attend S` (partial
                          dephase), interpolating `id`⟶`dephase`, with the copy-defect proved
                          to drop monotonically — and a witnessed collapse. ✅ verified.
-/
import Scratch.We
import Scratch.Attention
import Scratch.Trace
import Scratch.KnowingFeeling
import Scratch.Chemistry
import Scratch.Biology
import Scratch.Rel
import Scratch.RelCoherence
import Scratch.Recurrence
import Scratch.PartialTrace
import Scratch.MatrixModel
import Scratch.MatrixCoherence
import Scratch.Compact
import Scratch.NoCloning
import Scratch.SparsityReal
import Scratch.Decoherence
import Scratch.Classical
import Scratch.Distribution
import Scratch.Feedback
import Scratch.Attending
