/-
# Scratch — mathlib-dependent work area

Mathlib-backed formalization, kept out of the default build so the dependency-free
core (`RelExist`) stays fast. Compiling this is what triggers the mathlib build.

* `Scratch.We`          — `≈ := νΘ` and the shared world `𝔼 := D/≈` (theorem T2),
                          via `OrderHom.gfp` (Knaster–Tarski). ✅ verified.
* `Scratch.Identity`    — A2 restated: identity is the lived `≈`; observation `≅` is a
                          **strictly lossy** projection. Proves soundness `≈ ⊆ ≅`, strictness
                          `≈ ⊊ ≅` (witness), and the non-injective forgetting `D/≈ ↠ D/≅` (the
                          first-person surplus). ✅ verified.
* `Scratch.Forgetting`  — the unification: identity-collapse, dephasing, and the partial trace are
                          one construction (`Coarsening`), each non-injective for the same reason —
                          a nonempty residue (surplus / copy-defect / entanglement). ✅ verified.
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
                          to drop monotonically — and a witnessed collapse; plus the irreducible
                          floor (the shared block attention cannot reach). ✅ verified.
* `Scratch.Conservation` — **decoherence *is* the partial trace**: entangle a system with an
                          environment (`entangle`); the global state stays coherent while its
                          partial trace (the relationship forgotten) is classical — coherence
                          conserved, only relocated. ✅ verified.
* `Scratch.Forgetting`   — identity-collapse, dephasing, and the partial trace as one `Coarsening`,
                          each non-injective for the same reason (a residue). ✅ verified.
* `Scratch.Knowing`      — the bridge: the gap is governed by relation; `≅` is the *disjoint*
                          (view-from-nowhere) observer; completeness ⟺ disjointness. ✅ verified.
* `Scratch.Registration` — `reg` derived from the `Φ_c` dynamics: registration *is* absorption. ✅ verified.
* `Scratch.Marginal`     — nondeterminism is a consequence of relation: a related whole's marginal
                          branches; local determinism ⟺ no relation. ✅ verified.
* `Scratch.RelationalMarginal` — …robustly, for any global law; deterministic conservation is the
                          priced corollary. ✅ verified.
* `Scratch.Convergence`  — the depth/threshold read off `Φ_c`'s orbit directly (not an abstract `σ`).
                          ✅ verified.
* `Scratch.Stabilization` — does the orbit converge? ω-convergence always (continuity), finite-depth
                          iff ACC. ✅ verified.
* `Scratch.Feeling`      — **feeling as a relational decoherence differential** (`≅ₒ`, not the
                          view-from-nowhere `≅`): conserved coherence carried across a relation. ✅ verified.
* `Scratch.RelationalAppearance` — relativizing the outside: soundness/surplus *survive and strengthen*
                          against `≅ₒ`, but "the surplus is exactly nondeterminism" does **not** — a
                          deterministic system has a relational surplus (feeling from the seam, not
                          choice). ✅ verified.
* `Scratch.QuantumSeam`  — bridge B route 2: the seam on the **actual** `dephase` (lossy, irreversible)
                          via **no-broadcasting** — the compact face of the firewall whose cartesian
                          face is Lawvere. (B-as-Lawvere/route 1 remains open.) ✅ verified.
* `Scratch.GraphModel`   — **Pω**, the Plotkin–Scott graph model: a concrete non-trivial reflexive
                          object — continuous self-maps are a retract of `Set ℕ` (`app (Graph f) = f`),
                          with the fixpoint (GoI's `Y`) and the `K` combinator. ✅ verified.
* `Scratch.DomainTraced` — the **simplest domains (complete lattices) as a `TracedSMC`** via the
                          join-monoid (the scalar/identity trace; *not* the Hasegawa fixpoint trace,
                          which stays open). ✅ verified.
* `Scratch.Causation`    — a causality `[reading]` made a theorem: **the missing cause is the other** —
                          conditioning on the other's hidden state restores determinism; local
                          indeterminism *is* the un-viewed relational cause. ✅ verified.
* `Scratch.SparsityPosits` — discharging the two sparsity posits: `d ≥ 2` given structural meaning
                          (**genuine return** = not-given ∧ not-one-shot, `genuine_return_iff`) and shown
                          load-bearing (positive floor ⟺ sparse vs dense); and the valuation `μ`
                          **constructed** as the orbit's return index (the genuine returns are strict
                          standing increases), discharging it for unit cost. ✅ verified.
-/
import Scratch.We
import Scratch.Identity
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
import Scratch.Conservation
import Scratch.Forgetting
import Scratch.Knowing
import Scratch.Registration
import Scratch.Marginal
import Scratch.RelationalMarginal
import Scratch.Convergence
import Scratch.Stabilization
import Scratch.Feeling
import Scratch.RelationalAppearance
import Scratch.QuantumSeam
import Scratch.GraphModel
import Scratch.DomainTraced
import Scratch.Causation
import Scratch.SparsityPosits
