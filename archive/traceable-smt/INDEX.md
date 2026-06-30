# Archive index — the prior edifice, as a mineable library

> **What this is.** Handoff I.II changed arenas: the theory moved from a **traced-SMC / operator-representation**
> setting to a **quantaloid / allegory** in which relations are the primitive arrow. The work below is **not
> wrong** — it is the same theory in a representation we outgrew — so it was **archived, not deleted**, and
> kept *navigable*. This index maps **what was proved and where**, so a future reader can find a result in one
> move and port its **shape** into the new arena.
>
> **Two layers, kept distinct.** This directory (`archive/traceable-smt/`) holds the edifice we *just* outgrew
> (the rotated papers, the theory/foundation layers, the scratch frontier, and the Agda layer). The work we
> outgrew *earlier* is nested under [`prior-archive/`](prior-archive) (the older deprecated development —
> functorial semantics, the `Int`/GoI scaffolding, the sparsity capstones, etc.). Nothing here is on the
> build path; archived code is **not** gated.
>
> **"Depended on" = what would have to be re-grounded relationally** to carry the result into the new arena.

## The seam — reflexive opacity (arena-independent: Lawvere is Lawvere)

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `lawvere` | `paper-2/formal/RelExist/Mirror.lean` | a point-surjective `A → (A→B)` forces every `f : B → B` to have a fixed point — the diagonal argument | **0 axioms**, pure function-level diagonal; arena-independent — re-states directly in any cartesian/allegorical setting with a diagonal |
| `self_cannot_trace_relation` | `paper-2/formal/RelExist/Seam.lean` | the one self-relation a self cannot completely take on itself (Lawvere at `Env = Self`) — **the seam** | Lawvere specialized; arena-independent |
| `self_cannot_fully_decohere` | `paper-2/formal/Scratch/SeamForcing.lean` | a self-inclusive block cannot be fully decohered — the un-decohereable floor that *orders* the arrow | the matrix decoherence model (`Scratch.Decoherence`); the **forcing** is structural, the *matrix* witness is what re-grounds |

## The engine / asymmetry — the codirection dynamics

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `asymmetry_emerges` | `scratch/formal/GenerativeEngine.lean` | asymmetry between the two ends is *produced* by the dynamics, not imposed | the two-sided modulus engine `Engine2 (α i)(α j)`; real-analysis (mathlib) |
| `capacity_orders_couplings` | `scratch/formal/GenerativeEngine.lean` | the richer-capacity end leads on both coupling and coherence at every step | same engine; ordering on `ℝ` |
| `growth_requires_both` | `scratch/formal/GenerativeEngine.lean` | growth of either coupling requires **both** coherences live (non-extraction) | mutual (non-freezable) attention term |
| `engine_bounded` / `engine2_bounded` | `scratch/formal/GenerativeEngine.lean` | the per-end capacity `α ≤ 1` caps the orbit in `[0,1]` forever — no blowup | convex `raise` cap; mathlib |

## Emergence — the self exists

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `self_exists` | `theory/formal/Theory/Axioms.lean` | the A3 codirection process has a fixed point (a self) | the `JointFixed` construction (`Theory.MutualCoupling`); gfp / Knaster–Tarski |
| `self_exists_stable` | `scratch/formal/GenerativeEngine.lean` | a *stable* self is reached generatively (ignition basin) | `engine_ignition`; mathlib analysis |
| gfp / stabilization machinery | `theory/formal/Theory/MutualCoupling.lean` | `jointStep`, `JointFixed` (`= Axioms.IsSelf`) — the co-direction step and its fixed point | `OrderHom.gfp`; the matrix arena |

## Eigenform / band — the self's shape

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `eigenform_of_fixed` | `theory/formal/Theory/Axioms.lean` | a fixed state lies in the sustainable field `Peri` (the eigenform reading, derived) | band layer; `modPow_diagonal` |
| `self_is_periBand` | `theory/formal/Theory/Axioms.lean` | the self is exactly the conserved (modulus-one) band | band coincidence |
| `band_coincidence_from_axioms` | `theory/formal/Theory/BandFromAxioms.lean` | the seam band coincides with the rotating energy band — derived from A1–A3, no fourth posit | `RotatingSpectrum`, `BandCoincidence`; contractivity + nondegeneracy |
| `energy_arrow_spectrum`, `rotating_sustained` | `theory/formal/Theory/RotatingSpectrum.lean` | energy = the rotating band; `genReal = Re log μ ≤ 0` is the arrow | spectral decomposition; mathlib `Complex` |

## Modular / thermal (papers two/three)

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `modularFlow`, `modularFlow_maximally_mixed` | `theory/formal/Theory/ModularFlow.lean` | the intrinsic dynamics a state induces; the trace is its infinite-temperature limit (D1's modular form) | `modPow` spectral exponential; mathlib `Matrix`/`Hermitian` |
| `combinedFlow_add` | `paper-3/formal/Paper3/OneGenerator.lean` | the modular clock and dissipative arrow are two faces of **one** generator at equilibrium | KMS bridge + Schur commutation in the preferred basis |
| `presence_conserved`, `pythagorean` | `paper-3/formal/Paper3/Einselection.lean` | the conserved band's HS weight (**presence**) is conserved and splits into knowing ⊕ energy | einselection (`stationary_eq_diagonal_real`); band layer |
| `arrow_is_loss_not_relocation` | `paper-3/formal/Paper3/Einselection.lean` | within the self's ledger the arrow is **loss**, not relocation — the negative handed to conservation | dephasing dissipator; HS norm |

## Conservation (paper-four frontier)

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `decoherence_is_partial_trace` | `scratch/formal/Conservation.lean` | decoherence conserves coherence — it relocates it into the system/environment cross-term | the matrix model + partial trace (`Foundation`); `Scratch.Decoherence` |

## Sparsity — selves are rare (note: **old budget framing**)

> These predate the capacity-`α` reframing and use the *external attention budget* model; their counting is
> sound but the framing is the one the signature later disowned. Re-grounding relationally means redoing the
> count over codirected capacity, not a spent scalar.

| Result | File | What it shows | Depended on |
|---|---|---|---|
| `selves` nowhere-dense; `conjecture_3_7` | `prior-archive/formal/Archive/Scratch/SparsityCapstone.lean` | density of selves `→ 0` under a finite budget + exclusive per-self cost | budget model; order density |
| `Sparsity`, `SparsityReal`, `SparsityPosits`, `SparsitySharing` | `prior-archive/formal/Archive/RelExist/Sparsity.lean`, `prior-archive/formal/Archive/Scratch/Sparsity*.lean` | counting / density / the discharged posits (`d ≥ 2`, constructed `μ`); cost-sharing correction | pigeonhole; cylinder topology; **budget framing** |
| `selves-nowhereDense` (Agda) | `prior-archive/agda/RelExist/Sparsity.agda` | the topological sparsity statement, independently in Agda | `--safe` Agda; final coalgebra |

---

**How to use this.** When a new-arena (relational) theorem needs an old proof's structure, find it here, open
the file, and port the **shape** — re-grounding whatever the "depended on" column flags (the matrix model, the
operator representation, the budget framing) onto relations-as-primitive. The seam and the conservation facts
are the most directly portable (arena-independent or near it); the modular/spectral and sparsity material
needs the most re-grounding.
