# The canonical axioms — `{A1, A2, A3, D1}`

> *One axiomatization, shared by all three papers.* This file states the four canonical commitments of the
> theory plainly, for a reader who has never seen the repository, and lists for each the per-paper
> *consequences* that were once separate "readings" and are now **derived theorems**. The mechanization is
> [`theory/Theory/Axioms.lean`](../formal/Theory/Axioms.lean) (Lean 4, `sorry`-free; every theorem named
> below carries only the corpus-norm footprint `[propext, Classical.choice, Quot.sound]`).

The theory has one philosophical wager: **relation comes first, and the self is what relation produces.** Four
commitments make that precise. Three are structural scaffolding (`A1`, `A2`, `D1`); one — **A3** — is the
load-bearing bet. The move is to state A3 as a **process** and show the rest of the theory's
pictures of the self *fall out of it*. What was three papers' worth of separately-posited "readings" of the
self is now one process with three consequences.

---

## A3 — the self is the fixed point of a process `[the wager; derived consequences]`

**Statement (the process).** *Relations co-direct attention asymmetrically in the relata.* A relation is a
loop of attention between two relata `i` and `j`; each end raises the attention it gives toward what it can
sustain, at a rate **limited by its own finite capacity** `α` (its standing in all its *other* relations).
The loop is **mutual** (neither end closes it alone) but **not symmetric** (each raises at its own rate). This
is a *process*, **diachronic** — it runs in time, the same tense as A1's flow and A2's coinduction.

**The self is derived, not posited.** A **self** is a **fixed point** of this process: a configuration the
loop returns unchanged — the state sustained under the attention channel `Φ_c`, the coupling settled on the
conserved band. The self is no longer *asserted* to be an eigenform; it is *defined* as the fixed point and
its structure is *proved*.

**Mechanization.** The process is `MutualCoupling.jointStep α` (the canonical name `Theory.Axioms.A3process`);
a self is `MutualCoupling.JointFixed` (`Theory.Axioms.IsSelf`).

**First, existence (the first risk).** If the process had no fixed points, no self would ever form. It does:

- `self_exists` — the fully-conserved coupling (`μ ≡ 1`, the maximal band) is a fixed point for *every* state
  and *every* capacity. A self *can* form.
- `self_exists_stable` — more strongly, a *stable* self is **reached generatively**: from the strong-attention
  basin the coupling climbs to the conserved band while the coherence is **not** spent (`x ≥ x₀/2 > 0`
  forever). The self is a stable, bounded achievement, not a fragile coincidence.

**The three readings, now derived as theorems of the one process:**

| Reading (paper) | What it says | Derived as |
|---|---|---|
| **Eigenform `νΦ_c` / `Peri`** (paper one) | the self is the sustainable field the loop returns unchanged | `eigenform_of_fixed`, `self_is_periBand`, `energy_in_self` |
| **Generative engine** (paper three) | mutually-attended self-relating *makes more self*, finitely (capacity `α` is the brake) | `generative_law` (`orbit_engine2`), `generative_bounded` |
| **Phase-bearing / modular self** (paper two) | the self rotates at the modular (energy) frequencies, sustained, the modular flow a symmetry | `modular_preserves_self`, `modular_sustains_self`, `modular_is_symmetry` |

- **Eigenform (paper one).** A self's state is returned unchanged by the channel, so it lies in A3's
  *sustainable field* `Peri(Φ_c)` = the conserved (modulus-one) band — which carries the rotating **energy**
  band beside the fixed **knowing** band `νΦ_c`. Paper one's "self `:= Peri`" was once *A3 read at the
  strength of its text*; it is now a theorem (`eigenform_of_fixed`).
- **Generative engine (paper three).** The per-edge moduli of a genuine process orbit obey the two-sided
  capacity-bearing engine `Engine2 (α i) (α j)` (`generative_law`); with admissible capacities the orbit stays
  bounded forever (`generative_bounded`) — growth is a *finite achievement*, `α` the regulator, divergence
  structurally excluded.
- **Modular self (paper two).** For a state diagonal in the preferred basis, the modular flow is a
  **modulus-one Schur multiplier**: it **maps the self into itself** (`modular_preserves_self`), **sustains**
  every coherence edge-for-edge — the rotating sub-band cycling at the modular energies forever
  (`modular_sustains_self`) — and **commutes** with the co-direction channel (`modular_is_symmetry`). The
  modular self is the *same* fixed point, read under the modular flow rather than the dissipative one (the
  "two faces of one generator" of `OneGenerator`).

**Why it matters.** A3 is the one wager that stops the theory being a universal solvent — drop it and nearly
everything trivially "is a self." Stating it as a process, with the finite capacity `α` built in, is what makes
selfhood *selective* and *achievable*. **The collapse is total**: every reading
derives; none stays forked.

**Gloss.** A relation builds a persisting self only when it loops — returned to, re-entered, lived again until
it holds; and being attended-to *raises* the attention one can give, so the self is sustained generatively,
not spent down — but finitely, because each relatum's capacity is bounded by all its other relations.

---

## A1 — the arena, dimension-generic `[structural]`

**Statement.** The theory works in a **traced symmetric monoidal category** (the language in which "a
relating" is a composable, tensorable, traceable thing). The mechanized core is the traced-SMC typeclass
`Foundation.Traced`.

**Dimension is an instantiation parameter, not an axiom.** Every result of A3 above is stated over an
*arbitrary* index type — the process, the eigenform, the conserved band are all polymorphic. Paper one
instantiates the **finite** case; papers two/three the **infinite** general case. *Finite vs infinite is not
an axiom difference — it is the same A1 instantiated.* Witnessed by `A1_dimension_generic`: the eigenform
derivation carries no finiteness hypothesis.

**Gloss.** Before any claim about selves, fix *what kind of thing a relating is*. A1 is that choice of arena —
one arena, read at whatever dimension a given paper needs.

---

## A2 — relation primacy (priority) `[structural; derived-canonical]`

**Statement.** A state's identity **is** its first-person relational unfolding — there is **no bare carrier**
beneath it. Canonically, this is the **strong extensionality** of the world of selves `𝔼 = D/≈`
(bisimilarity *is* equality on `𝔼`): no individuation finer than the lived relating `≈`.

**One A2, already proved.** This is `Priority.priority_universal` (re-exported as `Theory.Axioms.A2_priority`),
holding for **every** system. The old `≈ ⊊ ≅` "surplus" is its downstream *signature*, sourced from the seam —
not the priority claim itself, and kept separate.

**Gloss.** Take away every relation and no bare self remains underneath. You *are* your relating, with no
residue.

---

## D1 — self-relation = the trace, generalized to the modular flow `[definitional; generalized]`

**Statement.** The self-relating of a system *is* the **trace** of a relating on it — output returned to
input (`σ = Tr`). The canonical, **generalized** form is the **modular flow**: `σ = modularFlow ρ`, the
intrinsic dynamics the state `ρ` induces, of which the trace is the **infinite-temperature limit**.

**Same definition, generalized.** At the maximally-mixed state the modular flow is the identity — internal
time is *off* and `σ = Tr` is recovered (`D1_trace_is_modular_limit`,
`ModularFlow.modularFlow_maximally_mixed`). Paper one instantiates the trace (time off); papers two/three the
modular flow (time on). `σ = Tr ⇝ σ = modularFlow ρ`.

**Co-directed form.** Self-relation is the unary case (a private feedback wire). When the looped wire is
*shared* between two relata, the same feedback is **co-directed** — and that is exactly the A3 process. So A3's
co-direction is a *consequence* of D1's feedback, not an extra ingredient.

**Gloss.** The simplest relation is the self relating to itself: attention turned inward, modeled as feedback.
At the deep end, that feedback *is* the flow of internal (thermal) time.

---

## How the four fit together

```
         A1  — the arena (one arena; finite or infinite by instantiation)
          │
   D1  — self-relation = feedback (trace ⇝ modular flow)
          │   shared wire ⇒ co-direction
          ▼
   A3  — the co-direction PROCESS, capacity-bounded     A2 — no bare carrier
          │   the self = its fixed point (derived)           (priority, universal)
          ├──────────────┬───────────────────────┐
          ▼              ▼                        ▼
   eigenform/Peri   generative engine      phase-bearing / modular self
     (paper one)      (paper three)              (paper two)
```

Three papers, one axiomatization. The differences between the papers are **instantiations** (A1's dimension,
D1's trace-vs-modular) and **derived consequences** (A3's three readings), not different axioms.

---

## Where this lives — the legible canonical home (directory convention)

`theory/` is the **canonical home of the theory** — the living frontier already beyond paper one, and now the
home of the one shared axiom layer.

- **A root** is exactly a top-level directory with `formal/` (Lean) + `spec/` (prose) + `README.md`, governed
  by the import gates ([`scripts/gate.sh`](../../scripts/gate.sh)). The six roots: `foundation/`, `theory/`,
  `paper-1/`, `paper-2/`, `scratch/`, `archive/`. See [`STRUCTURE.md`](../../STRUCTURE.md) for the full
  discipline and the roots-vs-infrastructure split.
- **Infrastructure** (not roots): [`lake/`](../../lake) — the Lean package home + mathlib cache, renamed out
  of the old `formal/` collision so `formal/` only ever names a root's Lean sources; [`agda/`](../../agda) —
  the parallel coinductive ν-layer; [`papers/`](../../papers) — the final manuscripts; `scripts/` and the
  top-level docs.
- **The canonical axiom layer is stable and version-pinned.** `Theory.Axioms` changes **only
  backward-compatibly** (generalization, never redefinition), exactly like `foundation/`. Papers **import (or
  cite) and pin** it — they do not fork it. Each paper records its pin in `spec/04-provenance.md`; the gate
  enforces both the import allowance and the pin. The axioms are **one shared layer**, not per-paper forks —
  there is no divergence to protect, because the readings are consequences of the one process.

**Build.** `cd lake && lake build Foundation Paper1 Theory Paper2` (green). The canonical layer is
`Theory.Axioms`; its prose is this file.
