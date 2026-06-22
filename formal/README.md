# `formal/` — mechanized development

Lean 4 formalization of Relational Existentialism, tracking [`docs/spec/`](../docs/spec/).

## Status

| Result | Lean name (`RelExist.*`) | Spec source | State |
| --- | --- | --- | --- |
| Core counting bound | `min_mul_length_le_totalSpend` | [03 §3.2](../docs/spec/03-sparsity-conjecture.md) | ✅ proved |
| **Lemma 3.1** (sparsity from a budget), division-free | `stab_card_bound` | [03 Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ✅ proved |
| Lemma 3.1, divided form `≤ β/m` | `stab_card_le_div` | [03 Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ✅ proved |
| Sparsity at depth `d ≥ 2` (`≤ β/2`) | `stab_card_le_half` | [03 §3.2](../docs/spec/03-sparsity-conjecture.md) + [A4](../docs/spec/02-axioms.md) | ✅ proved |
| **Lemma 3.2** (collapse without a bound) | `unbounded_without_budget` | [03 Lemma 3.2](../docs/spec/03-sparsity-conjecture.md) | ✅ proved |

All five are `sorry`-free; their only axiom dependency is `propext` (verified via
`#print axioms`). This is the **discrete (ℕ-valued) core** of the sparsity
dichotomy: a finite attention budget, divided among selves each costing at least a
positive floor, bounds the number of selves independently of how many couplings
exist — and remove the budget and that bound collapses.

The core (`RelExist`) is deliberately **dependency-free (no mathlib)** so it builds
in seconds even where mathlib's cache is unreachable.

### The loop bridge — step 3 (core, no mathlib)

This closes the gap the spec flagged ([03 §3.3](../docs/spec/03-sparsity-conjecture.md)):
the sparsity lemmas count with a *threshold*, but [A4](../docs/spec/02-axioms.md)
defines a self as a **fixed point** of budgeted iterated self-relation. The bridge
([`RelExist/Loop.lean`](RelExist/Loop.lean)) connects them.

| Result | Lean name (`RelExist.*`) | Meaning | State |
| --- | --- | --- | --- |
| `loop_R(e) = e ⟺ N(e) ≥ d(e)` | `loopR_isEigen_iff_le_fundedReturns` | budgeted loop is an eigenform iff budget funds depth-many returns | ✅ proved |
| `loop_R(e) = e ⟺ d·λ ≤ β` | `loopR_isEigen_iff` / `loopR_isEigen_iff_selfCost` | …iff the budget covers the self's cost (the resource threshold) | ✅ proved |
| derived cost floor `2 ≤ d·λ` | `two_le_selfCost` | depth `≥ 2` (A4) ⇒ cost `≥ 2`: the sparsity floor is *derived*, not posited | ✅ proved |
| witness model is non-vacuous | `matarN_stabilizesAt` | a concrete maturation dynamics actually `StabilizesAt` depth `d` | ✅ proved |
| capstone | `stab_card_le_half_of_depths` | selves with depths `≥ 2` and total cost `≤ β` number `≤ β/2`, floor **discharged** | ✅ proved |

So A4's fixed-point self and the counted threshold are now provably the same
condition, and the sparsity bound's cost-floor hypothesis is a theorem.

### Doctrine axioms — A2, A3, A6

The three previously prose-only axioms, mechanized via their essential mathematical
content. (The abstract *traced symmetric monoidal category* typeclass is deliberately
not reproduced — large categorical infrastructure; what the axioms invoke is here.)

| Result | Lean name | Spec | Target | State |
| --- | --- | --- | --- | --- |
| **A6 σ-side** — Lawvere; the mirror can't close | `RelExist.Mirror.{lawvere, no_complete_selfModel, selfModel_remainder}` | [A6](../docs/spec/02-axioms.md), [00 §0.4.2](../docs/spec/00-doctrine.md) | core (no mathlib) | ✅ **0 axioms** |
| **A2** — self-relation is feedback (`νP`) | `RelExist.Trace.{selfTrace, selfTrace_fixed}` | [A2](../docs/spec/02-axioms.md) | Scratch | ✅ proved |
| **A3** — to relate is to create (Conway `Tr`) | `RelExist.Trace.{Tr, Tr_fixed, le_Tr, Tr_mono}` | [A3](../docs/spec/02-axioms.md) | Scratch | ✅ proved |
| **A6 contrast** — knowing obstructed vs feeling whole | `RelExist.KnowingFeeling.{knowing_can_fail_to_close, no_complete_boolModel, feeling_is_whole}` | [A6](../docs/spec/02-axioms.md) | Scratch | ✅ proved |

Lawvere's theorem (`RelExist.Mirror.lawvere`) and its consequences are **fully
constructive** — they depend on *no axioms whatsoever*, which is fitting: the mirror's
incompleteness is not an assumption but the contrapositive of a one-line diagonal.

### mathlib-backed results (target `Scratch`)

| Result | Lean name | Spec source | State |
| --- | --- | --- | --- |
| `≈ := νΘ` as the greatest bisimulation | `RelExist.We.bisim` | [A5](../docs/spec/02-axioms.md) | ✅ defined (`OrderHom.gfp`) |
| `Θ ≈ = ≈` (fixed point) | `RelExist.We.bisim_unfold` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| **coinduction** — every bisimulation `≤ ≈` | `RelExist.We.bisim_coind` / `bisim_of_bisimulation` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| `≈` is an equivalence (refl/symm/trans) | `RelExist.We.bisim_{refl,symm,trans}` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| **shared world** `𝔼 := D/≈` | `RelExist.We.World` | [A5](../docs/spec/02-axioms.md) | ✅ defined (quotient) |
| co-directed attention operator (induced by coupling) | `RelExist.Attention.couplingOp` | [§1.3](../docs/spec/01-signature.md) | ✅ defined |
| "receiving raises giving" (monotone) | `RelExist.Attention.couplingOp_mono` | [§1.3.2](../docs/spec/01-signature.md) | ✅ proved |
| **self = eigenform** `νΦ` (fixed point, maximal) | `RelExist.Attention.sustainedField{,_fixed,_greatest}` | [§1.3.3](../docs/spec/01-signature.md), [A4](../docs/spec/02-axioms.md) | ✅ proved |
| generativity — relating **accumulates** attention | `RelExist.Attention.orbit_{ascending,le_gfp}` | [§1.3.3](../docs/spec/01-signature.md) | ✅ proved |
| Lemma 3.1 over `ℝ` (`\|Stab\| ≤ β/m`) | `RelExist.Real.stab_card_le_div` | [03 Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ✅ proved |
| **density → 0** (`\|Stab N\|/N → 0`) | `RelExist.Real.stab_density_tendsto_zero` | [03 §3.1, Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ✅ proved (`Filter.Tendsto`) |

`Scratch.We` formalizes **axiom A5**: observational identity as `νΘ = OrderHom.gfp Θ`,
with coinduction, the proof that `≈` is an equivalence, and the shared world `𝔼 := D/≈`.
`Scratch.Attention` recasts **attention as a consequence of structure** (§1.3): a
co-directed, asymmetric operator `Φ_c` induced by the coupling, with the self an
*eigenform* `νΦ_c`, finiteness *constitutive* (the bounded capacity `α`, no budget), and
"receiving raises giving" as monotone accumulation — the budget model of
`RelExist/Loop.lean` becomes its uniform-depleting special case. `Scratch.SparsityReal`
lifts the sparsity dichotomy to `ℝ` with the genuine **density-→-0** limit. See
*One-command setup* below.

## Build

```sh
cd formal
lake build            # the dependency-free core (RelExist) — fast, no mathlib
lake build Scratch    # the mathlib-backed target — compiles mathlib on first run
```

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.15.0`). Audit the proofs' axiom footprint with:

```sh
lake env lean -e '#print axioms RelExist.stab_card_bound'
```

### One-command setup — `scripts/bootstrap.sh`

[`scripts/bootstrap.sh`](scripts/bootstrap.sh) installs everything idempotently:
`elan`, the Lean toolchain, the core build, and (unless `SKIP_MATHLIB=1`) the
mathlib-backed target.

```sh
formal/scripts/bootstrap.sh                  # toolchain + core + mathlib
SKIP_MATHLIB=1 formal/scripts/bootstrap.sh   # toolchain + core only (seconds)
```

It is written for the network policy in our remote sessions — `github.com` +
`pypi.org` allowed, but `release.lean-lang.org` / `api.github.com` and the mathlib
cache blob blocked. So it installs the toolchain by **direct GitHub download**
(decompressing the `.tar.zst` via the `zstandard` PyPI module, since there is no
`zstd` binary) and **compiles mathlib from source** (no cache). With a permissive
policy none of these workarounds are needed — `elan` and `lake exe cache get` do it
automatically.

### Reusable container (Claude Code on the web)

A `SessionStart` hook ([`.claude/hooks/session-start.sh`](../.claude/hooks/session-start.sh),
registered in [`.claude/settings.json`](../.claude/settings.json)) runs
`bootstrap.sh` at the start of every **remote** session and persists the toolchain
on `PATH`. The first remote session compiles the mathlib slice once (≈4 min for the
current imports); the platform then caches the container state, so later sessions
start with Lean + mathlib already built. The hook no-ops in local (non-remote)
sessions. Once merged to the default branch, all future sessions pick it up.

## Roadmap

The discrete core is step 1 of [the spec's proof strategy](../docs/spec/03-sparsity-conjecture.md#35-proof-strategy-for-mechanization).
Next, in rough order:

1. **mathlib upgrade.** Re-cast costs in `ℝ_{≥0}`, prove the density-→-0 statement
   (`Filter.Tendsto`) and the "nowhere dense" form (topology). mathlib is now
   installed (target `Scratch`), so this proceeds there — no cache required, just the
   one-time source compile the bootstrap already does.
2. **Sharing.** Replace the `List` of costs by a graded poset with sub-additive cost
   (lax `c`), re-deriving the bound up to the sharing defect ([03 §3.3](../docs/spec/03-sparsity-conjecture.md)).
3. **Threshold ⇔ fixed point.** The categorical crux: in the traced fragment,
   `loop_R(e) = e ⟺ N(e) ≥ d(e)` ([01 §1.3.3](../docs/spec/01-signature.md)).
4. **Doctrine + Layer 4.** Symmetric monoidal / cartesian fragment structures and
   the functorial-semantics firewall.
