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

### mathlib-backed results (target `Scratch`)

| Result | Lean name | Spec source | State |
| --- | --- | --- | --- |
| `≈ := νΘ` as the greatest bisimulation | `RelExist.We.bisim` | [A5](../docs/spec/02-axioms.md) | ✅ defined (`OrderHom.gfp`) |
| `Θ ≈ = ≈` (fixed point) | `RelExist.We.bisim_unfold` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| **coinduction** — every bisimulation `≤ ≈` | `RelExist.We.bisim_coind` / `bisim_of_bisimulation` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| `≈` is an equivalence (refl/symm/trans) | `RelExist.We.bisim_{refl,symm,trans}` | [A5](../docs/spec/02-axioms.md) | ✅ proved |
| **shared world** `𝔼 := D/≈` | `RelExist.We.World` | [A5](../docs/spec/02-axioms.md) | ✅ defined (quotient) |
| Lemma 3.1 over `ℝ` (`\|Stab\| ≤ β/m`) | `RelExist.Real.stab_card_le_div` | [03 Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ⏳ written; analysis-slice build verifying |
| **density → 0** (`\|Stab N\|/N → 0`) | `RelExist.Real.stab_density_tendsto_zero` | [03 §3.1, Lemma 3.1](../docs/spec/03-sparsity-conjecture.md) | ⏳ written; analysis-slice build verifying |

`Scratch.We` formalizes **axiom A5** (`docs/spec`): observational identity as
`νΘ = OrderHom.gfp Θ` (Knaster–Tarski *is* the `ν`-modality the spec needs), with the
coinduction principle, the proof that `≈` is an equivalence, and the shared world as
the quotient `𝔼 := D/≈`. `Scratch.SparsityReal` lifts the sparsity dichotomy to `ℝ`
and proves the genuine **density-→-0** limit. See *One-command setup* below.

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
