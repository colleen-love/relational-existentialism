# `agda/` — the coinductive ν-layer

Layer 5 of [the formalization plan](../docs/formalization-plan.md#5-the-proof-assistants):
a **second proof assistant**. The [`formal/`](../formal/) Lean development mechanizes the
doctrine's greatest-fixed-point modality `ν` through `OrderHom.gfp` (Knaster–Tarski on a
complete lattice). Agda hosts the *same* content with **native coinduction** — coinductive
records and copatterns — which is the idiom the plan flags Agda as "cleanest" for, and the
one axioms [T2](../docs/spec/02-axioms.md) (the "we") and [D1](../docs/spec/02-axioms.md)
(the looped self) were reaching for all along. Here `≈` is not the greatest *post*-fixed
point of a lattice operator but the **final coalgebra** itself: a proof of `x ≈ y` is an
infinite, productive agreement, and the coinduction principle is one guarded definition
rather than a call to `le_gfp`.

Two modules, both from scratch over only the standard library:
[`RelExist/Coinductive.agda`](RelExist/Coinductive.agda) — the ν-layer proper — and
[`RelExist/Sparsity.agda`](RelExist/Sparsity.agda) — the **topological** form of the
sparsity dichotomy ([spec 03 §3.5](../docs/spec/03-sparsity-conjecture.md), step 4).

## Status — `RelExist.Coinductive` (the ν-layer)

| Result | Agda name | Spec | State |
| --- | --- | --- | --- |
| a system as a behaviour (final coalgebra of the observation functor) | `Behaviour` | [00](../docs/spec/00-doctrine.md) | ✅ defined (coinductive record) |
| **T2** — `≈` as the greatest bisimulation | `_≈_` | [T2](../docs/spec/02-axioms.md) | ✅ defined (coinductive record) |
| `≈` is an equivalence | `≈-refl` / `≈-sym` / `≈-trans` / `≈-isEquivalence` | [T2](../docs/spec/02-axioms.md) | ✅ proved (copattern corecursion) |
| **shared world** `𝔼 := D/≈` | `SharedWorld` | [T2](../docs/spec/02-axioms.md) | ✅ defined (`Setoid`) |
| **coinduction** — every bisimulation `⊆ ≈` | `coinduction` (from `Bisimulation`) | [T2](../docs/spec/02-axioms.md) | ✅ proved (one guarded definition) |
| **D1** — a fixed point of the dynamics is a stationary self (the eigenform `νΦ`) | `fixpoint-isStationary` / `fixpoint-isSelf` | [D1](../docs/spec/02-axioms.md) | ✅ proved (via `coinduction`) |

## Status — `RelExist.Sparsity` (topological sparsity, step 4)

The spec's [Conjecture 3.3](../docs/spec/03-sparsity-conjecture.md#34-the-conjecture) asks
for the *infinite-state* form of "selves are rare": that the carrier of selves `Stab` is
**nowhere dense** in the space of states under "the natural topology on states `I → D`."
[§3.5 step 4](../docs/spec/03-sparsity-conjecture.md#35-proof-strategy-for-mechanization)
names Agda's ν-layer as the host. States are **behaviours in the final coalgebra**; the
natural topology is the **cylinder topology** (basic opens are finite-prefix determined);
the looped selves (D1) are exactly the *constant* behaviours `repeat a`.

| Result | Agda name | Meaning | State |
| --- | --- | --- | --- |
| topological "Stab" *is* the doctrine's self | `Const→isSelf` / `isSelf→Const` | the constant behaviours are exactly the D1 selves | ✅ proved |
| **closed** — the non-selves are open | `nonConst-open` | one moment of difference is finite-prefix witnessed ⇒ `Stab` is closed | ✅ proved |
| **empty interior** — every cylinder meets the non-selves | `selves-emptyInterior` | no observation prefix forces selfhood | ✅ proved |
| **nowhere dense** — sparsity, topological form | `selves-nowhereDense` | given two distinct observations, `Stab` is closed with empty interior | ✅ proved |
| **sharp dichotomy** — trivial alphabet ⇒ all selves | `trivial→allSelf` | one observation ⇒ every state is a self (`Stab` dense), mirroring Lemma 3.2 (`β = ⊤`) | ✅ proved |

This is the lift the spec flagged once `Cl(𝕋)` existed: the Lean side *counts* (`Stab`
finite, density `→ 0` — `Scratch.SparsityReal.stab_density_tendsto_zero`); the Agda side
gives the topological statement Conjecture 3.3 actually asks for, with the same sharp
dichotomy — "two distinct observations" is the expressivity hypothesis (the avatar of
`ε > 1`), and dropping it collapses the theory to the universal solvent.

Both modules are checked with `--safe --guardedness`: no postulates, no escape hatches —
every coinductive proof is machine-verified productive. `RelExist.Coinductive` is the
constructive, final-coalgebra counterpart of `formal/`'s lattice-theoretic `RelExist.We`
(`νΘ`), so the doctrine's `≈` now has **two independent mechanizations** that agree;
`RelExist.Sparsity` discharges the topological clause of the sparsity conjecture that the
Lean counting bound cannot reach.

## Build / check

```sh
cd agda
agda RelExist/Coinductive.agda   # the ν-layer
agda RelExist/Sparsity.agda      # topological sparsity (imports Coinductive)
```

Requires Agda (2.6.x) and the standard library, registered as a default library. A
UTF-8 locale is needed for Agda to read the unicode source (`export LC_ALL=C.UTF-8`).

### One-command setup — `scripts/bootstrap.sh`

[`scripts/bootstrap.sh`](scripts/bootstrap.sh) installs Agda + the standard library
idempotently from the Ubuntu archive and registers the library so `agda` finds it by
default. It is invoked **non-fatally** by the repo's `SessionStart` hook
([`.claude/hooks/session-start.sh`](../.claude/hooks/session-start.sh)): a remote session
that fails to install Agda still has the full Lean development, so a transient apt hiccup
never blocks the session from starting.
