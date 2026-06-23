# `agda/` — the coinductive ν-layer

Layer 5 of [the formalization plan](../docs/formalization-plan.md#5-the-proof-assistants):
a **second proof assistant**. The [`formal/`](../formal/) Lean development mechanizes the
doctrine's greatest-fixed-point modality `ν` through `OrderHom.gfp` (Knaster–Tarski on a
complete lattice). Agda hosts the *same* content with **native coinduction** — coinductive
records and copatterns — which is the idiom the plan flags Agda as "cleanest" for, and the
one axioms [A5](../docs/spec/02-axioms.md) (the "we") and [A2](../docs/spec/02-axioms.md)
(the looped self) were reaching for all along. Here `≈` is not the greatest *post*-fixed
point of a lattice operator but the **final coalgebra** itself: a proof of `x ≈ y` is an
infinite, productive agreement, and the coinduction principle is one guarded definition
rather than a call to `le_gfp`.

Everything is built from scratch over only the standard library, in one module:
[`RelExist/Coinductive.agda`](RelExist/Coinductive.agda).

## Status

| Result | Agda name (`RelExist.Coinductive`) | Spec | State |
| --- | --- | --- | --- |
| a system as a behaviour (final coalgebra of the observation functor) | `Behaviour` | [00](../docs/spec/00-doctrine.md) | ✅ defined (coinductive record) |
| **A5** — `≈` as the greatest bisimulation | `_≈_` | [A5](../docs/spec/02-axioms.md) | ✅ defined (coinductive record) |
| `≈` is an equivalence | `≈-refl` / `≈-sym` / `≈-trans` / `≈-isEquivalence` | [A5](../docs/spec/02-axioms.md) | ✅ proved (copattern corecursion) |
| **shared world** `𝔼 := D/≈` | `SharedWorld` | [A5](../docs/spec/02-axioms.md) | ✅ defined (`Setoid`) |
| **coinduction** — every bisimulation `⊆ ≈` | `coinduction` (from `Bisimulation`) | [A5](../docs/spec/02-axioms.md) | ✅ proved (one guarded definition) |
| **A2** — a fixed point of the dynamics is a stationary self (the eigenform `νΦ`) | `fixpoint-isStationary` / `fixpoint-isSelf` | [A2](../docs/spec/02-axioms.md) | ✅ proved (via `coinduction`) |

The module is checked with `--safe --guardedness`: no postulates, no escape hatches —
every coinductive proof is machine-verified productive. It is the constructive,
final-coalgebra counterpart of `formal/`'s lattice-theoretic `RelExist.We` (`νΘ`), so the
doctrine's `≈` now has **two independent mechanizations** that agree.

## Build / check

```sh
cd agda
agda RelExist/Coinductive.agda   # type-checks the whole module (exit 0 = verified)
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
