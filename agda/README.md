# `agda/` — the coinductive ν-layer (infrastructure, not a root)

A **parallel proof assistant** — a *second* mechanization, infrastructure like [`lake/`](../lake), not a
root. Its live modules are dual witnesses for [paper one](../paper-1/spec/paper-one.md). The
[`lake/`](../lake/) Lean development mechanizes the
doctrine's greatest-fixed-point modality `ν` through `OrderHom.gfp` (Knaster–Tarski on a
complete lattice). Agda hosts the *same* content with **native coinduction** — coinductive
records and copatterns — which is the idiom Agda is cleanest for, and the
one that theorem [3.2](../paper-1/spec/03.2-lived-identity.md) (the "we") and definition [D1](../paper-1/spec/02-axioms.md)
(the looped self) were reaching for all along. Here `≈` is not the greatest *post*-fixed
point of a lattice operator but the **final coalgebra** itself: a proof of `x ≈ y` is an
infinite, productive agreement, and the coinduction principle is one guarded definition
rather than a call to `le_gfp`.

Two **live** modules, both from scratch over only the standard library, witnessing **paper one**:
[`RelExist/Coinductive.agda`](RelExist/Coinductive.agda) — the ν-layer proper (theorem
[3.2](../paper-1/spec/03.2-lived-identity.md), the lived identity `≈`) — and
[`RelExist/Inversion.agda`](RelExist/Inversion.agda) — the first-person surplus `≈ ⊊ ≅` (the
[3.5](../paper-1/spec/03.5-decoherence.md) inversion), proved in *both* assistants (cf. Lean
`bisim_ne_obsEq`). The third witness — **topological sparsity** — is paper-**three** material and lives in the
archive: [`archive/agda/RelExist/Sparsity.agda`](../archive/agda/RelExist/Sparsity.agda) (it imports the live
`RelExist.Coinductive`).

## Status — `RelExist.Coinductive` (the ν-layer)

| Result | Agda name | Spec | State |
| --- | --- | --- | --- |
| a system as a behaviour (final coalgebra of the observation functor) | `Behaviour` | [00](../theory/spec/00-doctrine.md) | ✅ defined (coinductive record) |
| **3.2** — `≈` (the **lived identity**) as the greatest bisimulation | `_≈_` | [3.2](../paper-1/spec/03.2-lived-identity.md) | ✅ defined (coinductive record) |
| `≈` is an equivalence | `≈-refl` / `≈-sym` / `≈-trans` / `≈-isEquivalence` | [3.2](../paper-1/spec/03.2-lived-identity.md) | ✅ proved (copattern corecursion) |
| **shared world** `𝔼 := D/≈` | `SharedWorld` | [3.2](../paper-1/spec/03.2-lived-identity.md) | ✅ defined (`Setoid`) |
| **coinduction** — every bisimulation `⊆ ≈` | `coinduction` (from `Bisimulation`) | [3.2](../paper-1/spec/03.2-lived-identity.md) | ✅ proved (one guarded definition) |
| **observational equality** `≅` (the outside view) | `_≅_` | [02 A2](../paper-1/spec/02-axioms.md), [03.5](../paper-1/spec/03.5-decoherence.md) | ✅ defined (same observation stream) |
| **deterministic collapse** `≈ ⟺ ≅` (the *boundary* case) | `≈⇒≅` / `≅⇒≈` | [03.5](../paper-1/spec/03.5-decoherence.md) | ✅ proved — a clockwork has *no surplus*; the gap is `RelExist.Inversion` below |

## Status — `RelExist.Inversion` (the inversion `≈ ⊊ ≅`, nondeterministic)

The doctrine's headline (A2 restated) over a **nondeterministic** witness — the same early-vs-late
choice as Lean's `Scratch/Identity.lean`, so both proof assistants prove the first-person surplus.

| Result | Agda name | Spec source | State |
| --- | --- | --- | --- |
| nondeterministic transition system (the early/late witness) | `Step` (one constructor per edge) | [03.5](../paper-1/spec/03.5-decoherence.md) | ✅ defined |
| lived identity `≈` (relational bisimulation) | `_≈_` (coinductive, `fwd`/`bwd`) | [02 A2](../paper-1/spec/02-axioms.md) | ✅ defined |
| observational equality `≅` (trace equivalence) | `_≅_`, `HasTrace` | [02 A2](../paper-1/spec/02-axioms.md) | ✅ defined |
| **soundness** `≈ ⊆ ≅` | `≈⇒≅` | [03.5](../paper-1/spec/03.5-decoherence.md) | ✅ proved |
| **strictness** `≈ ⊊ ≅` — the first-person surplus | `surplus` (`p0≅q0` ∧ `¬p0≈q0`) | [03.5](../paper-1/spec/03.5-decoherence.md) | ✅ proved (matches Lean `bisim_ne_obsEq`) |
| **D1** — a fixed point of the dynamics is a stationary self (the eigenform `νΦ`) | `fixpoint-isStationary` / `fixpoint-isSelf` | [D1](../paper-1/spec/02-axioms.md) | ✅ proved (via `coinduction`) |

## Archived — `RelExist.Sparsity` (topological sparsity, paper three)

The topological form of "selves are rare" — the carrier of selves `Stab` is **nowhere dense** in the cylinder
topology on behaviours (`selves-nowhereDense`), with the sharp dichotomy `trivial→allSelf` — is **paper-three**
material. It has been moved to [`archive/agda/RelExist/Sparsity.agda`](../archive/agda/RelExist/Sparsity.agda)
so the live Agda layer holds only paper-one witnesses, matching the Lean side (sparsity lives in `archive/`).
It imports the live `RelExist.Coinductive` and is itself `--safe --guardedness`; details in
[`archive/spec/03.7-sparsity.md`](../archive/spec/03.7-sparsity.md).

Both live modules are checked with `--safe --guardedness`: no postulates, no escape hatches — every
coinductive proof is machine-verified productive. `RelExist.Coinductive` is the constructive, final-coalgebra
counterpart of the Lean side's lattice-theoretic `RelExist.We` (`νΘ`), so the doctrine's `≈` now has **two
independent mechanizations** that agree.

## Build / check

```sh
cd agda
agda RelExist/Coinductive.agda   # the ν-layer (theorem 3.2)
agda RelExist/Inversion.agda     # the first-person surplus ≈ ⊊ ≅
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
