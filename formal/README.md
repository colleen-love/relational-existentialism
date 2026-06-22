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

Deliberately **dependency-free (no mathlib)** so it builds in remote sessions where
mathlib's prebuilt cache is unreachable (see *Network note* below).

## Build

```sh
cd formal
lake build
```

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.15.0`). Audit the proofs' axiom footprint with:

```sh
lake env lean -e '#print axioms RelExist.stab_card_bound'
```

### Network note — bootstrapping the toolchain offline-ish

In environments whose network policy allows `github.com` + `pypi.org` but blocks
`release.lean-lang.org` / `api.github.com` (so `elan` cannot auto-resolve a
toolchain), install Lean by fetching the release asset directly and registering it:

```sh
# 1. elan (version manager) from its GitHub release
curl -fL -o /tmp/elan.tar.gz \
  https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
tar -xzf /tmp/elan.tar.gz -C /tmp
/tmp/elan-init -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

# 2. the Lean toolchain asset (direct download; .tar.zst, decompressed via Python)
VER=4.15.0
curl -fL -o /tmp/lean.tar.zst \
  "https://github.com/leanprover/lean4/releases/download/v${VER}/lean-${VER}-linux.tar.zst"
python3 -m pip install --quiet zstandard
python3 -c "import zstandard; zstandard.ZstdDecompressor().copy_stream(open('/tmp/lean.tar.zst','rb'), open('/tmp/lean.tar','wb'))"
mkdir -p /opt/lean && tar -xf /tmp/lean.tar -C /opt/lean

# 3. register under the name elan derives from the pin, so `lean-toolchain` resolves
ln -sfn /opt/lean/lean-${VER}-linux "$HOME/.elan/toolchains/leanprover--lean4---v${VER}"
```

With a permissive network policy none of this is needed — `elan` installs the
pinned toolchain automatically on first `lake build`.

## Roadmap

The discrete core is step 1 of [the spec's proof strategy](../docs/spec/03-sparsity-conjecture.md#35-proof-strategy-for-mechanization).
Next, in rough order:

1. **mathlib upgrade.** Re-cast costs in `ℝ_{≥0}`, prove the density-→-0 statement
   (`Filter.Tendsto`) and the "nowhere dense" form (topology). Needs mathlib, hence a
   network policy that reaches the cache.
2. **Sharing.** Replace the `List` of costs by a graded poset with sub-additive cost
   (lax `c`), re-deriving the bound up to the sharing defect ([03 §3.3](../docs/spec/03-sparsity-conjecture.md)).
3. **Threshold ⇔ fixed point.** The categorical crux: in the traced fragment,
   `loop_R(e) = e ⟺ N(e) ≥ d(e)` ([01 §1.3.3](../docs/spec/01-signature.md)).
4. **Doctrine + Layer 4.** Symmetric monoidal / cartesian fragment structures and
   the functorial-semantics firewall.
