I'll start by examining the spec and the existing formal directory structure.

Let me explore the formal directory structure and look at existing patterns.

There's no lakefile or toolchain yet. Let me check the repo root and any build/CI setup.

Now let me check the build environment — whether the toolchain and mathlib cache are available.

Environment is ready: Lean 4.15.0, mathlib v4.15.0, oleans cached. Let me confirm the baseline build is green.

Environment confirmed working. Now let me look at the design's target theorems once more and check a couple of Mathlib lemma names before writing.

All lemmas exist. Now let me write the Lean file.

Now update the root to import it:

The module `ws1` isn't registered as part of the library (only `Series03` is a root). I need to register it so Lake builds it. Let me add it to the library roots.

Good — mathlib loads and most of the file elaborates. Two fixes needed.

Build succeeds. Now let me verify it's genuinely sorry-free and audit exactly which axioms the theorems depend on.

The audit is exactly as designed:
- **No `sorry`** (the only grep hit is the word "sorry-free" in a comment).
- `ws1_C1` → standard axioms + my single intentional `exists_terminal_coalg` (mirroring the design's own sanctioned `stabilization_theorem` black box).
- `ws1_C2`, `lambek`, `bisim_eq`, `omega_consistency` → **only** the standard Lean/Mathlib axioms — fully proven, no custom axiom.

Now clean up the temporary check file and restore the lakefile.

Clean and green. Let me review the final state and commit.

Done. The Lean 4 proof is written, compiles green, is sorry-free, and is pushed to `claude/charter-design-lean-proof-k1l3zl`.

## What I did

**`series-03/formal/ws1.lean`** — formalizes the WS1 design (`4-charter-design-review.md`): the Groundless Carrier as the terminal coalgebra of the κ-bounded powerset functor `P_κ`, and everything the design's dependency DAG (§7) builds on it:

| Design item | Lean |
|---|---|
| Lemma 1.1 functoriality of `P_κ` | `PkMap_id`, `PkMap_comp` |
| Lemma 2.3 Lambek (`struct` is an iso) | `lambek` |
| Theorem 3.2 bisimulation = equality | `bisim_eq` |
| §3.3 non-degeneracy `∃ a b, a ≠ b` | inside `ws1_C1` |
| Theorem 4.1 `Ω = {Ω}` | `omega_selfsingleton` field |
| §5 assembled `GroundlessCarrier` (incl. the [NEW] `nondegenerate` field) | `ws1_C1` |
| Theorem 6.2/6.3 solution lemma | `ws1_C2` |
| Lemma 6.4 Ω-consistency | `omega_consistency` |

**Faithfulness on scope.** The design is explicit (§2.1–2.2, §7 item 1) that existence of the terminal coalgebra rests on *one* external black box — the Worrell/Adámek–Koubek stabilization theorem — which the design itself carries as `axiom stabilization_theorem`. I mirror exactly that single sanctioned concession as `exists_terminal_coalg` and prove everything downstream. I also matched the §1.1 discipline: `hreg : κ.IsRegular` feeds *only* the existence axiom, while every downstream cardinality bound uses only `ℵ₀ ≤ κ`.

**Sorry-free verification.** `grep` finds no `sorry`/`admit`. `#print axioms` confirms `lambek`, `bisim_eq`, `ws1_C2`, and `omega_consistency` depend only on the standard `propext`/`Classical.choice`/`Quot.sound`; `ws1_C1` additionally uses the one declared `exists_terminal_coalg` axiom — no hidden axioms, no `native_decide`.

**Build wiring.** `Series03.lean` now `import ws1`, and I added `ws1` to the `Series03` library roots in `lake/lakefile.toml` (an import alone doesn't get compiled unless the module is registered with the library). `lake build Series03` completes successfully.

One note for you: I did not open a PR (none was requested). The branch is pushed and ready if you want one.
