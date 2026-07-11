Let me start by checking git state and merging main, then read the WS2 spec.

Merge succeeded cleanly. Now let me read the WS2 target spec plus supporting docs.

This is a substantial deliverable. Let me read the WS2 Phase 1 (conceptualize) to know what axioms were declared, plus the design doc, and re-read my `ws1.lean` exports.

Let me read the WS2 design doc (02) for definitions like `Rel.comp`, `PkPreservesWeakPullback`, `BisimUpToEquiv`, and re-read my `ws1.lean` to get exact exported names.

Now let me confirm exact `ws1.lean` export names/signatures and a couple of Mathlib API facts I'll build against.

Now let me verify Mathlib's `Rel.comp` and the cardinal product bound:

The API confirms my analysis: `Cardinal.mul_lt_of_lt` needs only `ℵ₀ ≤ κ` (not regularity), and `Rel.comp` matches. I'll build WS2 incrementally, core first. Let me write the foundation and validate it compiles before adding the harder lemmas.

Now add ws2 to the build and the Series03 root, then compile:

Good news — the hard lemmas (`PkRel_le_comp`, `PkRel_comp_le`, `diagBisim`) compiled. Four fixable issues remain: (1) `PkRel_functorial` needs binder type annotations; (2)/(3) `Bisim` is a `Type` (structure with data), not a `Prop`, so it can't sit inside `∧` — I need `Nonempty (Bisim ...)`; (4) the `coinduction` field binders. Let me fix:

The hard direction (`PkRel_le_comp`) needs just `rfl` after the composition rewrites, and `diagBisim` compiled. `PkRel_comp_le`'s nesting is off (`ab.1.1.2` is a membership proof, not the R-proof). Let me fix `PkRel_le_comp` and rewrite `PkRel_comp_le` with correct projections:

All math errors resolved — just need `noncomputable` on `νPk` (it depends on the choice-based `qpfPk`):

The core WS2 deliverable compiles sorry-free. Now let me add the two remaining design pieces — `bisim_comp` (composition of bisimulations, D3) and the up-to-equivalence coinduction (E). First let me confirm the `EqvGen` API name:

`EqvGen` isn't in this Mathlib. I'll define the equivalence closure inline (a small inductive) for a faithful "up-to-equivalence." Let me add `bisim_comp` (D3) and the up-to component (E):

`bisim_comp` returns `Bisim` (a `Type`, data), so it's a `def` not a `theorem` — and noncomputable (uses `.choose`):

Full WS2 compiles sorry-free — including `bisim_comp` and the up-to component. Now the full build plus the axiom audit the task requires:

Every WS2 theorem depends on **only `[propext, Classical.choice, Quot.sound]`** — Mathlib's standard three. No custom axiom, no AFA-encoding axiom, no `sorry`. Let me clean up, do the full build, and verify sorry-free:

Full build green, no `sorry`, all axiom-free beyond Mathlib's standard three. Let me review git state and the header once more, then commit:

Let me verify my WS1 commits are intact — the log head looks like main's, which needs checking before I commit:

My WS1 work is intact (the recent-by-date ordering just surfaced main's doc commits first). Let me confirm the merge landed and `ws1.lean` is tracked in HEAD:

Everything is consistent: my WS1 branch was already merged into main via PRs #45–47, and `git merge origin/main` fast-forwarded my branch to main's head (which now contains the WS1 QPF work). So my branch is correctly "restarted from latest main" with WS2 as fresh follow-up work. Let me commit and push:

Done. All requested steps complete and pushed to `claude/charter-design-lean-proof-k1l3zl`.

## Summary

**Merged main** — fast-forwarded the branch onto latest `main` (which already contained the merged WS1 work), then built WS2 on top as fresh follow-up.

**`series-03/formal/ws2.lean`** — realizes `04-charter-design-review.md` (Framings 1+3+4+2+5), built on the imported WS1 theorems, wired into the build via `import ws2` in `Series03.lean` and the library roots.

| Design component | Lean |
|---|---|
| A concrete carrier + terminality | `νPk`, `νPk_terminal` (Cofix universal property — corrected, no `Classical.choose`) |
| B non-degeneracy | `ws2_nondegenerate` |
| C bisim = identity | `ws2_bisim_eq` |
| **D weak-pullback preservation (Lemma 3.1a, the new work)** | `PkRel`, `PkRel_le_comp` (⊆), `PkRel_comp_le` (⊇), `PkRel_functorial`, `ws2_weak_pullback` |
| D3 composition / behavioural | `bisim_comp`, `ws2_bisim_behavioural` |
| E coinduction | `ws2_coinduction`, `BisimUpToEquiv`, `ws2_coinduction_upto` |
| assembled | `WS2Characterization`, `ws2_characterization` |

**Build compiles, sorry-free** — `lake build` green; no `sorry`/`admit`.

## `#print axioms` — flagging

Every WS2 theorem (`ws2_characterization` and all components) depends on **exactly `[propext, Classical.choice, Quot.sound]`** — Mathlib's standard three. Checking against WS2 Phase 1 (`01-conceptualize.md`, "Ambient theory"):

- **No AFA-encoding axiom** — consistent with Phase 1's declaration that "AFA is *modeled* coalgebraically … not imported set-theoretically." Nothing to flag.
- **`Classical.choice`** is present but **declared/anticipated in Phase 1**: the ambient is "ZFC (Mathlib)," and the design's Component D proof architecture explicitly calls for `Classical.choice` to select middle points. It appears exactly there (`PkRel_le_comp`, `bisim_comp`) plus inside imported WS1 machinery. Not undeclared.
- `propext`/`Quot.sound` are inherent to the ZFC/Mathlib base.

**Nothing undeclared to flag.**

## Two honest corrections to the design (documented in the file header)

1. **`hreg` (regularity) is unnecessary.** `Cardinal.mul_lt_of_lt` gives the product bound from `ℵ₀ ≤ κ` alone (`a·b = max(a,b)` for infinite cardinals). I thread only `hinf` where the bound is used; `ws2_characterization` keeps the charter's `IsRegular` hypothesis (as `_hreg`, unused) for signature fidelity.
2. **`bisim_comp` consumes the ⊇ direction** (`PkRel_comp_le` — merging two witnesses), not the ⊆ direction the design's §D3 names; composing a bisimulation *builds* a witness rather than decomposing one.

One note: the design's WS4 targets (`ws4_behav_congruence_target` etc.) reference `Quantale`/`WPow`/`WPowObs`, which are explicitly **deferred** to WS4 and undefined here — I did not formalize them, matching the design's "deferred obligation" status.
