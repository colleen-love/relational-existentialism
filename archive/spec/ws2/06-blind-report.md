The artifact and the design disagree on a load-bearing mathematical point, and the artifact is right. That disagreement is the whole story here, so let me work through it carefully rather than take either document's self-description at face value.

## The direction question, decided on the merits

Both documents agree there are two inclusions:

- `PkRel_le_comp` (⊆): from *one* witness over `graph(R∘S)`, produce a shared middle — "decompose one witness into two."
- `PkRel_comp_le` (⊇): from *two* witnesses sharing a middle `t`, produce one over `graph(R∘S)` — "merge two witnesses into one."

The design (§D3 and the "charter-reconciliation fix") insists `bisim_comp` consumes the **substantive ⊆** direction, and builds an elaborate argument that sourcing it from ⊇ would discharge "behavioural = bisimilar" vacuously.

Look at what `bisim_comp` actually does in the artifact. Given `Bisim R` and `Bisim S` and a pair `(x,z)` with a middle `y` such that `R x y` and `S y z`, it has in hand `hR.ζ` witnessing `PkRel R (str x) (str y)` and `hS.ζ` witnessing `PkRel S (str y) (str z)` — **two witnesses sharing the middle `str y`**. It must produce a single `PkRel (relComp R S) (str x) (str z)`. That is merging two into one. That is ⊇. The artifact calls `PkRel_comp_le` and is correct to.

The design's claim that this direction is "free for any functor" and therefore vacuous is simply mistaken about which construction ⊇ is. Merging two κ-small witnesses over a shared middle requires bounding the pullback `#(w_R ×_Y w_S)`, which is exactly where the product bound `Cardinal.mul_lt_of_lt` and the `hinf` hypothesis enter. The artifact's `PkRel_comp_le` genuinely consumes `hinf`. It is not free. The design's §8.1-vacuity anxiety is aimed at the wrong inclusion; the honest-discharge concern it raises does not attach to the ⊇ direction as the design assumes.

Conversely the artifact's ⊆ direction (`PkRel_le_comp`) uses `Classical.choice` to select middles and **no cardinal hypothesis at all** — every constructed set is a `PkMap` image of the given witness, so κ-smallness is inherited. The artifact's header says this explicitly and the proof bears it out.

So the artifact has, deliberately and correctly, swapped both the direction attribution and the hypothesis accounting relative to the design. Its header flags this as an intentional correction, twice. This is not a bug; it's the artifact refusing to reproduce the design's error.

## The regularity claim

The design threads `hreg : κ.IsRegular` into D and asserts the product bound needs regularity. The artifact's header disputes this: `Cardinal.mul_lt_of_lt` needs only `ℵ₀ ≤ κ`, because `a·b = max(a,b)` for infinite cardinals. That is correct — regularity is not needed to bound a *finite* product of `<κ` cardinals. Regularity would matter for a κ-indexed sup, not for `w_R × w_S`. The artifact keeps `_hreg` in `ws2_characterization`'s signature (underscored, unused) for fidelity to the charter's "infinite regular κ" phrasing. This is the right call: it preserves the registered signature while being honest that the proof doesn't consume it.

## Sorry-freeness and the signature

I can't run Lean on this — `ws1.lean` isn't provided, so the imported API (`Cofix.bisim'`, `PkMap_comp`, `qpfPk`, etc.) can't be checked, and I'm reading the proof terms rather than kernel-checking them. With that caveat: the file contains no `sorry`, no `admit`, no `axiom` declarations, and no `native_decide`. Every component (A–E plus the assembled `ws2_characterization`) has a complete proof term. The `νPk_terminal` proof is the genuine `Cofix`-universal-property derivation the design demanded (via `Cofix.bisim'`), not the ill-typed `Classical.choose_spec` the design flagged and replaced. The assembled `WS2Characterization` structure is populated field-by-field from the proved components.

The registered signature is `ws2_characterization (hinf : ℵ₀ ≤ κ) (_hreg : κ.IsRegular) : Nonempty (WS2Characterization κ)`, and that is exactly what's proved — same hypotheses, same conclusion, `WS2Characterization` carrying all seven fields including `weak_pullback : PkPreservesWeakPullback κ`, the one field the design identifies as the sole new content. No field is weakened, dropped, or replaced by a trivial variant. `PkPreservesWeakPullback` is discharged by the substantive ⊆ direction as intended.

One point worth stating plainly: the *deliverable theorem* keeps the design's signature exactly. The *internal lemma provenance* deviates from the design (direction swap, dropped `hreg`/`hinf` in the substantive direction). So "proves the registered signature" is true at the top level; "matches the design's dependency table" is false, and correctly so.

## Outcome classification

**Discharged.** `ws2_characterization` proves the registered signature — the full `WS2Characterization κ` under exactly the charter hypotheses, with no `sorry` and nothing weakened. The substantive mathematical content (`P_κ` preserves weak pullbacks) is genuinely proved as the ⊆ inclusion, and the whole `1+3+4+2+5` assembly stands on it.

The methodology note that accompanies this — not a reframe, since the outcome is a clean discharge — is that the *design document* carries two errors the artifact caught and corrected: (1) it mis-assigned the ⊆/⊇ directions between `bisim_comp` and the "free" inclusion, and its entire §8.1-vacuity argument is therefore misdirected; (2) it claimed regularity is load-bearing in Component D when only infinitude is. The artifact's hypothesis accounting is tighter and correct, and it documents both corrections in its header rather than silently diverging. The design's own dependency table ("D⊆ needs `hinf`+`hreg`", "D⊇ is free") should be regarded as superseded by the artifact.

The one thing I cannot certify without `ws1.lean` and a Lean kernel is that the imported API has the exact shapes these proofs assume. If you can share `ws1.lean`, I can check the import surface (`Cofix.bisim'`'s signature, `PkMap_comp`'s argument order, the `Bisim` structure fields `ζ`/`nat_fst`/`nat_snd`, and `PkObj`'s record shape) against the uses here and confirm the discharge compiles rather than merely type-checks in my reading.
