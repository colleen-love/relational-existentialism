I'll verify this Lean artifact against the design document's registered signatures. Let me set up the environment and actually check it compiles, since claims about `sorry`-freeness and axiom-freeness are checkable.The file content is in my context as a document, not on disk. Let me write it out and do the analysis. First, let me note that fully building Mathlib in this sandbox is likely infeasible (network is restricted to package registries, and a Mathlib build takes enormous resources), so I'll verify what I can by static analysis of the Lean source against the design's registered signatures. Let me write the file out for careful line-by-line inspection.Let me do the substantive analysis. I need to check several things carefully. Let me be honest upfront: I cannot compile this against Mathlib in this sandbox, so my verification is a careful static audit, not a machine-checked confirmation. Where the artifact's correctness hinges on the exact behavior of Mathlib lemmas (`card_typein_toType_lt`, `Cofix.bisim'`, etc.), I'll flag what would need machine-checking.

Let me work through the key claims.

**1. `sorry`-freeness and axioms (textual).** No `sorry` appears anywhere in the source. No `axiom` declaration appears — the header explicitly states the earlier `exists_terminal_coalg` axiom was deleted and replaced by a theorem. This is consistent with the text.

**2. The critical question: does the artifact prove the *registered* signature, or a weakened variant?** This is where the interesting divergence lives. Let me compare the design's registered structure against the artifact's.Now let me assess the individual proof obligations for soundness, and identify the one place I think warrants the most scrutiny — the QPF construction, which is the load-bearing novelty.Now the most important part of the classification: whether the artifact proves the *registered* signature or a *weakened variant*, and whether the deviation in method matters. Let me examine the subtle points carefully.Now let me check the C2 solution lemma signature and one subtle correctness point in the `IsInfinite` vs `ℵ₀ ≤ κ` hypothesis encoding, plus the `omega_selfsingleton` phrasing difference.I have enough for a rigorous classification. Let me note the one genuine scope gap and the limits of my verification, then give the verdict.

---

## Verification report: `series-3/formal/ws1.lean`

**Verification method / caveat.** I audited the Lean source statically against the design's registered signatures. I could **not** machine-check it: building Mathlib is not feasible in this sandbox (no Lean toolchain present, and the network is restricted to package registries). So the `sorry`-free and axiom-free claims are confirmed only *textually* (no `sorry` token, no `axiom` declaration anywhere in the file); a definitive `#print axioms ws1_C1` and a clean `lake build` still need to be run in a real Mathlib environment. Everything below is conditional on the source compiling, which hinges on a handful of Mathlib lemmas behaving as named — flagged at the end.

### Signature fidelity — proves the registered signature, not a weakened variant

Every field of the design's §5 `GroundlessCarrier` and every registered theorem statement is matched, with three cosmetic re-encodings that are provably equivalent, not weakenings:

- **`struct : U ≃ P_κ.obj U`** → **`lambek : Function.Bijective carrier.str`**. Bijectivity of the structure map *is* the Lambek iso; equivalent content.
- **`omega_selfsingleton : struct ω = ⟨{ω},_⟩`** → **`(str ω).1 = {ω}`**. Subtype equality is `.val` equality (`Subtype.ext`); equivalent.
- **`κ.IsInfinite`** → **`ℵ₀ ≤ κ`**. Same predicate for cardinals.

The **C2** statement (`ws1_C2`) matches design Theorems 6.2/6.3 verbatim in content (`∃! sol`, same defining equation), with uniqueness routed through terminality's uniqueness clause exactly as the design demands. `omega_consistency` (Lemma 6.4) is present and proved via one use of `hom_unique`, matching the design's insistence that it is "not free."

The `bisim_eq` field is precisely design **Theorem 3.2** ("every bisimulation ⊆ diagonal"), which is what the registered `GroundlessCarrier` signature calls for. Design Lemmas 3.1/3.1a (weak-pullback preservation, greatest-bisimulation packaging) are **not** in the registered signature and are correctly and openly flagged as absent — this is a documented non-inclusion, not a silent weakening of a registered obligation.

### Method deviation — a strengthening, not a weakening

The design reaches existence through the transfinite terminal sequence resting on a **permanent `stabilization_theorem` axiom** (design §5 states `ws1_C1` is "conditional on the `stabilization_theorem` axiom"). The artifact abandons that route and instead proves existence via a **QPF/`Cofix`** construction: bounded powerset over a *fixed* κ is a quotient of the polynomial functor whose position types are the initial segments of `κ.ord.toType` (each `< κ` because `κ.ord` is the least ordinal of cardinality κ). This is a legitimate and known technique, and the construction reads correctly: `absPk = range`, `reprPk` enumerates a `<κ`-set by the order-type-`(#s).ord` initial segment, with the `QPF` laws discharged by `Subtype.ext` + range identities, and terminality obtained from `Cofix.corec`/`dest_corec` (cone) and `Cofix.bisim'` (uniqueness).

The registered *theorem statement* `ws1_C1` is unchanged; the proof is strictly **stronger** — it discharges the same conclusion with no custom axiom and, in fact, needs neither regularity (`_hreg`, underscored/unused) nor infiniteness for existence (κ-hypotheses consumed only for the Ω-singleton and non-degeneracy). This eliminates the design's single highest-risk external import.

### Outcome classification

**DISCHARGED.** The artifact proves the registered signature of the WS1 deliverable — `ws1_C1` (existence of the `GroundlessCarrier` with all bundled fields) and `ws1_C2` (the solution lemma) — as theorems, textually free of `sorry` and of any `axiom` declaration, via a route that removes the design's conditional dependence on `stabilization_theorem`. The three signature differences are equivalent re-encodings, and the omitted Lemmas 3.1/3.1a fall outside the registered signature and are declared.

Two boundary conditions attach to that verdict, neither of which downgrades it:

1. **The declared WS1↔WS7 bounded-carrier drift persists** (design §0.1/§8). Existence is proved for the κ-bounded functor `P_κ`, not charter §3.1's full-powerset/AFA carrier. This is a *modeling choice*, not an unproved obligation — and it is orthogonal to the axiom question the artifact resolves. The "which bound / no-everything" question (charter §3.7–§3.8) remains a genuine WS1↔WS7 joint obligation, unaffected either way.

2. **My check is static.** A methodology note rather than a reframe: to convert this from "audited sound" to "machine-confirmed," run `lake build` and `#print axioms ws1_C1` / `ws1_C2` against current Mathlib. The results most worth confirming are the exact names/signatures of `Ordinal.card_typein_toType_lt`, `Cofix.bisim'`, `Cofix.dest_corec`, and `QPF.Cofix`'s API, since the whole axiom-elimination rests on them existing as used. If any of those has drifted in the Mathlib version targeted, the file would fail to compile — but the mathematics of the route would remain valid and repairable.
