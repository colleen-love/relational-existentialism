# WS6 verification

## `sorry`-free / axiom status

No `sorry` appears anywhere in the file, and no custom `axiom` declarations are introduced. Every result rests on imported ws1/ws2 theorems (themselves axiom-free per their headers) plus Mathlib's `CategoryTheory` API. The claimed axiom budget `[propext, Classical.choice, Quot.sound]` is consistent with the constructions used (`Classical.propDecidable` as a local instance, terminality/Lambek machinery from ws1). Nothing suspicious — the file is `sorry`-free as claimed, modulo an actual `#print axioms` run which the environment can't perform here.

## Registered signature vs. what is proved

This is the crux, and the file is unusually honest about it. There are **two deviations from the design's registered signatures**, both surfaced explicitly rather than hidden:

**F3 signature change (the important one).** The design (§2.3, Doc 1) registers:

```
ws6_empty_standpoint (obs) (h : PositionFree obs) : (∀ u, obs u) ∨ (∀ u, ¬ obs u)
```

The artifact does **not** prove this. It proves instead:

```
ws6_standpoint_vacuous (obs) : PositionFree obs
```

The header note argues the registered disjunction is *false as stated*: since `endo_eq_id` makes `PositionFree obs` hold vacuously for every `obs`, the design's theorem would force every predicate on the carrier to be constant, which is refuted by any non-constant `obs` on the ≥2-element (`ws2_nondegenerate`) carrier. This reasoning is correct — the registered F3 signature is genuinely unprovable (indeed refutable), and the artifact substitutes the true proposition. So F3 does **not** meet its registered signature; it meets a corrected one. Critically, this is not a stealth weakening: `ws6_standpoint_vacuous` proves *less* apparent content and the file routes the difference as the criterion-(vi) shortfall.

**F4 signature change (minor/structural).** The design bundles `D` as an internal field of `FaithfulCarrierEmbedding`; the artifact lifts `D` (and its `Category`) to explicit parameters to avoid a typeclass diamond. The mathematical content of `ws6_poles_split` is otherwise the registered one, and the proof is sound: `coincide` ⟹ each `E.F.obj x` terminal ⟹ hom-subsingleton ⟹ `F.map f = F.map g` ⟹ (faithful) `f = g`, contradicting `distinct`. The load-bearing mechanism is terminality (`eq_of_tgt`), matching the design's Revision-1 correction. `ws6_embedding_nonvacuous` genuinely certifies the hypothesis is inhabited and `coincide` fails in `WCat`, so the theorem is not vacuous.

**F2** proves its registered signature (`ws6_no_maximal`) cleanly — maximality injects the whole carrier into a `<κ` support, contradicting `κ ≤ #X`. Correct.

**F5** proves `ws6_relative_bottom` as registered (empty-observation pole + untouched identity theory). Correct.

**`ws6_no_faithful_zero_host`** is, as the design demands, stated as a `Prop` and left uninhabited — not proved, correctly, and flagged as almost certainly false as a blanket.

## Outcome classification

The registered *criterion* the charter assigns WS6 is **(vi)**, "no substantive terminal standpoint." That criterion is carried only by F3, and F3 is vacuous — the substantive form of (vi) is **not** delivered. So the workstream as a whole cannot be classified Discharged.

Breaking it down by the charter's §5 vocabulary:

- **F4 `ws6_poles_split` — Impossibility-proved (scoped).** A sharp negative (total identification of the carrier with a zero object is impossible); counts as success per §5. But its scope is the `coincide` (total-collapse) case only, not the broader cross-category claim.
- **F2 `ws6_no_maximal` — Discharged**, by `κ`-fiat (inherited WS1 obligation, not `(F,κ)`-independent).
- **F3 `ws6_standpoint_vacuous` — Failed against the registered signature**, and the design's registered F3 proposition is itself unprovable/false. The *honest* residual is that criterion (vi) is **Open**.
- **F5 — Partial-by-construction.**

**Overall: PARTIAL**, with the obstruction made precise. The poles-coincidence hazard resolves as a provable (scoped) impossibility, F2 and F5 land as designed, but the workstream's core criterion (vi) is not achieved — because the registered F3 theorem is false and the true statement is vacuous, leaving (vi) genuinely Open. The obstruction is stated sharply: the terminal carrier admits only the identity endo-view (`endo_eq_id`), so substantive standpoints require spans out of non-terminal coalgebras that `νPk` alone does not furnish; this is routed to a sheaf/site layer over the coalgebra category, coupled to WS2's category choice and WS7's `(F,κ)`.

## Methodology note (triggered by the partial result)

The file's own framing is methodologically sound and worth endorsing: it does not reframe the two signature failures as successes. Two points deserve flagging as the required note rather than a reframe:

The design-level F3 signature was **mathematically defective** — not merely hard. `ws6_empty_standpoint`'s disjunction is refutable on any non-degenerate carrier, so the design review that registered it contained an error that only surfaced at formalization. This is exactly the kind of drift the charter's §8.2 naming discipline exists to catch, and here it was caught at the right layer (the artifact refuses the false theorem and renames). The lesson: a registered signature can be wrong, and formalization is the check that catches it; the correct response was substitution-with-disclosure, which is what happened.

Second, the assembly `WS6NoPoles` deliberately omits any `standpoint_substantive` field, so no importer can read (vi) as closed from the bundle, and the top-level theorem is named `ws6_split_and_no_maximal` rather than `ws6_resolved`. That naming discipline is the correct structural safeguard for a Partial outcome and matches the WS4/WS5 precedent in the sibling files. The classification should therefore stand as **Partial**, not be laundered upward by the genuine F4 impossibility.
