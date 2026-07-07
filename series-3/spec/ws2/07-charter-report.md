Now I can check the import surface, since `ws1.lean` is provided. Let me do that first, then map WS2 up to the charter.

## Import-surface check: does ws2.lean rest on what ws1.lean actually provides?

Going through every WS1 name ws2.lean cites as "established, axiom-free":

- `Coalg`, `IsTerminalCoalg`, `PkObj`, `PkMap`, `PkMap_id`, `PkMap_comp` — all present, and the `Bisim` structure fields are exactly `ζ`/`nat_fst`/`nat_snd` with the signatures ws2.lean uses. The `diagBisim` and `bisim_comp` constructions match these field types.
- `bisim_eq`, `hom_unique`, `lambek`, `omegaCoalg`, `emptyCoalg`, `mk_empty_lt`, `mk_singleton_lt` — all present with matching signatures. `ws2_bisim_eq` calls `bisim_eq (νPk_terminal κ)` correctly.
- `qpfPk`, and the `Cofix`/QPF API (`Cofix.corec`, `Cofix.dest_corec`, `Cofix.bisim'`, `QPF.abs_repr`, `QPF.abs_map`, `QPF.repr`, `QPF.abs`) — present via the `qpfPk` instance.

The decisive item: `νPk_terminal` in ws2.lean is **the exact same proof term** as `exists_terminal_coalg`'s body in ws1.lean, specialised to the concrete carrier. Compare them line by line — the `refine ⟨Cofix.corec C.str, …⟩`, the `Cofix.bisim'` call with `fun _ => True`, the three `calc`/`refine` obligations discharged by `QPF.abs_repr`/`QPF.abs_map` — they are identical. Since ws1.lean's version type-checks against the real `qpfPk` instance (that's what makes `exists_terminal_coalg` a theorem there), the specialised copy in ws2.lean type-checks against the same instance. This is the strongest confirmation available short of running Lean: the one genuinely non-trivial reused proof is verified transitively by matching an already-checked term.

One important discrepancy to flag, though it does not break anything: `exists_terminal_coalg` produces `⟨Cofix (PkObj κ), Cofix.dest⟩` as an *anonymous* witness, whereas ws2.lean defines `νPk κ := ⟨Cofix (PkObj κ), Cofix.dest⟩` and reproves terminality directly rather than importing `exists_terminal_coalg` and transporting. This is the *right* choice — it avoids the `Classical.choose` indirection the WS2 design memo itself flagged — and it means ws2.lean depends on `qpfPk` and the `Cofix` API but not on `exists_terminal_coalg` as a lemma. So the reused surface is the QPF instance, not the existence theorem. That's cleaner, not weaker.

Everything else checks: `PkMap_comp`'s argument order (`g f s`, giving `(g∘f)'' = g''(f'')`) matches every `rw [← PkMap_comp]` in `PkRel_le_comp` and `diagBisim`. The `PkObj` record shape (`⟨Set.range g, proof⟩` with a `Cardinal.mk (↥s) < κ` field) matches `PkRel_comp_le`'s explicit `⟨Set.range g, …⟩` construction and its `Cardinal.mk_range_le` bound. `mk_singleton_lt`/`mk_empty_lt` usage in `ws2_nondegenerate` matches ws1.lean's signatures.

So my earlier caveat is now discharged: the import surface is consistent, and ws2.lean is sorry-free and axiom-free beyond Mathlib's standard `propext`/`Classical.choice`/`Quot.sound` — the same three ws1.lean rests on. The AFA modeling is coalgebraic; no set-theoretic AFA axiom is imported anywhere.

## Mapping the verified WS2 theorem to the charter

`ws2_characterization` proves, for infinite regular κ, a `WS2Characterization κ` with seven fields. Against the charter these map as:

Criterion (i), *no atoms* — carried at the carrier level by `nondegenerate` plus the terminal/Lambek structure inherited from WS1's `Ω = {Ω}` construction. WS2 doesn't re-establish atomlessness; it inherits the WS1 carrier.

Criterion (ii), *each element identified with its relational unfolding up to bisimulation* — this is the load-bearing one, and it's where WS2 does genuine new work. The charter §8.1 WS2 audit is explicit: the *meaningful* form of (ii) is "behavioural equivalence = bisimilarity," and it is "conditional on weak-pullback preservation." `ws2_weak_pullback` proves `P_κ` preserves weak pullbacks (the substantive ⊆ direction, `PkRel_le_comp`), and `ws2_bisim_behavioural` proves behavioural equivalence coincides with identity, with transitivity (`bisim_comp`) genuinely consuming the preservation content. So the criterion is discharged *non-vacuously* — exactly the discipline §8.1 demanded ("prove weak-pullback preservation, don't discharge the coincidence without using preservation").

Criterion (vii), *non-degenerate — the ≥2-element part* — `ws2_nondegenerate` gives it, matching the §7 REV-A note that the bounded reading "contributes the ≥2-element part of (vii)."

Criteria (iv), (v), (vi), and the *full* non-collapse part of (vii) — WS2 does not touch these, and the charter doesn't ask it to. They belong to WS3/WS5/WS6/WS7.

## The functor-commitment question the charter foregrounds

The charter's WS2 hazard (§8.1) has two prongs. First: commit to a functor and prove weak-pullback preservation for it. WS2 commits to `F = P_κ` (the deliverable header states this explicitly and defers the Framing 6 / `W_Q` enrichment fork to WS4) and proves preservation for it. Discharged as stated.

Second prong: the charter warns that *if* WS2 or WS4 moves to a weighted/enriched functor, preservation "can fail, and then bisimilarity and behavioral equivalence come apart." WS2 does not resolve this — it explicitly **defers** it. `ws2_characterization`'s scope is `P_κ` only. The enriched-functor question (where the split might occur) is handed to WS4, precisely as §6.1's shared-`(F,κ)` structure and §8.1's "this choice binds WS4" require. This is a clean hand-off, not an unacknowledged gap.

## The two internal corrections carry up to the charter cleanly

From my earlier review: ws2.lean corrects the WS2 *design memo* on two points — the ⊆/⊇ direction attribution for `bisim_comp`, and the false claim that regularity is load-bearing in Component D. Neither correction disturbs the charter mapping. The charter cares that (ii)'s meaningful form is proved using preservation; ws2.lean does that via whichever inclusion actually merges witnesses (⊇, `PkRel_comp_le`, consuming `hinf`) for transitivity and the substantive ⊆ (`PkRel_le_comp`) for `PkPreservesWeakPullback`. Both inclusions are proved, so the assembled `weak_pullback` and `behavioural` fields are sound regardless of the memo's misattribution. And `ws2_characterization` retains `_hreg : κ.IsRegular` in its signature for charter fidelity ("for κ infinite regular"), even though the proof shows regularity is unnecessary — the theorem still proves the registered signature, just under a hypothesis it doesn't consume.

## Workstream-level outcome

**Discharged** — for the WS2-owned obligation, as scoped by the charter.

WS2's registered obligation (§4, §6 deliverable 2, criterion ii) is: choose the observation functor, prove `νF` exists and characterize its bisimulation, with the meaningful (behavioural = bisimilarity) form secured via weak-pullback preservation. `ws2_characterization` does exactly this for `F = P_κ`: existence and terminality of the concrete `νPk` (Component A), bisimulation = identity (C), weak-pullback preservation proved as new content (D), behavioural equivalence = identity built non-vacuously on it (D3), and coinduction / up-to-equivalence (E) — sorry-free, axiom-free beyond Mathlib's three, resting on a verified-consistent WS1 import surface. This is stronger than the memo planned (it eliminates a spurious regularity hypothesis and corrects the direction bookkeeping) and it discharges the exact §8.1 discipline the charter was most worried about.

The methodology note that accompanies a Discharged outcome is small and forward-pointing, not a correction to WS2 itself:

The charter's §8.1 WS2 hazard is only *half* retired. WS2 discharges (ii) for `P_κ`, but the charter's live worry — that an enriched/weighted functor breaks weak-pullback preservation and splits bisimilarity from behavioural equivalence — is deferred to WS4 (the Framing 6 / `W_Q` fork), not settled. So WS2 should be reported as "discharged for `F = P_κ`," carrying an explicit ratification obligation to WS4: if WS4 changes the functor for §3.5 grading, it must re-prove preservation for the enriched functor *or* declare the bisimilarity/behavioural split as a §8.2-style open substitution. Two smaller carry-forwards: the `hinf`-vs-`hreg` correction means downstream workstreams citing "κ infinite regular" for the bisimulation theory are over-hypothesizing — only `ℵ₀ ≤ κ` is used — which WS7 should note when it fixes a concrete κ; and, as with WS1, the axiom-freeness rests on a static reading of the artifact, so a live `#print axioms ws2_characterization` against current Mathlib is still owed before "axiom-free" is reported without qualification.

One thing I'll continue to flag honestly: "Discharged" here means the proof terms type-check against the WS1 surface as I've traced them and contain no `sorry`/`axiom`/`admit`. It is not a substitute for a machine `#print axioms` run, which is the only thing that certifies the Mathlib-axiom claim against a live toolchain. If you can run that against both `ws1_C1` and `ws2_characterization`, it would close the last operational gap the charter's own §8.1 note already identifies as owed.
