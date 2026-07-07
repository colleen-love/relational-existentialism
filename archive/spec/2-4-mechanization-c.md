# 2-4-mechanization-c — Work Order: the Lambek Sub-problem and the Resumed Re-anchoring

Target file: `series-2/formal/Spec24e.lean` (or extend Spec24d if the roots fight; log the choice). Conventions unchanged: no `sorry`; doc-comments with spec addresses (cite 2.4); axiom audit in-build; results post-hoc-marked; hostile-first. **FP-B3 through FP-B6 remain in force exactly as frozen in order b** — this order does not refreeze them; it adds only the sub-problem's own predictions (FP-C1/C2 below).

**Scope in one line.** Unblock `Infinite Ω_R` by whichever of two routes lands, retire the Lambek debt if affordable, then execute order b's Stages 2–6 unchanged. The O-2-4-5 closing discipline carries over verbatim: on completion, record that the condition is met and hand the file back without touching §8.

---

## Stage 0 — the sub-problem: two routes to `Infinite Ω_R`

**Route C — Lambek-free infinitude (MUST; the primary path).** No `mk` needed; only `Cofix.corec`, `Cofix.dest`, and `dest_corec`, all of which univariate QPF provides.

- The family: `tower : ℕ → Ω_R` by corecursion from `g : ℕ → HC ℕ` with `g 0` the object-sorted self-pair (sort-profile (O,O)) and `g (n+1) = s(inr n, inr n)` (pure R–R on the predecessor). `tower n` is a spine whose descent reaches the (O,O) profile at exactly depth n.
- The separator: a depth-observation function `obs : ℕ → Ω_R → SortProfileTree k` (or the minimal observable: "depth of first (O,O) profile," valued in ℕ∞) defined by iterated `dest`, computed on the family via `dest_corec`. This is the same separation technique that proved `elt2 ≠ elt3` and `eqDepthC_nontrivial` — leveraged, not reinvented; if `EqDepthR` can serve directly as the separator, prefer it.
- **FP-C1 (frozen):** `tower_injective` — distinct indices give distinct elements (unequal observations at depth min(m,n)) — hence `Infinite Ω_R` via `Infinite.of_injective`.
- Membership: `tower n ∈ Ω_R`-coherent-part where needed — the spines satisfy K1–K3 by construction (self-witnessing at the base, borne-where-bearing along the spine); if coherence membership is needed for T16_ω's statement over Ω_C, prove `tower_mem_ΩC` via `imageC_good` on the evident coherent description.

**Route A — Lambek by hand (SHOULD-strong; the durable asset).** Worth its own effort regardless of Route C, because it pays the spec's standing "Lambek in both sorts" claim, and it is an upstream candidate (univariate `QPF.Cofix.mk` at parity with `MvQPF.Cofix.mk`).

- `mkC : HC Ω_R → Ω_R := Cofix.corec (Functor.map Cofix.dest)`.
- `mkC_dest : mkC (dest t) = t` — the coinductive core, via the univariate bisim principle (`Cofix.bisim` or `bisim'`; if the available bisim's hypotheses fight the HC instance, log the obstruction precisely — that log is itself a deliverable).
- `dest_mkC : dest (mkC x) = x` — derived: `dest_corec` gives `dest (mkC x) = map (mkC ∘ dest) x`; `mkC ∘ dest = id` by funext on `mkC_dest`; `map_id` closes.
- `destEquivC : Ω_R ≃ HC Ω_R` packaged; doc-comment: Lambek mechanized for the corrected functor, retiring the claim from 2.4 §2's construction paragraph.
- **FP-C2 (frozen, honestly uncertain):** the bisim route closes without new axioms beyond the file's existing audit profile. If it does not, Route C stands alone, the gap is documented in 2.4 §10, and Route A moves to the MAY ledger below.
- **Drop clause (sanctioned):** if Route A exceeds a working session after Route C has landed, drop with the obstruction logged.

**MAY — upstreaming.** Prepare `QPF.Cofix.mk`/`mk_dest`/`dest_mk` as a minimal standalone mathlib PR candidate (no project vocabulary in it). A small, citable community artifact; zero project risk; entirely optional.

## Stage 1 — T16_ω (MUST; = order b Stage 2, unchanged)

- `T16_ω` from finite `pat` + `Infinite Ω_R` (FP-B3). The mandatory loan caveat carries verbatim: scaffold-assisted, not the κ-loan's discharge; downstream consumers inherit by citation.

## Stage 2 — the C1 landing (SHOULD; = order b Stage 3, unchanged; the star)

- FP-B4 (global disconnection, hostile) and FP-B5 (`no_windowless_hosted` — *we are born as bridges*, both prices in the doc-comment) exactly as frozen.

## Stage 3 — P3h positive (SHOULD; = order b Stage 4, unchanged)

- `ConnectedDescription`, `hosted_of_closeC_connected` (FP-B6), completing FP3's split.

## Stage 4 — B5 interface pack (SHOULD; = order b Stage 5, unchanged)

- T14 pack, Reveal pack (P1 barrier two existence, T13 chain-step bound), `deployableC` dichotomy, `holdDepthC` support lemmas. T14d MAY, drop freely.

## Stage 5 — T4 scaffolding (MAY; = order b Stage 6, unchanged)

- Profile definitions, `≈w`, refl/symm, cheap non-degeneracy witness. S1 and T7 remain gated to the next order, hostile-first there.

---

## New frozen predictions (this order only)

| # | Prediction | Falsifier would mean |
|---|---|---|
| FP-C1 | `tower` injective; `Infinite Ω_R` Lambek-free | depth-observation misread; T16_ω blocked pending Route A |
| FP-C2 | univariate bisim closes `mkC_dest` | mathlib gap deeper than diagnosed; document in §10, Route A to MAY |

## Deliverable summary

| Stage | Level | Contract items |
|---|---|---|
| 0 | MUST (C) / SHOULD (A) / MAY (upstream) | FP-C1; destEquivC + FP-C2; PR candidate |
| 1 | MUST | FP-B3 + loan caveat |
| 2 | SHOULD | FP-B4, FP-B5 — the star |
| 3 | SHOULD | FP-B6 |
| 4 | SHOULD | interface pack |
| 5 | MAY | T4 scaffolding |

Success criterion: Stage 0 (Route C) + Stage 1 land → the blocker is retired and FP-B3 is real. Stages 2–4 complete order b's contract; on their completion the O-2-4-5 condition is met — record it, and hand the file back with §8 untouched. The register remains the owner's to open.
