# WS2 — The collapse, and the forced answer

**Design doc. Series 4, the intellectual spine. Owns: the Collapse Theorem, the imported-weight leak, and the forced-answer claim (restriction-quality is the essentially-unique atom-free quality).**

*References: `PkObj`, `Coalg`, `νPk`, `IsTerminalCoalg`, `bisim_eq`, `Bisim`, `omegaCoalg` (ws1); the unlabeled-collapse argument `ws10_unlabeled_atomless_collapses` (ws10); the graded functor `WQObj`, `GoodQuantale`, `BotFree`, the Łukasiewicz nilpotence `Luk`, and the cost quantale `ℕ∞` (ws14). WS2 reuses ws10's collapse verbatim and ws14's leak witness verbatim; its new content is the *forced-answer* synthesis.*

## The three results and their status coming in

Two of the three are already proved in Series 3 and are *imported*, not re-derived — WS2's job is to reframe them as the two premises of a single argument and then supply the third (new) step.

| Result | Series 3 source | WS2 role |
|---|---|---|
| Collapse Theorem | `ws10_unlabeled_atomless_collapses` | import as Premise 1 |
| Imported-weight leak | `ws14_core_not_closed_Luk` (nilpotent `Luk`) | import as Premise 2 |
| Forced-answer claim | — (new) | the synthesis |

## Part A — The Collapse Theorem (import + reframe)

```lean
/-- Premise 1. In the plain carrier, atomlessness forces a single point. -/
theorem ws2_collapse (hinf : ℵ₀ ≤ κ) :
    ∀ a b : (νPk κ).X, HereditarilyNonempty a → HereditarilyNonempty b → a = b :=
  ws10_unlabeled_atomless_collapses hinf
```
*No new proof.* The reframing (charter §3.3): this is not a defect but a **proof that difference must bottom out**, and since atomlessness removes the bottom, a second currency of difference is *forced*. WS2's prose (charter §3) is the deliverable here; the Lean is a re-export with the charter-facing name.

**Paper-decidable check that the import is legitimate:** confirm `HereditarilyNonempty` as WS2 states it (every reachable state has a nonempty successor set) matches ws10's hypothesis. One-line correspondence; verify at execute against ws10's actual definition.

## Part B — The imported-weight leak (import + generalize)

The claim to establish: *every* imported quality with a bottom element leaks, not just the one nilpotent witness. Candidates for how strong a statement to make:

### L1 — Single witness (weakest)
```lean
theorem ws2_leak_Luk : ∃ (n : ℕ) (a b : Luk n), a ≠ ⊥ ∧ b ≠ ⊥ ∧ a * b = ⊥
```
Just `ws14`'s nilpotent pair. **Paper triage:** true, already essentially in ws14; but too weak to support "every imported quality cheats" — it shows *one* does.

### L2 — All quantales with ⊥-divisors (middle)
```lean
theorem ws2_leak_general (Q) [GoodQuantale Q] (h : ¬ BotFree Q) :
    ∃ (composite-of-two-atomless-relations), weight = ⊥   -- an atom produced by composition
```
Quantifies over *every* quantale that has ⊥-divisors. **Paper triage:** decidable — `¬ BotFree Q` unfolds to `∃ a b, a * b = ⊥ ∧ a ≠ ⊥ ∧ b ≠ ⊥`, which is exactly the composite needed; the proof is the ws14 negative-half argument with the concrete `Luk` pair replaced by the abstract witnesses. **This is the right strength:** it says the leak is a property of *having a ⊥-divisor*, not of Łukasiewicz specifically.

### L3 — All quantales whatsoever, including BotFree (strongest — and false)
Would claim even zero-divisor-free quantales leak. **Paper triage:** *false*, and usefully so — the BotFree quantales (e.g. `ℕ∞`, ws14's cost quantale) are exactly the escape route, and L3 being false is what makes the escape real. Rejecting L3 is itself content: it locates the leak precisely at ⊥-divisors.

**Winner: L2**, with L3's falsity recorded as the sharp boundary.

```lean
/-- Premise 2. Any imported quality with a ⊥-divisor produces an atom under
    composition. The leak is exactly ⊥-divisibility. -/
theorem ws2_leak (Q) [GoodQuantale Q] (h : ¬ BotFree Q) :
    ∃ (t : WQObj Q κ (νWQ Q κ).X), (members atomless) ∧
      ¬ HereditarilySupported (wqAlg t)
-- proof: ws14 negative half, abstracted from Luk to the h-witness

/-- The boundary: BotFree quantales do NOT leak (the escape route exists). -/
theorem ws2_botfree_safe (Q) [GoodQuantale Q] [BotFree Q] :
    (composition preserves hereditary support)   -- ws14 positive half
```

## Part C — The forced-answer claim (the new synthesis)

This is WS2's original content and the program's boldest claim: **restriction-quality is the essentially-unique atom-free supplier of the second currency of difference.** The design problem is that "essentially unique" can be stated at several strengths, and only some are provable on paper.

### F1 — Existence only (floor)
```lean
theorem ws2_restriction_no_leak :
    -- restriction-quality (WS1's `face`) introduces no ⊥ and no external algebra,
    -- so the L2 leak cannot occur: there is no imported bottom element at all.
```
**Paper triage:** true and easy — restriction-quality has *no* `Q`, hence no `⊥ ∈ Q`, hence the L2 hypothesis `¬ BotFree Q` is not even expressible. The only "empty face" would be the empty *object*, already outlawed. Decidable, provable, but only says restriction *is one* atom-free quality.

### F2 — Uniqueness up to the leak dichotomy (target)
Frame quality abstractly: a **quality assignment** is any way of decorating edges that (i) supplies distinguishing power beyond presence/absence and (ii) supports composition. Prove a **dichotomy**: any such assignment either (a) draws its values from an external algebra — and then either has a ⊥-divisor (leaks, by L2) or is BotFree *by external fiat* (charter §4.2's "forbidden, not unable"); or (b) draws its values from the relata themselves — and is then a restriction-quality up to renaming.
```lean
/-- The forced-answer dichotomy. -/
theorem ws2_forced_answer (A : QualityAssignment κ) (hdist : SuppliesDifference A)
    (hcomp : SupportsComposition A) :
    (External A ∧ (LeaksBy L2 A ∨ BotFreeByFiat A))
  ∨ (Internal A ∧ IsRestrictionQuality A)
```
**Paper triage:** this is the crux and is *only partly* paper-decidable. The classification `External ∨ Internal` is a genuine dichotomy on where values live (decidable to state). The hard clause is `Internal A → IsRestrictionQuality A` — "any internal quality is essentially restriction." This needs a **rigidity argument**: an internal value on the edge `x→y` is a sub-object of the carrier definable from `x`; the maximal canonical such is the reachable face (WS1). Whether *every* internal assignment reduces to it (up to renaming) is the open mathematical content. **Verdict:** state F2 as the target; prove the External branch fully (it is L2 + the fiat observation); prove `Internal → IsRestrictionQuality` under a **canonicity hypothesis** (the internal value is the reachable-through face) and flag the fully general rigidity as the named open.

### F3 — Categorical universal property (strongest, likely deferred)
Restriction-quality as a terminal object in a category of internal quality assignments. **Paper triage:** the right *form* of "essentially unique," but requires setting up that category with its morphisms — more machinery than a first pass warrants; likely a Series-4-late or Series-5 item. Record as the eventual home of F2.

**Winner: F2, reported honestly as "dichotomy proved; internal-rigidity under canonicity hypothesis, general rigidity open."** This matches the charter's own hedge (§5.2: "we conjecture, and WS2 is charged with making this precise").

## The coincidence duty (charter §7)

WS2 is where the coincidence discipline first bites program-wide: the Collapse Theorem (Premise 1) is the **independently forced** fact that makes plurality-via-faces non-trivial. WS3 must re-invoke `ws2_collapse` to show that *removing* faces re-collapses — so plurality is earned against a standing impossibility, not stipulated. WS2 exports `ws2_collapse` under a stable name precisely so WS3 can cite it as the forced counterweight.

## Outcome classes

- **Discharged:** Parts A, B (L2 + boundary), and F1.
- **Partial (expected overall status):** F2 dichotomy with internal-rigidity conditional; general rigidity the named open — the boldest claim delivered as "defended, conditionally proved," per charter §9's pre-registered hedge.
- **Impossibility proved:** the L2 leak and L3's falsity are both sharp negatives counting as success.

## Deliverable

`series-4/formal/ws2.lean`: `ws2_collapse` (re-export), `ws2_leak` + `ws2_botfree_safe` (abstracted from ws14), `ws2_restriction_no_leak` (F1), `ws2_forced_answer` (F2, with the internal-rigidity clause under its canonicity hypothesis and a typed open for the general case). Prose deliverable: charter §§3–5 are WS2's plain-language write-up. Axiom check owed on `ws2_collapse` and `ws2_leak`.
