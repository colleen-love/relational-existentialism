# WS1 — Atomless behavior is unique

**Design doc. Series 7, the blocking engine. Owns: the general lemma that on *any* plain `P_κ`-coalgebra all hereditarily-non-empty states are bisimilar, and the recovery of the program's two existing collapses (static, dynamic) as its instances.**

*Series 7 is standalone; all names are transcribed into `series-7/formal/Series7/ws1.lean` and re-namespaced `Series7.WS1` (see `spec/README.md` §6). The core of this workstream is **already built** in Series 6 `ws2.lean` (`hneRel`, `hneRel_isBisim`); WS1's job is to first-class it as the named engine and connect it to both instances. Shared predicates are defined in `spec/README.md` §2 and cited here.*

## The object at stake

The charter's hinge (§3): a single lemma is the root of every collapse the program has proved. Series 4's Parmenides collapse (`ws2_collapse`) concluded *equality* on the terminal coalgebra; Series 6's process collapse (`ws1_productive_unique`) concluded uniqueness on the founded approximations. Both are the same fact one step earlier: **atomless states have one behavior.** WS1 must state that fact at its natural generality — *bisimilarity*, on an *arbitrary* plain coalgebra, not assuming terminality — because it is the weaker, more general form (bisimilarity, not equality) that reaches beyond the terminal object to any construction faithful to relating. Equality is then WS2's job (add behavioral identity). The design question is only how to state and prove the bisimilarity lemma so that (a) it is genuinely general (any `dest`, not just `νPk`), (b) it discharges to the already-built `hneRel_isBisim`, and (c) it recovers the two instances honestly.

**Ambient theory.** `spec/README.md` §2: `PkObj`/`PkMap`; `IsBisim`; `SHNE` (strong hereditary non-emptiness); `hneRel`/`hneRel_isBisim` (transcribed from Series 6 `ws2.lean`); `bisim_eq` on `νPk`.

## Candidates

### C1 — Existential-bisimulation form (the lead; transcribes Series 6)

```lean
theorem ws1_atomless_bisim {X : Type u} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) : ∃ R, IsBisim dest R ∧ R x y :=
  ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩
```
Any two atomless states are related by *a* bisimulation, namely the "both atomless" relation.

- **Ambient `F`:** `P_κ`; the bisimulation is `hneRel dest x y := SHNE dest x ∧ SHNE dest y`.
- **Success condition:** the term typechecks — it is `hneRel_isBisim` plus the two hypotheses.
- **Failure mode:** none structural (the proof is already built in Series 6); the only risk is that "∃ a bisimulation" is *too weak* to be useful downstream if a workstream needs the *greatest* bisimulation or genuine bisimilarity. Checked against consumers below.

**Paper triage.** Decidable-on-paper and already proved: `hneRel_isBisim` exists verbatim in Series 6 `ws2.lean`. C1 is that lemma with the two hne states threaded in. Every downstream consumer (WS2's collapse, WS3's history bridge) needs only "∃ bisimulation relating them", not the greatest one, because behavioral identity (WS2) contains *every* bisimulation in equality. **Winner.**

### C2 — Bisimilarity (greatest bisimulation) form

```lean
theorem ws1_atomless_bisimilar {X} (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    Bisimilar dest x y                                  -- x ~ y, the gfp
```
State it as genuine bisimilarity (membership in the greatest bisimulation).

- **Failure mode:** **needs gfp machinery.** `Bisimilar` as the greatest bisimulation requires the coinductive/gfp apparatus; on an arbitrary `dest` this is extra scaffolding for no gain, since `Bisimilar` is *implied* by "∃ bisimulation relating them" (C1) and behavioral identity only ever consumes the latter.

**Paper triage.** Strictly stronger-looking but downstream-equivalent (C1 ⇒ C2 by the gfp being the union of bisimulations, and WS2 needs neither the union). **Reject as the primary; C1 suffices.** Retain `Bisimilar` only if WS3 needs a canonical relation to name.

### C3 — Anamorphism-to-Ω form (elegant, less general)

```lean
theorem ws1_atomless_maps_to_omega {X} (dest) (x) (hx : SHNE dest x) :
    anamorphism dest x = omegaState hinf          -- the unique morphism sends every hne state to Ω
```
Every atomless state maps to Ω under the unique coalgebra morphism to `νPk`; two atomless states are then bisimilar because they have the same image.

- **Failure mode:** **needs finality.** The anamorphism exists only into the terminal coalgebra, and phrasing the lemma through it *reintroduces* the terminality WS1 exists to drop. It also does no more than C1 downstream.

**Paper triage.** Conceptually illuminating (atomless behavior *is* Ω, made literal), but it presupposes the terminal coalgebra, so it is *less* general than C1, not more. **Reject as the statement; retain "atomless behavior is Ω" as the interpretive gloss** (WS3/WS4 use it: the unique atomless behavior is the single point every import must differ *from*).

### C4 — Equality form (conflates with WS2)

```lean
theorem ws1_atomless_eq {X} (dest) (hbehav : BehaviorallyIdentified dest) (x y)
    (hx : SHNE dest x) (hy : SHNE dest y) : x = y
```
Skip bisimilarity, conclude equality directly (assuming behavioral identity).

- **Failure mode:** **premature.** This is `ws2_static_collapse` — it bakes ingredient (2) into the engine. WS1 must stay at bisimilarity so WS2 can add behavioral identity as a *separate, named* hypothesis (the non-circularity story needs (2) visible as its own ingredient, not hidden in the lemma).

**Paper triage.** True but it is WS2's theorem, not WS1's. **Reject:** keeping the engine at bisimilarity is exactly what lets WS2 exhibit "drop (2) and you keep bisimilarity but lose the collapse" — the ingredient must be separable.

## Winning candidate: C1 (existential-bisimulation), with C3's "behavior is Ω" as gloss

### Definitions and obligations

```lean
namespace Series7.WS1
-- PkObj, PkMap, IsBisim, SHNE, hneRel, hneRel_isBisim, νPk, bisim_eq, omegaState,
-- HereditarilyNonempty, ws2_collapse, Proc, ws1_productive_unique — all transcribed (README §6).

/-- **The engine.** On any plain coalgebra, any two atomless states are related by a
    bisimulation. Weaker than equality (no behavioral identity assumed), hence general. -/
theorem ws1_atomless_bisim {X} (dest : X → PkObj κ X) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y := ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩

/-- **Static instance.** On the terminal coalgebra, behavioral identity turns the engine
    into equality — this is `ws2_collapse`, now a corollary of the general lemma. -/
theorem ws1_recovers_static (hinf : ℵ₀ ≤ κ) (x y : (νPk κ).X)
    (hx : HereditarilyNonempty x) (hy : HereditarilyNonempty y) : x = y

/-- **Dynamic instance.** The productive thread of the process is unique — Series 6's
    `ws1_productive_unique`, transcribed, the SAME idea on the founded approximations. -/
theorem ws1_recovers_dynamic (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : Productive t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht
```

**D1 — the engine.** `ws1_atomless_bisim`. *Strategy:* the term above; `hneRel_isBisim` is transcribed. *Paper-decidable:* yes — it is a proved Series 6 lemma re-exported with the hne hypotheses threaded.

**D2 — the static instance.** `ws1_recovers_static`. *Strategy:* from `ws1_atomless_bisim` on `dest = (νPk κ).dest`, get a bisimulation `R` with `R x y`; `bisim_eq` (behavioral identity on the terminal coalgebra) gives `x = y`. Confirms `ws2_collapse` is a corollary. *Paper-decidable:* yes.

**D3 — the dynamic instance, honestly a parallel not a derivation.** `ws1_recovers_dynamic`. *Strategy:* transcribe `ws1_productive_unique` verbatim. **Honest note (routed to WS3/WS7):** `Proc` is *not* a single plain coalgebra (it is the thread space of the final ω-chain), so the dynamic collapse is **not literally derived** from `ws1_atomless_bisim` — it is proved by its own finite-approximation induction (`allNonempty_unique`). The two are instances of one *idea* (atomless ⇒ unique behavior), proved on two carriers. Whether they are *one theorem* is the WS3 history-bridge question, and the honest default (per the program's recurring pattern) is that they are a **conjunction with a shared idea**, not a single derivation. *Paper-decidable:* the transcription is; the "one theorem or two" is flagged open.

## Outcome classes (per charter §7)

- **Discharged:** D1 (engine), D2 (static instance) — near-certain, both transcribe built proofs.
- **Discharged (transcribed):** D3 as the parallel dynamic instance.
- **Partial (pre-registered, routed to WS3/WS7):** whether the static and dynamic instances are one theorem or two. Honest default: two instances of one idea; the unifying single derivation (if any) is WS3's history-bridge.
- **Strip test:** delete "atomless" (SHNE) from `ws1_atomless_bisim` and the bisimulation `hneRel` has no field — the lemma is not a bare "any relation is a bisimulation" fact; atomlessness is load-bearing.

## Deliverable

`series-7/formal/Series7/ws1.lean`: transcribed carrier + `hneRel`/`hneRel_isBisim`; `ws1_atomless_bisim` (D1), `ws1_recovers_static` (D2), `ws1_recovers_dynamic` (D3). Axiom check: `#print axioms ws1_atomless_bisim` on the standard three (it is `hneRel_isBisim`, already axiom-clean in Series 6).
