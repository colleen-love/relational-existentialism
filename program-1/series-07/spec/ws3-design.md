# WS3 — The trichotomy of distinction

**Design doc. Series 07, the theorem's teeth. Owns: the classification that every distinction between two objects of a plain construction is a leaf, an import, or an intensional-history difference; that the third collapses under atomlessness; and — the hardest, genuinely-open piece — that the classification is exhaustive, so no fourth kind of distinguisher can survive the collapse.**

*Series 07 is standalone; names transcribed into `series-07/formal/Series07/ws3.lean`, re-namespaced `Series07.WS3` (see `spec/README.md` §6). Unlike WS1/WS2, this is **not** a reframing of built Series 06 machinery — the collapse of the third kind transcribes `ws1_productive_unique` (README §6), but the trichotomy statement and its exhaustiveness are the genuinely new Lean of the series. The four ingredients, `hneRel`, `ws1_atomless_bisim`, `SHNE`, `BehaviorallyIdentified` are defined in README §2 and cited here, never redefined.*

## The object at stake

WS1 collapses the plain world; WS2 states the four-ingredient impossibility. Both are *collapse* theorems: they show a plain, behaviorally-identified, atomless construction is a subsingleton. What turns a collapse into an **impossibility** (charter §4.4, §5.2) is the claim that there is *nothing else to try* — that any distinguisher one might reach for between two atomless objects is already one of the three refuted kinds. That completeness is WS3's, and it is what the charter names the theorem's teeth: without it the headline degrades from "atomless plurality is impossible" to "here is a collapse, plus four examples of escapes we happened to think of."

The classification (charter §5.2): any distinction between `x y` of a plain construction is
- **(i) a LEAF** — a descent/behavioral difference, a place where relating bottoms out unequally; this *is* an atom, forbidden by ingredient (3) atomlessness (`SHNE`);
- **(ii) an IMPORT** — a coordinate not carried by the relating (a label, index, weight), forbidden by ingredient (1) plain or, equivalently on the plain functor, by (2) behavioral identity (the coordinate is invisible to `dest`, so it violates `BehaviorallyIdentified`);
- **(iii) an INTENSIONAL-HISTORY difference** — a difference in the founded approximation-history; under atomlessness this **collapses** (transcribe Series 06 `ws1_productive_unique`: all atomless histories are Ω's), and otherwise reduces to (i) or (ii).

The design question is how to cash out "any distinction" and "no fourth kind" so that (a) the three kinds are *genuinely distinct* and *jointly exhaustive*, (b) exhaustiveness is **not** obtained by *defining* distinction as the three-way disjunction (the definitional-partition trap, charter §7), and (c) the third kind's collapse discharges to `ws1_productive_unique`. The honest expectation, pre-registered: (a)+(c) are attainable; **(b) — non-fiat exhaustiveness — is the hard open, likely Partial.**

**Ambient theory.** `spec/README.md` §2: `PkObj`/`PkMap`; `IsBisim`; `SHNE`; `hneRel`/`hneRel_isBisim`; `BehaviorallyIdentified` (= `NoImportedAtom`, the same predicate); `ws1_atomless_bisim` (WS1); `Proc`/`allNonempty`/`ws1_productive_unique` (Series 06, transcribed). The **plain functor** `F X = PkObj κ X` and a **distinction relation** `Distinct dest x y : Prop` (a witnessed inequality `x ≠ y` on a plain coalgebra) are the two ambients every candidate must fix.

## Candidates

### C1 — Trichotomy as a genuine classification, each kind independently characterized, exhaustiveness proved (the lead, if attainable)

```lean
-- each kind CHARACTERIZED independently of the others, on the plain functor:
def LeafDiff  {X} (dest : X → PkObj κ X) (x y : X) : Prop :=   -- a descent difference: some
  ∃ path, Reaches dest x path ∧ ¬ SHNE dest (endpoint path)    -- reachable state bottoms out (an atom)
def ImportDiff {X} (dest : X → PkObj κ X) (x y : X) : Prop :=  -- a coordinate invisible to relating:
  (∃ R, IsBisim dest R ∧ R x y) ∧ x ≠ y                        -- bisimilar yet unequal ⇒ not carried
def HistoryDiff {X} (dest : X → PkObj κ X) (x y : X) : Prop := -- differ only in founded history
  SameLimit dest x y ∧ ∃ n, stage n x ≠ stage n y

theorem ws3_trichotomy {X} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y ∨ HistoryDiff dest x y
theorem ws3_trichotomy_exhaustive {X} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) (h : x ≠ y) :
    ¬ LeafDiff dest x y →                       -- atomlessness kills (i)
    (ImportDiff dest x y ∨ HistoryDiff dest x y) -- the residue is forced into (ii) or (iii), NO fourth
```

Each kind is a predicate with its own content — `LeafDiff` names an actual atom by descent, `ImportDiff` names a bisimilar-yet-unequal pair (a `BehaviorallyIdentified` violation, i.e. a coordinate the relating does not carry), `HistoryDiff` names a same-limit stagewise split — and exhaustiveness is a *proved implication*, not the definition of `Distinct`.

- **Ambient `F`:** `PkObj κ`; distinction `x ≠ y`; the classifier is the *disjunction proved of* it, not assumed.
- **Success condition:** `ws3_trichotomy` holds with the three predicates independently defined, and `ws3_trichotomy_exhaustive` shows that ruling out the leaf (atomlessness) forces import-or-history — with import = `BehaviorallyIdentified` failure and history collapsing (C-history below). The residue after removing (i)/(iii) is exactly (ii), and (ii) is refuted by (2).
- **Failure mode:** **the fourth kind.** Exhaustiveness needs "no distinguisher escapes the three predicates." The danger: a pair `x ≠ y` that is not a leaf (both `SHNE`), not import (no bisimulation relates them — genuinely distinct behavior), and not history (same construction, no stages). By `ws1_atomless_bisim` two `SHNE` states *are* related by `hneRel`, so such a pair would make `hneRel` relate unequal states — which is `ImportDiff` by definition. So the fourth kind, *if the carrier is a single plain coalgebra*, is provably empty. The leak is at the seam between carriers (the history dimension), addressed in the strip below.

**Paper triage.** The load-bearing observation: on a **single plain coalgebra**, `ws1_atomless_bisim` makes exhaustiveness a *theorem*, not a partition — any two atomless states are `hneRel`-related, so a non-leaf distinction between them is *necessarily* a bisimilar-yet-unequal pair, i.e. `ImportDiff` (a `BehaviorallyIdentified` violation). This is the non-circular core: exhaustiveness falls out of the engine, not out of the definition of `Distinct`. The residual open is whether `HistoryDiff` is a *third irreducible kind* or itself an `ImportDiff` on the thread-carrier — the "one theorem or two" question WS1/D3 flagged. **Winner for the single-coalgebra trichotomy; exhaustiveness Discharged there, Partial across carriers.**

### C2 — Exhaustiveness by defining distinction as the three-way disjunction (the DEFINITIONAL-PARTITION trap — rejected, named)

```lean
def Distinct {X} (dest) (x y : X) : Prop :=              -- DO NOT DO THIS
  LeafDiff dest x y ∨ ImportDiff dest x y ∨ HistoryDiff dest x y
theorem ws3_trichotomy_trap {X} (dest) (x y) (h : Distinct dest x y) :
    LeafDiff dest x y ∨ ImportDiff dest x y ∨ HistoryDiff dest x y := h   -- vacuous: `id`
```

Make the classification true by fiat: *define* a distinction to be a member of the disjunction, so the trichotomy is `id` and exhaustiveness is definitional.

- **Failure mode:** **the definitional partition — the charter §7 non-circularity violation, named.** The theorem `ws3_trichotomy_trap` is `fun h => h`; it proves nothing about `≠`. It cannot rule out a pair `x ≠ y` for which `Distinct` is *false*, which is exactly the fourth kind it pretends to exclude. Exhaustiveness here is a tautology of the definition, precisely the failure the strip test exists to catch.

**Paper triage.** This is the trap, transcribed so the build cannot drift into it. The discipline: `ws3_trichotomy` must be stated with the *primitive* `x ≠ y` in the hypothesis (as C1) and the disjunction in the *conclusion*, never the reverse. If the only provable exhaustiveness is C2's, the workstream reports **Circular** for exhaustiveness. **Reject; retained as the named anti-pattern WS7 audits against.**

### C3 — Trichotomy via the observational-history-is-universal argument

```lean
-- the observational history = the anamorphism image (behavior); everything ENDOGENOUS
-- to relating is captured by it, and anything beyond it is by definition an import.
def Behavior {X} (dest : X → PkObj κ X) (x : X) : νPk κ := anamorphism dest x
theorem ws3_history_universal {X} (dest) (x y : X) (h : x ≠ y) :
    Behavior dest x ≠ Behavior dest y     -- (i): the difference IS in the behavior (a leaf downstream)
    ∨ Behavior dest x = Behavior dest y    -- (ii): same behavior, unequal ⇒ import (not carried)
```

Cash out exhaustiveness as: the observational history (the behavior = image under the unique morphism to `νPk`) captures *all* endogenous distinction; either two objects differ in behavior (a leaf/descent difference downstream) or they share behavior and are yet unequal — and a difference not visible in the behavior is *by definition* not carried by the relating, hence an import. There is no third place for a distinction to live because "endogenous to relating" *means* "visible in the behavior."

- **Success condition:** the dichotomy `Behavior x ≠ Behavior y ∨ Behavior x = Behavior y` is trivially total, but the *content* is that the second disjunct forces `ImportDiff` (`BehaviorallyIdentified` failure) and the first, under atomlessness, is impossible (`ws1_atomless_bisim`: atomless behaviors coincide, both Ω). So atomless ⇒ second disjunct ⇒ import, cleanly.
- **Failure mode:** **finality smuggled in / history≠behavior.** `Behavior` presupposes the terminal coalgebra (the anamorphism), reintroducing the finality WS1 spent effort dropping; and it conflates *observational* history (behavior in `νPk`) with *intensional* history (the founded approximation thread, `HistoryDiff`), which is exactly the (iii) the process carries. If those two come apart, the "universal" argument covers observational but not intensional distinction — the leak.

**Paper triage.** The *cleanest exhaustiveness argument* — "beyond the behavior is by definition an import" is the charter's own §5.2 justification made literal — but it (a) needs finality and (b) is universal only for *observational* distinction. Intensional history is the residue it does not cover, and that residue is handled only by collapse (C-history), not by universality. **Reject as the sole statement; retain as the interpretive spine of exhaustiveness** (WS7 cites it: "no fourth kind because endogenous = behavioral"), paired with C1's carrier-level proof and the history-collapse below.

### C4 — Collapse-plus-examples, exhaustiveness dropped honestly (the fallback)

```lean
theorem ws3_history_collapses (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : allNonempty t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht   -- (iii) collapses; transcribed
theorem ws3_three_kinds_refuted {X} (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ¬ LeafDiff dest x y ∧ (ImportDiff dest x y → ¬ BehaviorallyIdentified dest)
    -- each of the three named kinds refuted; NO claim they are exhaustive
```

Prove each of the three kinds is refuted (leaf by atomlessness, import by behavioral identity, history by collapse) but make **no** exhaustiveness claim — report the impossibility as "collapse plus three refuted example-classes."

- **Failure mode:** by design, drops the teeth. The impossibility is then "every distinction *we classified* is refuted," silent on a fourth kind. Honest, weaker: demotes the headline to `payoffsEstablished` (charter §5.2: "a fourth kind would demote the impossibility to collapse-plus-examples").

**Paper triage.** The pre-registered honest fallback if C1's exhaustiveness cannot be made non-fiat across carriers. Everything in it is Discharged (the three refutations transcribe built proofs); only the completeness quantifier is surrendered. **Accept as the fallback outcome, not the lead.**

## Paper-decidable triage

| Cand | Statement | Exhaustiveness | Non-circular? | Verdict |
|---|---|---|---|---|
| C1 | trichotomy, kinds independently defined, `≠` in hypothesis | proved on a single coalgebra via `ws1_atomless_bisim`; Partial across carriers | yes — engine gives it, not the definition | **Winner (statement)** |
| C2 | distinction *defined* as the disjunction | definitional (`id`) | **no — fiat partition** | **Reject (named trap)** |
| C3 | history-is-universal (behavior captures all endogenous) | clean, but observational only; needs finality | yes for observational; leaks intensional | **Reject as statement; keep as gloss** |
| C4 | three kinds refuted, no completeness | dropped honestly | n/a | **Fallback outcome** |

## Winning candidate: C1 (independently-characterized trichotomy) built on the engine, with C3 as the exhaustiveness gloss and `ws1_productive_unique` as the history-collapse; C4 the pre-registered fallback

### Definitions and obligations

```lean
namespace Series07.WS3
-- PkObj, IsBisim, SHNE, hneRel, hneRel_isBisim, ws1_atomless_bisim, BehaviorallyIdentified,
-- Proc, allNonempty, omegaProc, ws1_productive_unique — transcribed (README §6). LeafDiff,
-- ImportDiff, HistoryDiff as in C1 (each independently characterized on the PLAIN functor).

/-- **The trichotomy.** Any distinction on a plain coalgebra is a leaf, an import, or a
    history difference. `≠` in the HYPOTHESIS, disjunction in the CONCLUSION — never C2. -/
theorem ws3_trichotomy {X} (dest : X → PkObj κ X) (x y : X) (h : x ≠ y) :
    LeafDiff dest x y ∨ ImportDiff dest x y ∨ HistoryDiff dest x y

/-- **The third kind collapses.** Under atomlessness the intensional history is Ω's —
    transcribes Series 06 `ws1_productive_unique`, so HistoryDiff has no atomless witness. -/
theorem ws3_history_collapses (hinf : ℵ₀ ≤ κ) (t : Proc κ) (ht : allNonempty t) :
    t = omegaProc hinf := ws1_productive_unique hinf t ht

/-- **No fourth kind (the hard one).** For two ATOMLESS states, ruling out the leaf forces
    import or history — the residue after (i) is exactly (ii)∨(iii), by ws1_atomless_bisim. -/
theorem ws3_trichotomy_exhaustive {X} (dest : X → PkObj κ X) (x y : X)
    (hx : SHNE dest x) (hy : SHNE dest y) (h : x ≠ y) (hleaf : ¬ LeafDiff dest x y) :
    ImportDiff dest x y ∨ HistoryDiff dest x y
```

**D1 — the trichotomy.** `ws3_trichotomy`. *Strategy:* case on whether some reachable state from `x` or `y` fails `SHNE` (⇒ `LeafDiff`); else both are hereditarily `SHNE`, so `ws1_atomless_bisim` gives `hneRel dest x y`, and with `x ≠ y` that is `ImportDiff` by definition — unless the pair lives on a thread-carrier with `SameLimit`, which is `HistoryDiff`. *Paper-decidable:* yes for the single-coalgebra split; the `HistoryDiff` disjunct is where the thread-carrier enters. *Strip/coincidence:* the three predicates are **independently defined** (a leaf is a real atom, an import is a real bisimilar-unequal pair, a history diff is a real same-limit stage split) — deleting any one leaves the other two with distinct extensions, so this is a coincidence of three genuine notions, not a partition.

**D2 — history collapses.** `ws3_history_collapses`. *Strategy:* transcribe `ws1_productive_unique` verbatim (README §6); it *is* the statement that every atomless thread is `omegaProc`, so `HistoryDiff` has no atomless witness. *Paper-decidable:* yes — it is a built Series 06 theorem re-exported. *Strip:* delete "atomless" (`allNonempty`) and the uniqueness is false (finite founded stages branch), so atomlessness is load-bearing, not rigged.

**D3 — exhaustiveness, the genuinely-open crux.** `ws3_trichotomy_exhaustive`. *Strategy:* with `¬ LeafDiff` and both `SHNE`, `ws1_atomless_bisim` supplies `hneRel dest x y`; from `x ≠ y` this is `ImportDiff` — **on a single plain coalgebra this is a proof, not a partition** (the engine forces the residue into import). The **open** is the cross-carrier fourth kind: a distinction that is neither a leaf, nor a bisimilar-unequal pair on the given `dest`, nor a same-limit thread split — e.g. a distinction between two *different plain coalgebras* rather than two states of one, which "any construction" (WS6's un-formalizable quantifier) would need but which no single `dest` types. *Paper-decidable:* the single-coalgebra case yes; the cross-carrier universal **no** — it is the same un-rangeable "construction" quantifier WS6 owns. *Strip/coincidence — the load-bearing annotation:* exhaustiveness must come from `ws1_atomless_bisim` (the engine), never from *defining* `Distinct` as the disjunction (C2). The test WS7 runs: does removing the definitional disjunction leave exhaustiveness standing? For the single coalgebra, **yes** (the engine gives it). Across "any construction," **no** — and that gap is reported honestly, not closed by fiat.

## Outcome classes (per charter §7)

- **Discharged:** D1 (`ws3_trichotomy`, single-coalgebra), D2 (`ws3_history_collapses`, transcribed) — both rest on built proofs.
- **Discharged (single coalgebra):** D3 exhaustiveness *on one plain `dest`* — the engine forces non-leaf atomless distinctions into `ImportDiff`, non-circularly.
- **Partial — exhaustiveness open (the pre-registered honest outcome):** the *cross-carrier / any-construction* fourth kind. Exhaustiveness across all constructions is the un-formalizable "construction" quantifier (charter §5.3); reported Partial, routed to WS6 (heuristic ceiling) and WS7 (audit). This is the expected headline for WS3: teeth on one carrier, defended-heuristic across all.
- **Circular (the failure to watch, per charter §7):** if the *only* provable exhaustiveness is C2's — distinction *defined* as the disjunction — then exhaustiveness is a definitional partition and WS3 reports **Circular** for that clause, with the non-fiat proof (via the engine) as the named open. The discipline that keeps this from happening: `≠` in the hypothesis, disjunction in the conclusion; the three predicates independently characterized.
- **Strip test:** delete "atomless" and `ws3_history_collapses` fails (founded stages branch); delete the independent characterization of the three kinds and `ws3_trichotomy` becomes C2 (vacuous). Both deletions break the theorem by exhibiting the trap, which is exactly what non-circularity requires.

## Deliverable

`series-07/formal/Series07/ws3.lean`: transcribed engine (`hneRel`, `hneRel_isBisim`, `ws1_atomless_bisim`) + process (`Proc`, `allNonempty`, `ws1_productive_unique`); `LeafDiff`/`ImportDiff`/`HistoryDiff` independently defined; `ws3_trichotomy` (D1), `ws3_history_collapses` (D2), `ws3_trichotomy_exhaustive` (D3, single-coalgebra Discharged / cross-carrier Partial). The C2 trap is written as a commented anti-pattern so the build cannot drift into it. Axiom check: `#print axioms ws3_history_collapses` reduces to `ws1_productive_unique`'s (the standard three, axiom-clean in Series 06); `#print axioms ws3_trichotomy_exhaustive` must show it consumes `ws1_atomless_bisim`, not a definitional unfolding of `Distinct` — the machine-checkable evidence that exhaustiveness is engine-driven, not fiat.

---

*Design doc for Series 07 WS3. The trichotomy is the theorem's teeth: WS1/WS2 collapse the plain world, WS3 is the claim there is nothing else to try. The three kinds are genuine and independently characterized; exhaustiveness is a theorem on a single plain coalgebra (the engine forces it) and an honest Partial across "any construction" (the un-rangeable quantifier). No em dashes in final academic paper copy; this working design doc is not final copy.*
