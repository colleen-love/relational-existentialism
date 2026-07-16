# Series 07 — Design Index

**The anchor for the seven design docs. Fixes, once, every decision the workstreams share: the four ingredients as Lean predicates, the plain functor and its coalgebras, the general lemma that is the engine, the "construction" abstraction, the limit-atomlessness structure for the loophole, the non-circularity discipline, and the transcribed upstream machinery. `ws1…ws7-design.md` are written against this file; a shared object is defined here and cited, never redefined.**

*Series 07 is standalone. It carries its own copy of every Series 04/05/06 lemma it needs; nothing is imported across series. The upstream names reproduced (and transcribed verbatim into `series-07/formal/Series07/`) are listed in §6. Crucially, much of WS1–WS2 is a **reframing** of already-built Series 06 machinery (§6); the genuinely new Lean is WS3 (the trichotomy), WS5 (the loophole), and WS7 (the circularity audit). Designs must be honest about which is which.*

---

## 1. The one-paragraph design

The charter proves (WS2) that four ingredients are jointly unsatisfiable: (1) **plain relating** (the functor is the unlabelled `P_κ`), (2) **behavioral identity** (an object is its relating — every bisimulation is contained in equality; this is also exactly "no imported atom"), (3) **genuine every-moment atomlessness** (hereditary non-emptiness, at every object and moment), and (4) **plurality**. The engine (WS1) is one lemma, more general than any prior collapse: on *any* plain `P_κ`-coalgebra, all hereditarily-non-empty states are bisimilar — the relation "both atomless" is itself a bisimulation. Behavioral identity turns bisimilarity into equality, so 1∧2∧3 ⇒ ¬4, recovering the static collapse (`ws2_collapse`) and the dynamic collapse (`ws1_productive_unique`) as instances. WS3 makes the impossibility exhaustive (every distinction is a leaf, an import, or a collapsing history); WS4 catalogues the prior imports (weights, labels, levels) as the forced ingredient drops that explain the program; WS5 isolates the one loophole (limit-atomlessness, transient atoms); WS6 draws the heuristic ceiling; WS7 audits against the signature risk — **circularity**, that the theorem is true only because the ingredients were defined to exclude the escapes.

---

## 2. Ambient theory (shared by all workstreams)

**The functor and coalgebras.** `F X = P_κ X`, the κ-bounded powerset functor (Series 04/06 `PkObj`/`PkMap`, transcribed). A **plain coalgebra** is a type `X` with `dest : X → PkObj κ X`. `IsBisim dest R` is the standard powerset bisimulation. The terminal coalgebra is `νPk κ` with `bisim_eq` (behavioral identity holds there).

**The four ingredients, as Lean predicates.** A construction is given by its coalgebra data (`X`, `dest`), and the ingredients are:
```lean
-- (1) plain: dest lands in PkObj κ X — the UNLABELLED functor. Structural: the type has
--     no Q-coordinate. (νLk's functor is P_κ(Q × X); the tower is index-family; both fail (1).)
-- (2) behavioral identity = NO IMPORTED ATOM (they are the SAME condition):
def BehaviorallyIdentified {X} (dest : X → PkObj κ X) : Prop :=
  ∀ R, IsBisim dest R → ∀ x y, R x y → x = y          -- transcribed from Series 06 ws2
abbrev NoImportedAtom := @BehaviorallyIdentified        -- literally the same predicate
-- (3) genuine (every-moment) atomlessness:
def HereditarilyAtomless {X} (dest : X → PkObj κ X) : Prop := ∀ x, SHNE dest x   -- SHNE = strong hered. non-empty
-- (4) plurality:
def Plural {X} : Prop := ∃ x y : X, x ≠ y
```
That **(2) and "no imported atom" are the same predicate** is load-bearing for non-circularity (WS2/WS7): the "no import" clause is not an ad-hoc exclusion, it *is* the program's founding behavioral-identity principle. The escapes then fail a *different*, structural ingredient — (1) plain (νLk, weights, tower carry a coordinate/index) or (3) atomless (tower is locally founded; the metric route is atomless only in the limit).

**The general lemma (WS1, the engine).** Already essentially built in Series 06 `ws2.lean` as `hneRel` + `hneRel_isBisim`:
```lean
def hneRel {X} (dest : X → PkObj κ X) : X → X → Prop := fun x y => SHNE dest x ∧ SHNE dest y
lemma hneRel_isBisim {X} (dest) : IsBisim dest (hneRel dest)      -- transcribed
theorem ws1_atomless_bisim {X} (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y := ⟨hneRel dest, hneRel_isBisim dest, hx, hy⟩
```
WS1 first-classes this as the named engine and derives both instance-collapses from it.

**The construction abstraction.** The theorem is proved (a) for any plain coalgebra (WS1+WS2, covering the *static* case via `BehaviorallyIdentified`), and (b) for the *process* `Proc κ` (transcribed Series 06, covering the *dynamic* case via `ws1_productive_unique`). A single `Construction` structure unifying both is the WS6 heuristic ceiling, not a WS2 obligation — quantifying over "every construction" is exactly the un-formalizable universal.

**The loophole structure (WS5).** Limit-atomlessness: a process whose finite stages carry leaves (`∃ n, ¬ allNonempty n (x.1 n)`) but whose limit is atomless. The behavioral pseudometric / Cauchy-in-an-incomplete-space (Mathlib `Metric`, `CauchySeq`) is the concrete home; the key fact WS5 proves is that any plurality of atomless-in-the-limit processes carries a *finite-stage leaf* distinguishing them (a transient atom), so it relaxes ingredient (3) rather than refuting the theorem.

**Non-circularity discipline (charter §7).** The **non-circularity rule** replaces the coincidence rule: each escape must be refuted as a *theorem* (the construction provably drops a structural ingredient), never excluded by fiat. The **strip test**: delete "atomless"/"plain"/"import" and check the theorem does not silently use a rigged definition.

## 3. The verdict type (WS7)

```lean
inductive ProgramVerdict | importForced | payoffsEstablished | Circular    -- transcribed base, re-pointed
```
`importForced`: the theorem holds, non-circular, trichotomy exhaustive. `payoffsEstablished`: holds with honest scope (trichotomy or universal partial). `Circular`: the escapes only excluded by fiat — a sharp negative, honestly returned.

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk |
|---|---|---|---|---|
| WS1 | the general lemma (atomless behavior unique) | `hneRel_isBisim` (S6), `bisim_eq` | `ws1_atomless_bisim`; both instances | lemma too weak to reach dynamic case |
| WS2 | the Import Theorem + non-circularity | WS1, `Static`/`BehaviorallyIdentified`, `ws1_productive_unique` | `ws2_import_theorem`, `ws2_non_circular` | circular definition of the ingredients |
| WS3 | the trichotomy of distinction | WS1, `ws1_productive_unique` | `ws3_trichotomy`, exhaustiveness | a fourth kind of distinction |
| WS4 | imports catalogued: the program explained | `ws3_plurality_core` (S4), tower `Winf` (S5), weights (S3) | `ws4_*_are_import`, `ws4_program_explained` | a prior plurality that is not an import |
| WS5 | the limit-atomlessness loophole | `Proc`/`allNonempty` (S6), Mathlib metric | `ws5_limit_reintroduces_leaves`, adjudication | the loophole is the real world |
| WS6 | the heuristic ceiling | all | `ws6_provable_core`, `ws6_universal` (heuristic) | universal not formalizable |
| WS7 | the anti-circularity audit + verdict | all | `ProgramVerdict`, `ws7_verdict` | verdict rests on a fiat exclusion |

## 5. Predicted headline

The engine (WS1) and the static+dynamic instances are near-transcriptions of built Series 06 machinery, so they should discharge cleanly. The genuinely open, genuinely new results are the **trichotomy exhaustiveness** (WS3 — the hardest, a fourth kind of distinction would demote the impossibility to collapse-plus-examples) and the **loophole adjudication** (WS5 — whether limit-atomlessness is a real atomless plural world or import-in-time). Predicted verdict: **`importForced`** if the trichotomy lands and the non-circularity holds (ingredients 1–2 are the founding commitments, escapes refuted by theorem); **`payoffsEstablished`** if the trichotomy stays partial or the universal (WS6) resists; **`Circular`** only if the ingredient definitions are found rigged — not expected, since (2) = behavioral identity is the program's own principle and the escapes fail the *structural* (1)/(3), not a gerrymandered "atomless." A sharp negative that counts as success either way: the Import Theorem itself is an Impossibility.

## 6. Transcribed upstream machinery (named, copied verbatim into `series-07/formal/Series07/`)

Re-namespaced `Series07.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation:** `PkObj`, `PkMap`, `Coalg`, `IsBisim`, `bisim_eq`, `νPk` (Series 04 `ws1`/`ws2`, Series 06 `ws1`).
- **The engine (WS1), already built in Series 06 `ws2.lean`:** `SHNE` (strong hereditary non-emptiness), `hneRel`, `hneRel_isBisim`, `BehaviorallyIdentified`, `Static`, `HereditarilyAtomless`, `NoImportedAtom`, `GenuinelyAtomless`, `ws2_static_collapse`, `ws2_escapes_are_imports`.
- **The static instance:** `HereditarilyNonempty`, `ws2_collapse`, `ws2_grounded_core_subsingleton` (Series 04 `ws2`), `ws5_global_groundless_collapses` (Series 04 `ws5`).
- **The dynamic instance:** `Approx`, `trunc`, `Proc`, `allNonempty`, `Productive`, `allNonempty_unique`, `ws1_productive_unique`, `ws1_no_productive_plurality` (Series 06 `ws1`).
- **The imports (WS4):** `νLk`, `loopState`, `ws3_plurality_core`, `ws3_same_succ_diff_face` (Series 04 `ws3` — the label); `Tower`, `Winf` (Series 05 `ws1` — the index); the weight algebra (Series 03, archived — cited, transcribed only if WS4 needs a Lean witness).
- **Verdict:** `ProgramVerdict` (Series 05/06 `ws7`), re-pointed to `{ importForced, payoffsEstablished, Circular }`.

Nothing is `import`ed across series; each is copied into the relevant `series-07/formal/Series07/wsN.lean` and re-namespaced, and the closure gate confirms it.

---

*Design index for Series 07. Read this before any `wsN-design.md`; the shared objects (the four ingredients, `hneRel`, `ws1_atomless_bisim`, the `Construction` ceiling, the loophole structure) are defined here once and cited. No em dashes in final academic paper copy; this working design index is not final copy.*
