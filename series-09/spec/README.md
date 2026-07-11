# Series 09 — Design Index

**The anchor for the seven design docs. Fixes, once, every decision the workstreams share: the hold-reflexive carrier (the carrier home, settled in WS1 and ambient for all), the hold/restriction primitive (`x↾(x,y)`, holding-first, charter §3), the inspection that makes a hold range over the space of holds (hold-reflexivity), the self-total fixed-point equation, the re-diagonalization map, the single endogenous tower order `≺`, the transcribed Series 08/07/04 machinery, and the two Series-09 discipline rules (the diagonal must be a fixed-point contradiction not a bisimulation; monotonicity refuted-or-proved, never defined-in).**

*Series 09 is standalone. It carries its own copy of every Series 08/07/04 lemma it needs; nothing is imported across series (the closure gate confirms it). The upstream names reproduced (and transcribed verbatim into `series-09/formal/Series09/`, re-namespaced `Series09.WSn`) are listed in §6. Series 09's spine is genuinely new Lean: the hold-reflexive layer (`insp`, `SelfTotal`, `diag`), the diagonal spine (`ws1_no_self_total_hold`), the re-diagonalization map (WS3), and the monotonicity kill condition (WS5) are Series 09 content. What is transcribed is the carrier beneath them (the `P_κ` coalgebra, the hold `x↾(x,y)`, the engine `ws1_atomless_bisim`, the collapse `ws2_import_theorem_static`, the semantic import test, and — as the thing the spine must NOT unfold to — the Series 08 coincidence witness `ws1_symmetric_states_bisimilar`). Designs must be honest about which is which, and above all whether the spine's proof term is a diagonal or a bisimulation.*

---

## 1. The one-paragraph design

Series 08 proved (`ws2_import_theorem_static`) that on a plain `P_κ`-coalgebra, behavioral identity plus every-moment atomlessness forces subsingleton-ness, and its perspective spine came back **Partial** because the positionless collapse provably *coincided* with relational identity (`ws1_symmetric_states_bisimilar`): the distinguisher between two positions presupposed the plurality it was meant to produce. Series 09 keeps the carrier and the hold `x↾(x,y)` but relocates the distinguisher from *between two positions* to *inside one*, and it does so by adding the one primitive Series 08 lacked: **hold-reflexivity**, an inspection `insp : Hold dest → (Hold dest → Prop)` under which a hold's complete content is a predicate over the whole space of holds (not the mere successor point a self-loop affords). On this carrier the **self-total hold** — a hold whose content includes its own complete content — is a fixed point of the self-inspection, and the spine (WS1) is a single negative proved by diagonalization: `insp t t ↔ ¬ insp t t` is a contradiction, so **no hold is self-total** (`ws1_no_self_total_hold`), a Cantor/Lawvere fixed-point denial that references no bisimulation and is therefore *independent of relational identity by construction* — the exact repair Series 08 could not make. From this one fact three consequences follow from ONE position. **Plurality** (WS2): the diagonal residue (`residue insp := fun h => ¬ insp h h`) is distinct from every hold's content and **free** (unrecoverable from the inspection), derived from a single inspection with no second position in the premise — the repair of Series 08's circularity, tied to the Series 04/WS4 semantic import test. **Forced dynamics** (WS3): no self-total hold exists, so self-inspection cannot terminate in a complete self-image; the only coherent alternative is successive re-inspection — the **re-diagonalization map** — which never terminates (seriality), forcing dynamics from one position. **Depth/layering** (WS4): each re-diagonalization resolves a face by opening a new blind spot the prior stage could not see (the diagonal always escapes its enumeration); depth is the length of the re-diagonalization chain, and reachability its trace. The engine of all three is the re-diagonalization map (WS3), on which two obligations are cheap and discharged first — **(NL)** no leaf (the residue is a full unheld face, `SHNE` preserved) and **(NF)** not-a-function — and one is the series' open law, **(MG)** monotone growth of the residue, which WS5 *tests* against a pre-committed kill condition and never bakes into the map.

---

## 2. Ambient theory (shared by all workstreams) — fixed here once

### 2.1 The carrier home beneath the reflexivity (transcribed from Series 08/07; ambient for all)

The underlying relating is Series 08's **plain `P_κ`-coalgebra**, transcribed verbatim. It supplies κ-boundedness (hence consistency: the carrier has models) and the reaching/atomlessness/bisimulation vocabulary the escapes are argued in.

```lean
def PkObj (κ) (X) : Type u := {s : Set X // Cardinal.mk (↥s) < κ}          -- the κ-bounded powerset
-- a plain coalgebra is  dest : X → PkObj κ X
def SReaches (dest) : X → X → Prop := Relation.ReflTransGen (fun a b => b ∈ (dest a).1)
def SHNE (dest) (x) : Prop := ∀ v, SReaches dest x v → (dest v).1 ≠ ∅   -- strong hereditary non-emptiness
def IsBisim (dest) (R) : Prop := …                                       -- the powerset bisimulation
def BehaviorallyIdentified (dest) : Prop := ∀ R, IsBisim dest R → ∀ x y, R x y → x = y
theorem ws1_atomless_bisim (dest) (x y) (hx : SHNE dest x) (hy : SHNE dest y) :
    ∃ R, IsBisim dest R ∧ R x y                                          -- THE ENGINE (Series 08)
theorem ws2_import_theorem_static (dest) (hbehav : BehaviorallyIdentified dest)
    (hatom : ∀ x, SHNE dest x) : Subsingleton X                          -- THE COLLAPSE (Series 08)
```

**This is the home beneath the reflexive layer. No workstream may pick a different one.** The κ-bound on `PkObj` is load-bearing twice over: it is why the carrier is a *consistent object* (not a Russell paradox, charter §5.5), and it is why the diagonal is a genuine *gap* in something real rather than an inconsistency that trivialises everything.

### 2.2 The hold / restriction primitive (holding-first, charter §3; transcribed from Series 08/04)

A **hold** is a directed edge, `x` restricting the relation toward its successor `y` — Series 04's face `x↾(x,y)`, transcribed onto this carrier.

```lean
/-- A hold `x↾(x,y)`: `x` restricting toward its successor `y`. Holding is primitive; reaching is derived. -/
def Hold (dest : X → PkObj κ X) : Type u := { p : X × X // p.2 ∈ (dest p.1).1 }
/-- What the hold affords: the sub-field it turns toward (Series 04's face, forced by `dest` alone). -/
def afford (dest) (h : Hold dest) : Set X := { z | SReaches dest h.1.2 z }
```

`afford` is a *function of `dest`* (forced, not annotated): `ws1_hold_forced` re-proves Series 04's `ws1_face_forced` on this carrier. This is the same primitive Series 08 used; Series 09 does not change it. What Series 09 adds sits *on top* of it (§2.3).

### 2.3 The hold-reflexive layer and the self-total fixed-point equation (WS1 fixes it; ambient for all) — THE SERIES 9 CARRIER DECISION

Series 08's carrier could express a self-*loop* (`dest x ∋ x`, a hold pointing at a point) but not self-*totality* (a hold ranging over the space of holds), which is why its spine could only reach symmetry (coincidence) and never contradiction (independence). Series 09's one new structural ingredient repairs exactly this. A **hold-reflexive carrier** is a Series 08 coalgebra equipped with an **inspection**:

```lean
/-- A content: which holds a hold's complete face contains. A predicate over the WHOLE space of holds —
    not a successor point. This is what a self-loop carrier cannot express. -/
def HoldPred (dest : X → PkObj κ X) : Type u := Hold dest → Prop

/-- **Hold-reflexivity.** An inspection assigns to each hold its complete content: a predicate over the
    space of holds. A hold RANGES OVER HOLDS. This is strictly stronger than a self-loop (§4.4 guard). -/
--  the ambient parameter every WS2–WS6 statement is written against:
variable (insp : Hold dest → HoldPred dest)

/-- The **diagonal residue** of an inspection: the completed judgment about self-holding — the content
    no hold can correctly contain. Cantor/Lawvere's diagonal term, here read as the-me-I-cannot-reach. -/
def diag (insp : Hold dest → HoldPred dest) : HoldPred dest := fun h => ¬ insp h h

/-- **The self-total fixed-point equation.** A hold `t` is self-total iff its content is the completed
    self-inspection: it contains, for every hold, exactly the judgment the complete content demands.
    "A hold whose content includes its own complete content." The equation the diagonal denies. -/
def SelfTotal (insp : Hold dest → HoldPred dest) (t : Hold dest) : Prop :=
  ∀ h, insp t h ↔ diag insp h            -- i.e. insp t = diag insp
```

**The carrier decision, stated once and consumed by WS2–WS6 (protocol §2, first design duty):** the ambient home is the pair `(dest, insp)` — a κ-bounded coalgebra `dest : X → PkObj κ X` plus an inspection `insp : Hold dest → HoldPred dest`. WS1 fixes it; **no two workstreams may assume different homes.** Three properties are load-bearing and each is a WS1 obligation, none assumed:

- **κ-bounded ⇒ consistent (not Russell, §5.5).** `dest` lands in `PkObj κ`, so the carrier is a genuine object with models. The diagonal is a gap *inside* it, not an inconsistency. The unrestricted "a hold ranges over *all* holds as a surjection" is designed in as the **Russell-too-strong** failure mode (`ws1_no_self_total_hold` is precisely why such a surjection has no model), never demanded of the carrier.
- **Hold-reflexive ⇒ strictly stronger than a self-loop (§4.4).** A self-loop inspection has content a *point* (`inspLoop h := fun h' => h' = h`); a hold-reflexive inspection has content a *predicate over holds*. WS1 exhibits a **rich** inspection (surjective onto every content except the diagonal — the genuine gap) so the diagonal is *run*, not vacuously asserted. The self-loop carrier is designed in as the **self-loop-too-weak** failure mode, where the no-self-total result degenerates and the spine silently reduces to Series 08's coincidence.
- **The diagonal is a fixed-point contradiction, not a bisimulation (§4.1, the cardinal check).** The proof of `ws1_no_self_total_hold` is `insp t t ↔ ¬ insp t t → False` — propositional, referencing only `insp`. It mentions no `IsBisim`, no `BehaviorallyIdentified`, no `ws1_symmetric_states_bisimilar`. WS7 certifies this by unfolding the proof term and by a semantic independence witness (the spine holds where relational identity is false and where it is true — orthogonal).

### 2.4 The re-diagonalization map and the ONE endogenous tower order (WS3 fixes it; ambient for WS4, WS5) — THE SERIES 9 ORDER DECISION

Re-diagonalization reopens the gap at a stage that tried to close it: from an inspection, produce the residue it omits and a next-stage inspection that holds that residue (and omits its own).

```lean
/-- Re-diagonalization step: `insp ↝ insp'` — the next inspection HOLDS the prior residue (incorporates
    the blind spot as new content) while, by WS1, carrying a fresh residue of its own. NF (WS3): `insp'`
    is NOT determined by `insp` — many inspections hold a given residue. -/
def ReDiagStep (insp insp' : Hold dest → HoldPred dest) : Prop :=
  (∀ h, diag insp h → insp' (holdOf h) (holdOf h)) ∧ Inspects insp'   -- schematic; WS3 finalises `holdOf`/`Inspects`
/-- **THE TOWER ORDER, derived once.** `m ≺ m'` iff `m'` is reached by a re-diagonalization sequence from
    `m`. Endogenous: the reflexive-transitive closure of `ReDiagStep`, defined from the diagonal operator
    alone — no external stage index. -/
def prec (dest) : (Hold dest → HoldPred dest) → (Hold dest → HoldPred dest) → Prop :=
  Relation.ReflTransGen (ReDiagStep dest)
```

**This is the tower order (protocol §2, second design duty). WS3 (forced dynamics) and WS4 (tower/depth) both consume `prec`; neither may redefine it, and neither may substitute an external `ℕ`-index.** The imported-index branch (`≺` := a stamped stage counter, the Series 03/05 trap) is designed in as a **refuted** failure mode (`ws3_imported_index_refuted`, a cycle witness on which no strict monotone index fits), never a fallback. The **accumulated residue** is measured *separately* from the map (§2.5), so monotonicity stays testable.

### 2.5 The residue measure and the monotonicity discipline (WS5 owns; charter §5.4)

```lean
/-- The accumulated residue along a re-diagonalization chain: the blind spots gathered so far. Measured
    OUTSIDE `ReDiagStep`, so growth is a FACT ABOUT the map, provable or refutable, never a clause inside. -/
def accResidue (dest) (chain) : HoldPred dest := fun h => ∃ insp ∈ chain, diag insp h
```

`accResidue` is defined from the chain and the diagonal operator, **outside** `ReDiagStep`. Monotone growth (MG) is then the *fact* "`accResidue` strictly enlarges along `prec`" — a statement **about** the map, never a clause **inside** it. **The cardinal sin (charter §5.5, protocol §0): a re-diagonalization definition that stamps growth in, so `accResidue` strictly increases by unfolding `ReDiagStep`.** Series 09 forbids this: `ReDiagStep` says only "the next inspection holds the prior residue," which is compatible with the blind spot being *re-inherited unchanged* (no growth). WS5 runs the kill condition — exhibit a re-diagonalization that closes a prior blind spot (net residue non-increasing) — and reports `Refuted` / `Discharged` / `Partial`.

---

## 3. The verdict type (WS7)

```lean
inductive Series09Verdict
  | selfReferenceEstablished  -- spine INDEPENDENT (not Coincident), residue free, dynamics forced, monotonicity SETTLED (D/R/P)
  | coincident                -- the spine's proof unfolds to relational identity / bisimulation (Series 08's wall re-hit)
  | monismStands              -- a self-total hold was constructible OR the carrier was a mere self-loop
  | Circular                  -- residue free-by-fiat, monotonicity baked-in, or carrier Russell-inconsistent — sharp negative
  deriving DecidableEq
```

`selfReferenceEstablished`: WS1 spine discharged AND certified diagonal-not-bisimulation, WS2 residue free and non-circular (one position), WS3 order endogenous and (NL)+(NF) discharged, WS5 monotonicity settled to one of {Discharged, Refuted, Partial} by the kill condition. `coincident`: the Series-09-specific honest failure — the spine holds but its proof routes through `ws1_symmetric_states_bisimilar`-shaped identity, so no-self-total-hold is not the separable second fact (charter §5.5, the sharpest risk; naming it is a first-class outcome). `monismStands`: a self-total hold exists, or the carrier is only self-looping. `Circular`: a WS7 finding (freeness defined-in, monotonicity baked-in, carrier inconsistent). The verdict is a function of a mechanized `Audit` certificate whose every field is a theorem (transcribing Series 07/08's `Audit`/`verdict` pattern), so it cannot be hand-set — and its spine field carries the *diagonal-not-bisimulation* certificate, not merely the spine.

---

## 4. Cross-workstream triage summary

| WS | Owns | Consumes | Delivers | Key risk |
|---|---|---|---|---|
| WS1 | carrier + hold-reflexivity + the diagonal spine | `Hold`/`afford`, κ-bound; contrast with `ws1_symmetric_states_bisimilar` | `ws1_no_self_total_hold`, `ws1_diagonal_not_bisim`, `ws1_holdreflexive_not_selfloop` | the diagonal re-hits Series 08's coincidence (spine unfolds to bisimulation) |
| WS2 | plurality: the residue is free, from one position | WS1 spine + independence, `ws4_free_label_is_import`, `ws4_recoverable_not_import` | `ws2_residue_free`, `ws2_from_one_position`, `ws2_distributed_special_case` | residue recoverable-hence-not-free; second position smuggled in |
| WS3 | re-diagonalization map + endogenous order | WS1 spine (residue always exists), `SHNE` | `ws3_redi_no_leaf` (NL), `ws3_redi_not_function` (NF), `ws3_dynamics_forced`, `ws3_order_endogenous`, `ws3_imported_index_refuted` | order is a painted-on / imported index; NF baked out |
| WS4 | depth = accumulated blind spots; reach as trace | WS3 map + order | `ws4_new_blind_spot`, `ws4_depth_is_tower`, `ws4_reaches_is_trace`; universal Partial | depth is a bare reachability/order fact (strip) |
| WS5 | the monotonicity fork | WS3 map, `accResidue` | `ws5_kill_condition`, `ws5_monotonicity_verdict` (D/R/P) | monotonicity assumed-in-a-definition |
| WS6 | the heuristic ceiling | WS4, WS5, WS1 scope | `ws6_provable_core`, `ws6_universal_theses`, `ws6_monotonicity_retracted` | universal / universal-carrier not rangeable |
| WS7 | diagonal-not-bisimulation + freeness/monotonicity audit + verdict | all | `Series09Verdict`, `ws7_verdict`, the `Audit`, `ws7_coincidence_check` | verdict rests on a coincident spine, or a fiat exclusion |

---

## 5. Predicted headline

WS1's spine is genuinely new Lean and its target is the whole repair: **`ws1_no_self_total_hold` Discharged as an Impossibility proved INDEPENDENT of relational identity** — a Cantor/Lawvere fixed-point contradiction whose proof term contains no bisimulation lemma, certified by WS7's coincidence check. Its *strip test* will show the mathematical content is the bare Cantor fact "no `t` with `∀ h, P t h ↔ ¬ P h h`," with "self-total hold / the-me-I-cannot-reach" as the earned interpretive layer; the design says so, and — unlike Series 08 — surviving the strip *as a fixed-point fact* is exactly what the charter demands (the diagonal SHOULD be Cantor-shaped, §4.1). WS2's residue-freeness discharges from one position (the repair of Series 08's circularity). The genuinely open workstream is WS5's monotonicity kill condition. **Predicted verdict: `selfReferenceEstablished`** with monotonicity **Refuted-in-general, Discharged-on-a-strictly-growing-class (Partial)** — the honest expectation, mirroring Series 08's conservation outcome, is that a re-diagonalization on a periodic/constant carrier re-inherits its blind spot without strict growth (the cycle refutes strict MG), so the "ever-deepening self" is retracted and the bound downgraded to mere non-triviality. `coincident` only if WS1's proof is found to route through bisimulation (the SERIOUS finding the series exists to test, not expected); `monismStands` only if a self-total hold turns out constructible or the carrier is a mere self-loop (the twin carrier hazards, guarded); `Circular` only if the audit finds freeness defined-in or monotonicity baked-in (the two designed guards make it not expected). The one genuine scope hazard (charter §5.3): the spine may be Discharged only relative to an ambient `insp`, with the *universal* "every hold-reflexive carrier admits the diagonal" left a defended thesis (WS6) — which still repairs Series 08, since one non-coincident diagonal is enough.

---

## 6. Transcribed upstream machinery (named, copied verbatim into `series-09/formal/Series09/`)

Re-namespaced `Series09.WSn`, transcribed (not imported), as every prior series transcribed:

- **Carrier + bisimulation (Series 08 `ws1` / Series 07 `ws1`):** `PkObj`, `PkMap`, `toPk`, `SReaches`, `SHNE` (+ `SHNE.ne_empty`, `SHNE.succ`), `IsBisim`, `BehaviorallyIdentified`, `hneRel`, `hneRel_isBisim`, `ws1_atomless_bisim` (**the engine**, the both-atomless bisimulation), `twoLoop` (+ `twoLoop_HNE`, `twoLoop_true_bisim`), `pingPong` (the depth-advancing constant-breadth witness).
- **The collapse (Series 08 `ws1` / Series 07 `ws2`):** `ws1_recovers_static`, `ws2_import_theorem_static` (**the collapse**, `ws2_import_theorem`'s static form).
- **The labelled/face machinery and the semantic import test (Series 08 `ws1` / Series 07 `ws4`):** `LkObj`, `IsBisimL`, `BehaviorallyIdentifiedL`, `plainOf`, `Recoverable`, `labelLoop`, `facedLoop`, `ws4_free_label_is_import` (**the semantic import test**, positive horn), `ws4_recoverable_not_import` (**the semantic import test**, negative horn), `ws4_labelLoop_not_recoverable`, `ws4_facedLoop_recoverable`.
- **The Series 08 coincidence witness — transcribed as the thing the spine must NOT unfold to:** `Symmetric`, `ws1_symmetric_bisim_trivial`, `ws1_symmetric_states_bisimilar` (on a positionless coalgebra any two states are label-bisimilar). Series 09 keeps this in view as the negative touchstone; WS1/WS7 must certify the diagonal proof is *unlike* it.
- **The hold / face primitive (Series 08 `ws1` / Series 04 `ws1`):** `Hold`, `afford`, `ws1_hold_forced` (Series 04's `ws1_face_forced` on this carrier).
- **Verdict (Series 07/08 `ws7`):** the `Audit`/`verdict` certificate pattern, re-pointed to `Series09Verdict` (§3).

Nothing is `import`ed across series; each is copied into the relevant `series-09/formal/Series09/wsN.lean` and re-namespaced, and the closure gate confirms it. The **genuinely new Series 09 Lean** is the hold-reflexive layer (§2.3), the diagonal spine (WS1), the re-diagonalization map and endogenous tower order (WS3), the depth/blind-spot theorems (WS4), and the monotonicity kill condition (WS5).

---

*Design index for Series 09. Read this before any `wsN-design.md`; the shared objects (the carrier `(dest, insp)`, the hold `x↾(x,y)`, the self-total equation, the re-diagonalization map, the ONE order `≺`, the accumulated-residue measure, the verdict) are defined here once and cited. The two discipline rules — the diagonal is a fixed-point contradiction NOT a bisimulation (the coincidence check, promoted to first-class at the spine), and monotonicity is refuted-or-proved never defined-in — are the spine of the review. No em dashes in final academic paper copy; this working design index is not final copy.*
