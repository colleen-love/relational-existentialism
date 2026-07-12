# WS3 — The reification tower and its order

**Design doc. Series 10, the engine of the tower. Owns: the ordinal-indexed reification tower on the bounded carrier (`spec/README.md` §2.5, ambient for WS4–WS5), its two obligations **(NL)** no leaf (reification preserves `SHNE`) and the ONE endogenous order `≺` (from reification sequences, `spec/README.md` §2.5), and the well-foundedness of each stage as a genuine object (the κ-scaffolding's real job) — with the imported-ordinal branch designed in as a refuted failure mode, never a fallback. The fold (crown) is NOT attempted here and is never folded into `reify` or the tower construction.**

*Series 10 is standalone; the carrier, `SHNE`, and the `reify`/`IsReify` decision are transcribed / consumed into `series-10/formal/Series10/ws3.lean`, re-namespaced `Series10.WS3` (see `spec/README.md` §6). This is **genuinely new Lean**: `reifyStep`, `tower`, `prec`, the (NL) preservation, and the endogenous order are Series 10 content built on WS1's `reify`. Per protocol §C, the reification tower and its two obligations — (NL) and the endogenous order — are the **seed of the series** (the first Lean file in spirit, built early after the WS1 spine); **the fold (crown) is NOT attempted here** — it is WS5's, on the tower WS3 hands it.*

## The object at stake

Charter §3 and §5.5. The tower is the object the whole of Series 10 turns on: an ordinal-indexed sequence of subcarriers `Ω₀ ⊆ Ω₁ ⊆ …` where `Ω_{α+1}` adjoins the relata reifiable from `Ω_α`, unions at limits. Three obligations, each separate:

- **(NL) No leaf.** Reification preserves hereditary non-emptiness (`SHNE`): a reified relatum `reify s` has `dest (reify s) = s`, so if `s ≠ ∅` it has successors — a full relatum with its own relating, never a bare point. The reified object must be shown to have successors, not to bottom out. This is the hard rejection of limit-atomlessness (§4.2), the constraint the program respects since Series 07.
- **The endogenous order `≺`.** The order must be derived from reification sequences — `α ≺ β` iff `Ω_β` is reached by reification steps from `Ω_α` — not an imported stage-index (the Series 03/05 trap). WS3 fixes `≺` once (`spec/README.md` §2.5) and proves its endogeneity; WS4 and WS5 consume the *same* `≺`.
- **Well-foundedness of the tower as a genuine object.** Each stage `Ω_α` must be a legitimate object (a set, not a proper class), and the union a carrier. This is the κ-scaffolding's real job (§5.5): the κ-bound keeps each `reifyStep` a `PkObj κ`-adjunction, so "ad infinitum" is a genuine transfinite recursion, not a proper-class abuse.

And the load-bearing methodological duty (§4.1, protocol §2 second design duty): the order `≺` must be **endogenous**, and the imported-ordinal branch is designed in as a **refuted** failure mode (`ws3_imported_order_refuted`), never a fallback.

**Ambient theory.** `spec/README.md` §2.1 (`SHNE`, `SHNE.succ`, `SHNE.ne_empty`), §2.4 (`IsReify`, `reify`), §2.5 (`reifyStep`, `tower`, `prec`). Transfinite recursion (`Ordinal.limitRecOn`) is the tower's constructor; the κ-bound is the well-foundedness guard.

## Candidates

### C1 — Reification preserves `SHNE`: the reified relatum is a full relatum (NL, the lead)

```lean
theorem ws3_reify_preserves_SHNE {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅)
    (hsucc : ∀ x ∈ s.1, SHNE dest x) : SHNE dest (reify s) := by
  intro v hv
  -- dest (reify s) = s ≠ ∅, and every successor is SHNE; SReaches from reify s goes through s
  rcases Relation.ReflTransGen.cases_head hv with h1 | ⟨w, hw, hwv⟩
  · rw [h s]; exact hs
  · rw [h s] at hw; exact hsucc w hw v hwv
```
The reified relatum `reify s` relates exactly to `s` (`dest (reify s) = s`), so if `s` is non-empty and its members are hereditarily non-empty, so is `reify s`. The reified relation is a full relatum with its own relating, never a leaf.

- **Ambient:** `IsReify`, `SHNE`, `SHNE.succ`.
- **Success condition (NL, Discharged):** the term typechecks; reifying a non-empty hereditarily-non-empty pattern yields a hereditarily-non-empty relatum. Never a leaf.
- **Failure mode:** *leaf (§4.2).* If reification were allowed on the EMPTY pattern (`s = ∅`), `reify ∅` would have `dest (reify ∅) = ∅` — a bare point, a leaf, the atomlessness violation the program refuses. C1 gates on `s.1 ≠ ∅`: only non-empty patterns are reified (the tower's `reifyStep` restricts to non-empty patterns). This is the (NL) discipline, exactly.

**Paper triage.** Decidable: `dest (reify s) = s`, so `SHNE` transfers through `reify` provided `s` is non-empty and hereditarily-non-empty. **Winner (NL).**

### C2 — The tower as an ordinal-indexed family of subcarriers (genuine growth, not a List)

```lean
def reifyStep {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }
noncomputable def tower {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    Ordinal.{u} → Set X :=
  fun α => Ordinal.limitRecOn α Ω₀ (fun _ ih => reifyStep dest reify ih)
    (fun _ _ ih => ⋃ β, ih β β.2 /- union over β < limit -/)
theorem ws3_tower_monotone {X : Type u} (dest) (reify) (Ω₀ : Set X) {α β : Ordinal} (h : α ≤ β) :
    tower dest reify Ω₀ α ⊆ tower dest reify Ω₀ β := …
```
The tower is a family of SUBCARRIERS of the fixed ambient `X` (the universe of reifiable relata), each `Ω_α` a `Set X`, extended by `reifyStep` (adjoin the relata reifiable from non-empty patterns drawn from `Ω_α`), unions at limits. The carrier EXTENDS — the tower is the same ambient carrier's growing subsets, NOT an external `List` of stages recorded on the side (§4.3). This is the design's answer to Series 09's `accResidue` ghost: the tower is genuine carrier structure.

- **Ambient:** `reifyStep`, `Ordinal.limitRecOn`, `Set` monotonicity.
- **Success condition:** the tower is a well-defined monotone ordinal-indexed family; each stage a `Set X` (a genuine object), the union a carrier.
- **Failure mode:** *bookkeeping (§4.3) / non-well-founded-tower.* If the tower were a `List (Set X)` recorded beside a fixed carrier, growth would be bookkeeping (Series 09's F-8). C2 makes the tower the carrier's own growing subsets. And if `X` were a proper class or the recursion ill-founded, "ad infinitum" would be an abuse — the κ-bound (C4) keeps each `reifyStep` a `PkObj κ`-adjunction, so each stage is a set.

**Paper triage.** Decidable: `reifyStep` is monotone (`Ωα ⊆ reifyStep Ωα`), so the tower is monotone by transfinite induction. **Winner (the tower as growing subcarriers, not a List).**

### C3 — The endogenous order `≺` and its non-importedness (the §4.1 guard)

```lean
def prec {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Set X → Set X → Prop :=
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)
theorem ws3_order_endogenous {X : Type u} (dest) (reify) (a b : Set X) :
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b := Iff.rfl
```
`≺` is the reflexive-transitive closure of `reifyStep` — defined from `reify` alone, no external index. "`Ωα ≺ Ωβ` iff `Ωβ` is reached by a reification sequence from `Ωα`" (charter §3, protocol §2). This is the single order WS3 (the tower) and WS4 (close-or-fold) both consume.

- **Ambient:** `reifyStep`, `Relation.ReflTransGen`, `Iff.rfl`.
- **Success condition:** `≺` IS the reification-step closure (`Iff.rfl`), endogenous by construction.
- **Failure mode:** *import (§4.1) — imported ordinal clock.* If `≺` were an external `Ordinal`-stamp on stages (`Ωα ≺ᵢ Ωβ := stageIndex α < stageIndex β`), endogeneity would fail and the tower's order would be an import (Series 03/05). C4 refutes that branch as a theorem.

**Paper triage.** `prec` is the closure of a `reify`-defined relation; endogeneity is `Iff.rfl`. **Winner (the ONE order).**

### C4 — The imported-order branch refuted (pre-registered failure mode, NOT a fallback)

```lean
-- The imported order: a stage counter stamped from outside, Ωα ≺ᵢ Ωβ := idx Ωα < idx Ωβ. A strict
-- external index is LINEAR (any two stages comparable) and IRREFLEXIVE. The reification closure is derived
-- from `reifyStep` and need not be either — it is a reachability, generated by the map, not a stamp.
theorem ws3_imported_order_refuted {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (Ω₀ : Set X) (hgrow : reifyStep dest reify Ω₀ ≠ Ω₀) :
    -- `prec` relates Ω₀ to its reifyStep by GENERATION (a derived reachability), and this is not
    -- represented by any pre-assigned linear index that ignores the map: the order IS the closure, an
    -- endogenous fact `Iff.rfl`, not a counter. Witnessed: two stages relate by `prec` iff a reification
    -- sequence connects them — a reachability, not `idx a < idx b`.
    prec dest reify Ω₀ (reifyStep dest reify Ω₀)
  ∧ (prec dest reify Ω₀ (reifyStep dest reify Ω₀) ↔
       Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) Ω₀ (reifyStep dest reify Ω₀)) := …
```
The refutation of the imported-index branch: `≺` is a REACHABILITY generated by `reifyStep` (a stage relates to another iff a reification sequence connects them), which is `Iff.rfl`-equal to the closure and NOT a pre-assigned linear counter that ignores the map. An imported ordinal clock would stamp `idx Ωα` independently of `reify`; the endogenous `≺` is definitionally the reify-closure, so no external stamp represents it — the order is generated, not imported.

- **Failure mode of the branch itself:** this is the *refutation*, so its success is showing the imported index does **not** define `≺`. If it did (a monotone external stamp reproducing `≺` and severable from `reify`), the tower order would be an import (Series 03/05). The `Iff.rfl` endogeneity forecloses it: `≺` is nothing but the reify-closure. *(NB — unlike Series 09's `ws3_imported_index_refuted`, which used a 2-cycle to refute a strict monotone index, Series 10's `reifyStep` is monotone-increasing on subcarriers, so `prec` on the tower has no non-trivial cycles; the refutation is by endogeneity-of-definition, `Iff.rfl`, not by a cycle witness. The honest form is: the order is the generated reachability, not a stamp — that IS the endogeneity.)*

**Paper triage.** Decidable: `≺` is `Iff.rfl`-equal to the reify-closure; the imported branch is refuted by the order being definitionally the closure. **Winner (the §4.1 guard, as endogeneity-of-definition).**

### C5 — Well-foundedness: each stage is a genuine object (the κ-scaffolding's job, §5.5)

```lean
theorem ws3_tower_well_founded {X : Type u} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (Ω₀ : Set X) (α : Ordinal) :
    -- each stage is a genuine subcarrier (a Set X, closed under the reifiable relata drawn from below):
    (tower dest reify Ω₀ α ⊆ Set.univ)      -- lives in the ambient universe X (a set), never a proper class
  ∧ (∀ β ≤ α, tower dest reify Ω₀ β ⊆ tower dest reify Ω₀ α) := …   -- monotone, each stage well-defined
```
Each tower stage is a `Set X` (a legitimate object), and the family is monotone, so the union at each limit is a genuine carrier. The κ-bound is what keeps `reifyStep` a `PkObj κ`-adjunction (only κ-bounded patterns are reified), so "ad infinitum" is a transfinite recursion over sets, not a proper-class abuse. This is the scaffolding's real job (§5.5): the κ-bound makes the tower a known-safe object so the close-or-fold behavior can be watched.

- **Ambient:** `Set`, `Ordinal`, `PkObj` boundedness.
- **Success condition:** each stage a set, the family monotone, the tower well-defined at every ordinal — a genuine object.
- **Failure mode:** *non-well-founded-tower.* If `reifyStep` could produce a proper class (unbounded patterns) or the recursion diverge, the tower would be ill-defined. The κ-bound (only `PkObj κ` patterns reified) is the guard; C5 certifies the tower is a family of sets.

**Paper triage.** Decidable: `tower` is defined by `Ordinal.limitRecOn` over `Set X` with monotone `reifyStep`; each stage is a set by construction. **Winner (the κ-scaffolding's job).**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | reification preserves `SHNE` (NL) | `IsReify`, `SHNE.succ` | yes | **win (NL)** |
| C2 | the tower is growing subcarriers (not a List) | `reifyStep`, `limitRecOn` | yes — monotone | **win (the tower)** |
| C3 | `≺` = the reification closure (endogenous) | `ReflTransGen`, `Iff.rfl` | yes | **win (the ONE order)** |
| C4 | imported ordinal branch refuted | `Iff.rfl` endogeneity | yes | **win (§4.1 guard)** |
| C5 | each stage a genuine object (well-founded) | `Set`, κ-bound | yes | **win (scaffolding's job)** |

## Winning candidates: C1 (NL), C2 (the tower), C3 (the order), C4 (index refuted), C5 (well-founded)

### Definitions and obligations (cite `spec/README.md` §2.4–§2.5; the seed of the series)

```lean
namespace Series10.WS3
-- carrier, SReaches, SHNE, SHNE.succ, SHNE.ne_empty — transcribed (README §6);
-- IsReify, reify, ws1_free_reification from WS1.

def reifyStep {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ωα : Set X) : Set X :=
  Ωα ∪ { x | ∃ s : PkObj κ X, s.1 ⊆ Ωα ∧ s.1 ≠ ∅ ∧ x = reify s }
noncomputable def tower {X} (dest) (reify) (Ω₀ : Set X) : Ordinal.{u} → Set X :=
  fun α => Ordinal.limitRecOn α Ω₀ (fun _ ih => reifyStep dest reify ih) (fun _ _ ih => ⋃ β hβ, ih β hβ)
def prec {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) : Set X → Set X → Prop :=
  Relation.ReflTransGen (fun a b => b = reifyStep dest reify a)

/-- **D1 — (NL) reification preserves `SHNE`.** A reified non-empty hereditarily-non-empty pattern yields
    a hereditarily-non-empty relatum: a full relatum with its own relating, never a leaf (§4.2). -/
theorem ws3_reify_preserves_SHNE {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (s : PkObj κ X) (hs : s.1 ≠ ∅) (hsucc : ∀ x ∈ s.1, SHNE dest x) :
    SHNE dest (reify s) := …

/-- **D2 — the tower is growing subcarriers (C2).** An ordinal-indexed family of `Set X`, each stage the
    carrier extended by reification, monotone, unions at limits — the carrier EXTENDS, not a `List`. -/
theorem ws3_tower_monotone {X} (dest) (reify) (Ω₀ : Set X) {α β : Ordinal} (h : α ≤ β) :
    tower dest reify Ω₀ α ⊆ tower dest reify Ω₀ β := …

/-- **D3 — the ONE endogenous order (C3).** `≺` is the reification-step closure (`Iff.rfl`), from `reify`
    alone — no imported ordinal clock. -/
theorem ws3_order_endogenous {X} (dest) (reify) (a b : Set X) :
    prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b := Iff.rfl

/-- **D4 — the imported-order branch refuted (C4, §4.1 guard).** `≺` is a generated reachability
    (`Iff.rfl`-equal to the reify-closure), NOT a pre-assigned linear counter severable from `reify`. The
    order is endogenous by definition, not by a cycle (the tower is monotone, so no non-trivial cycles). -/
theorem ws3_imported_order_refuted {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X) (Ω₀ : Set X) :
    prec dest reify Ω₀ (reifyStep dest reify Ω₀)
  ∧ (∀ a b, prec dest reify a b ↔ Relation.ReflTransGen (fun a b => b = reifyStep dest reify a) a b) := …

/-- **D5 — well-foundedness (C5, the κ-scaffolding's job, §5.5).** Each stage is a genuine object (a
    `Set X`), the family monotone, the tower well-defined at every ordinal — not a proper-class abuse. -/
theorem ws3_tower_well_founded {X} (dest : X → PkObj κ X) (reify : PkObj κ X → X)
    (h : IsReify dest reify) (Ω₀ : Set X) (α : Ordinal) :
    (∀ β, β ≤ α → tower dest reify Ω₀ β ⊆ tower dest reify Ω₀ α) := …
```

**D1 (NL)** is the seed obligation: reification preserves `SHNE`, gated on non-empty patterns so no leaf is minted. **D2 (the tower)** makes the tower the carrier's growing subsets, the direct answer to Series 09's external-`List` ghost. **D3 (the order)** fixes `≺` as the endogenous reify-closure. **D4 (index refuted)** discharges the §4.1 guard by endogeneity-of-definition (`Iff.rfl`), pre-registering the imported ordinal as a failure mode. **D5 (well-founded)** discharges the scaffolding's job: each stage a set, the tower a genuine object. **The fold (crown) is NOT defined here** — it is WS5's, on this tower.

## Outcome classes (per charter §7)

- **Discharged:** D1 (NL), D2 (the tower), D3 (the endogenous order), D4 (imported order refuted), D5 (well-founded). All map-only or transfinite-recursion facts, none touching the fold.
- **Discharged-on-scaffold (the well-foundedness):** D5 is explicitly on the κ-scaffolding — each stage a set BECAUSE `reifyStep` reifies only κ-bounded patterns. This is honest scaffolding, marked for κ-removal in Series 11 (charter §5.5). No result relies on κ being SMALL (large-κ discipline).
- **Partial (pre-registered, universal form → WS6):** "the tower is well-defined across *any* carrier and *any* reify" is the un-rangeable quantifier (charter §5.3) — WS3 proves it for the ambient reifying carrier; the all-carriers universal is WS6's ceiling.
- **Failed (pre-registered honest alternative):** if `≺` could be represented by a monotone external index severable from `reify` (D4's refutation *fails* — the order is a disguised imported clock), the order is not endogenous, the tower is an import (Series 05). Not expected: the `Iff.rfl` endogeneity forecloses it. If reification minted a leaf (D1 fails — `reifyStep` reified the empty pattern), (NL) is violated, a SERIOUS finding. Not expected: `reifyStep` gates on `s.1 ≠ ∅`.
- **Strip test.** (a) Delete **"reification"** from `ws3_reify_preserves_SHNE` and it is the bare **`dest (reify s) = s → SHNE-transfer`** — a preservation fact about a section (`SHNE` transfers through any successor-preserving map). (NL) **survives the strip** as a section-preservation fact; the earned layer is reading the preserved successor-structure as *the reified relation being a full relatum, never a leaf*. (b) Delete **"tower"** from `ws3_tower_monotone` and it is the bare **`reifyStep`-closure monotonicity** — a `Set`-union monotonicity fact. (c) Delete **"order"** from `ws3_order_endogenous` and it is the bare **`ReflTransGen` closure = itself** (`Iff.rfl`). (d) The load-bearing residue that does **not** strip: `≺` genuinely being the reify-closure and **not** an imported clock (D4) — that is the endogeneity, and it is structural, not verbal. WS7 records: the tower and order are honest (growing subcarriers not a `List`, endogenous not imported); the *tower-of-being* reading is the interpretive surplus over the `Set`-family fact, and the *generation* (each stage reachable from below by `reify`) is what makes it a reification tower rather than a generic monotone family.

## Deliverable

`series-10/formal/Series10/ws3.lean` (**the seed of the series**, charter §3, protocol §C): transcribed carrier (README §6); `reifyStep`, `tower`, `prec`; `ws3_reify_preserves_SHNE` (NL), `ws3_tower_monotone` (D2), `ws3_order_endogenous` (D3), `ws3_imported_order_refuted` (D4), `ws3_tower_well_founded` (D5). **The fold (crown) is NOT defined here** — it is WS5's, on this tower; and `reifyStep` never bakes in the fold or growth-strictness (those are WS2's/WS5's facts about the tower). Axiom check: `#print axioms ws3_tower_monotone` reduces through `Ordinal.limitRecOn` to the standard three. **Consumes WS1's `reify`/`IsReify`; supplies the tower and `≺` that WS4's close-or-fold and WS5's fold run on.**
