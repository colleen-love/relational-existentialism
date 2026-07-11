# WS3 — Boundlessness without a wall

**Design doc. Series 05. Owns: no object in `W_∞` relates to everything, with the bound *endogenous* — each object's `< κ_α` relating is the grain of its level, and no level is last, so no global cap is imposed. Carries the coincidence duty that on any single level the bound is still the imposed cardinal wall.**

*Standalone. Depends on WS1 (`Tower`, `Winf`, `toColim`, `destInf`, `ws1_local_bound`) and WS2 (`ws2_supremum_walls`, the unbounded-cardinal index). Transcribes the Series 04 no-top cardinal wall `ws4_no_top_cardinal` and `carrier_card_ge` for the coincidence half.*

## The object at stake

Series 04's honest failure (charter §3.2, review S1/S2): on one carrier, "no object relates to everything" is powered by the cardinality fact `#succ x < κ ≤ #carrier` — a *fiat* wall (κ chosen from outside), with faces provably unable to supply the bound (`ws5_contraction_insufficient`). Series 05's claim is that stratification frees the bound: each object still has an honest `< κ_α` local bound, but the *world* `W_∞` has no global cardinal, because for any candidate cap some level overshoots it. The design question is which statement of "endogenous boundlessness" (a) is provable on the WS1 colimit, (b) genuinely differs from the single-carrier cardinal wall (the coincidence duty), and (c) survives the anti-laundering test — that the boundlessness is a fact about *the tower having no last level*, not a relabelled cardinality cap.

**Ambient theory.** WS1's `Winf T` with level-indexed `destInf`; the index `ℤ` (WS2) with cardinals `κ : ℤ → Cardinal` unbounded (`∀ c, ∃ α, c < κ_α`). No monad/distributive law. The key structural fact from WS1 is `ws1_local_bound`: every colimit point has a representative at some level `α` with `< κ_α` successors *there*.

## Candidates for "boundless without a wall"

### B1 — No global cardinal bounds the tower (the honest endogenous form)

```lean
/-- No cardinal caps `W_∞`: for every candidate cap `c`, some level's carrier already
    exceeds it, so `W_∞` is not contained in any single `νLk κ_α`. The bound is real
    at each object (`< κ_α`) and imposed at none (no `c` bounds the tower). -/
theorem ws3_no_global_cap (T : Tower Q) (hunb : ∀ c : Cardinal.{u}, ∃ a, c < (T.lvl a).card) :
    ∀ c : Cardinal.{u}, ∃ (a : T.Idx), c < (T.lvl a).card
```
- **Success condition:** proved from WS2's unbounded-cardinal index directly.
- **Failure mode:** the cardinals turn out set-bounded (a supremum `κ_sup` exists inside the theory) — then `ws2_supremum_walls` fires and `W_∞ ⊆ νLk κ_sup Q`, the tower-with-a-top. This is the §4.1 false repair; failure here means the index was not genuinely cofinal.

**Paper triage.** True and decidable — it is literally the unboundedness hypothesis `hunb` that WS2's index supplies. But *by itself* it is a fact about the **index/cardinals**, not about **objects relating** — so on the anti-laundering test it is a bare cardinal statement. It is necessary (it defeats §4.1) but not sufficient to earn "no object relates to everything by the grain of its level." Keep as a *lemma*; it is not the headline.

### B2 — No object of `W_∞` relates to everything (the no-top payoff on the colimit)

```lean
/-- No colimit object relates to every colimit object. Its representative lives at
    some level α with `< κ_α` successors there; but `W_∞` has objects at every level,
    and levels above α contribute objects α's representative cannot carry (they need a
    higher bound). So no object's `< κ_α` relating can reach the whole tower. -/
theorem ws3_no_top (T : Tower Q) (hunb : ∀ c, ∃ a, c < (T.lvl a).card) (x : Winf T) :
    ¬ ∀ y : Winf T, RelatesInf T x y
```
where `RelatesInf T x y` means `y` (reindexed to `x`'s level) is a successor of `x`'s representative.
- **Success condition:** proved by: `x` has a representative at level `α` with `< κ_α` successors (`ws1_local_bound`); by `hunb` there is a level `β > α` with `κ_β > κ_α`, and `W_β` has `≥ κ_β` objects (transcribed `carrier_card_ge` at level β), more than `x`'s `< κ_α` successors can cover *even after reindexing*, because reindexing up preserves the `< κ_α` count. Hence some object escapes `x`'s relating.
- **Failure mode:** if reindexing an object *up* the tower could increase its successor count to `κ_β`, the local bound would not transport and `x` might relate to everything below β — collapsing B2 to the single-carrier situation. The bound-relaxing connecting maps of WS1 (which relax the *bound* but do not *add edges*) are exactly what forecloses this: `ι` preserves the successor count.

**Paper triage — the crux.** This is the real headline. It is decidable-on-paper: the proof is "local `< κ_α` count (WS1) + a strictly larger level exists (WS2 unbounded) + reindexing preserves count (WS1 `ι` is edge-preserving) ⇒ objects at level β escape." **Crucially, this is *not* the single-carrier cardinal wall:** there is no single κ with `#succ x < κ ≤ #W_∞`; instead the escaping objects are produced by *a higher level that exists because no level is last*. The anti-laundering test: strip "no last level" (i.e. make the index have a greatest element) and B2 *fails* — with a top level `κ_top`, an object there could carry `< κ_top` successors and, if `κ_top ≥ #W_∞`... but `#W_∞ ≥ κ_top` by `carrier_card_ge`, so we are back to the single-carrier cardinal wall. So B2 genuinely *uses* no-last-level. Winner.

### B3 — The bound is the grain: an object's successor count equals its level's grain, not the world's size

```lean
/-- Each object's relating is bounded by its own level's cardinal, and that cardinal
    is the "grain" of the level — the world's size does not enter. Contrast the
    single-carrier wall, where the bound is `#carrier` itself. -/
theorem ws3_bound_is_grain (T : Tower Q) (x : Winf T) :
    ∃ a (y : (T.lvl a).carrier), x = toColim T y ∧
      Cardinal.mk ↥(lstr y).1 < (T.lvl a).card ∧
      ¬ ∃ c : Cardinal, (∀ z, x = toColim T z → Cardinal.mk ↥(lstr z).1 < c) ∧ IsGlobalCapOf T c
```
- **Success condition:** the first conjunct is `ws1_local_bound`; the second says no *global* cardinal is doing the bounding work — the bound is level-local.
- **Failure mode:** if every object's bound could be uniformly capped by one global `c` (the negation of the third conjunct), the tower has an effective supremum and walls. Reduces to B1's failure.

**Paper triage.** This is the "grain, not wall" thesis stated as an object-level property. Decidable but *awkward*: the third conjunct is a negative existential over cardinals whose predicate `IsGlobalCapOf` is essentially B1 restated. It is B1 ∧ B2 repackaged with heavier plumbing. **Trade-off vs B2:** more faithful to the charter's "grain" prose, but no additional mathematical content over B1+B2 and harder to prove cleanly. Hold as an *interpretive corollary* stated after B1+B2, not the primary target.

### B4 — Endogenous via face-counting (the Series 04 dream, retried)

```lean
/-- Attempt: the bound comes from faces, not cardinals — an object cannot face
    everything because facing costs a distinct part of itself per target. -/
theorem ws3_no_top_by_faces (T : Tower Q) (x : Winf T) :
    ¬ ∀ y, RelatesInf T x y   -- proof routed through FacingInjective, NOT carrier_card_ge
```
**Paper triage.** This is precisely what Series 04 **proved impossible on one carrier** (`ws5_contraction_insufficient`, `ws5_quotient_insufficient`: faces tame quality, not branching). Nothing about moving to a tower changes the *within-level* fact that faces do not bound branching. So a face-counting wall is unavailable *at each level*, hence unavailable on the colimit. **Reject — and reject loudly, recording it as the inherited negative.** The Series 05 escape is *not* to make faces bound (they cannot); it is to make the *bound itself* be a between-levels relation (B2). This is the key conceptual correction WS3 must state: Series 05 does not solve Series 04's face-bounding problem, it *dissolves* it by relocating boundlessness from within-a-carrier to between-levels.

## Winner: B2 (no-top on the colimit, powered by no-last-level) with B1 as its feeding lemma and B3 as interpretive corollary; B4 recorded as the inherited impossibility

### The coincidence duty (charter §6, WS3)

The charter demands: re-prove that *on any single level* the bound is still the imposed cardinal wall, so the endogenous boundlessness is earned against the single-carrier fiat.

```lean
/-- **The coincidence theorem.** Boundlessness-without-a-wall is bought *exactly* by
    stratifying. Two halves:
    * **single-level (the fiat, transcribed Series 04):** on any one level `νLk κ_α Q`,
      the only no-top fact is the cardinal wall `#succ x < κ_α ≤ #carrier` — faces
      cannot supply it (`ws5_contraction_insufficient`, inherited);
    * **tower (the endogenous form, B2):** on the colimit, no object relates to
      everything *because no level is last*, with no single κ imposed.
    Same no-top payoff: a fiat wall on one carrier, a between-levels grain on the tower.
    Earned against a standing fiat, not stipulated. -/
theorem ws3_wall_vs_grain (T : Tower Q) (hunb : ∀ c, ∃ a, c < (T.lvl a).card)
    (a : T.Idx) (hinf : ℵ₀ ≤ (T.lvl a).card) :
    -- single-level fiat: the level's own no-top is the cardinal wall
    (∀ x : (T.lvl a).carrier, ¬ ∀ y, y ∈ (lstr x).1)  -- via carrier_card_ge at κ_α
    -- tower grain: colimit no-top powered by unboundedness
  ∧ (∀ x : Winf T, ¬ ∀ y, RelatesInf T x y) :=
  ⟨fun x => ws4_no_top_cardinal_at a x, fun x => ws3_no_top T hunb x⟩
```
This is the exact analogue of Series 04's `ws3_same_succ_diff_face` (collapse-on-`νPk` ∧ split-on-`νLk`): a single statement pairing the standing impossibility with the recovered payoff.

### Definitions and lemmas needed

```lean
namespace Series05.WS3

/-- `x` relates to `y` in the colimit: `y`, reindexed to `x`'s level, is a successor of
    `x`'s representative there. Well-defined on the quotient by `ι_dest` (WS1). -/
def RelatesInf (T : Tower Q) (x y : Winf T) : Prop := ...

/-- Reindexing up the tower preserves the successor count (the connecting maps relax
    the bound, they do not add edges). The load-bearing WS1 fact for B2. -/
theorem reindex_preserves_count (T : Tower Q) {a b} (h : T.le a b) (x : (T.lvl a).carrier) :
    Cardinal.mk ↥(lstr (T.ι h x)).1 = Cardinal.mk ↥(lstr x).1

/-- The single-level no-top wall, transcribed to level α. -/
theorem ws4_no_top_cardinal_at (T : Tower Q) (a : T.Idx) (x : (T.lvl a).carrier) :
    ¬ ∀ y, y ∈ (lstr x).1    -- = carrier_card_ge at κ_α
```

### Proof architecture for B2 (`ws3_no_top`)

1. Take `x : Winf T`; by `ws1_local_bound` fix a representative `y` at level `α`, with `#succ y < κ_α`.
2. By `hunb` (WS2), pick `β` with `κ_β > κ_α`; by transcribed `carrier_card_ge`, `#W_β ≥ κ_β > κ_α`.
3. Suppose for contradiction `x` relates to every colimit object. Then in particular it relates to every object of `W_β` (injected via `toColim`). Reindexing `y` up to level β preserves its count (`reindex_preserves_count`), so `y`-at-β has `< κ_α` successors — but it would need `≥ #W_β ≥ κ_β > κ_α` of them to relate to all of `W_β`. Contradiction.
4. The contradiction is produced by *the existence of level β*, i.e. by no-last-level (`hunb`), not by a single global cap. ∎

**Dependencies on imported upstream theorems.** WS1: `ws1_local_bound`, `ι_inj`, `ι_dest`, `destInf` well-definedness. WS2: `hunb` (unbounded cardinals from the `ℤ` index), `ws2_supremum_walls` (to state why a set-bounded tower would fail). Transcribed Series 04: `carrier_card_ge`, `ws4_no_top_cardinal`, and the negatives `ws5_contraction_insufficient` / `ws5_quotient_insufficient` (for B4's recorded impossibility).

## What counts as failure

- *No genuine unboundedness (§4.1 returns):* if the cardinal assignment has a set-supremum, B1 fails, `ws2_supremum_walls` fires, and the tower walls. Report the boundlessness as fiat-in-the-index.
- *Local bound does not transport:* if reindexing up added edges (`reindex_preserves_count` false), B2 collapses to the single-carrier wall — report no-top as **Relocated (cardinal wall)** exactly as Series 04 did.
- *Anti-laundering failure:* if B2 goes through with the index given a greatest element (no-last-level not load-bearing), then it is the cardinal wall in disguise — report **Partial**, the Series 04 failure relocated up a level. WS7 runs this strip test.

## Outcome classes (per charter §7)

- **Discharged:** B2 + the coincidence `ws3_wall_vs_grain`, with B1 as lemma. Expected, given WS1/WS2 deliver.
- **Impossibility proved (inherited, a success):** B4 — faces cannot bound branching — recorded as the standing negative the tower dissolves rather than solves.
- **Partial:** if the anti-laundering strip test shows no-last-level is not load-bearing in the mechanized B2, report as the relocated Series 04 failure.

## Deliverable

`series-05/formal/ws3.lean`: `RelatesInf`, `reindex_preserves_count`, `ws4_no_top_cardinal_at`, `ws3_no_global_cap` (B1), `ws3_no_top` (B2), `ws3_bound_is_grain` (B3), `ws3_wall_vs_grain` (coincidence), and the transcribed `ws5_contraction_insufficient` re-export recording B4's impossibility. Axiom check owed on `ws3_no_top` and `ws3_wall_vs_grain`.
