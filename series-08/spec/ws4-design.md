# WS4 — Narrowing and depth

**Design doc. Series 08, layering. Owns: reaching-deeper is holding-more-narrowly (breadth falls as depth resolves) on the re-restriction map, and reachability (`SReaches`) as the trace of a narrowing sequence, derived not axiomatic. Discharged on witnesses; the universal form ("all depth is narrowing, across any construction") is a pre-registered Partial (charter §5.3).**

*Series 08 is standalone; names transcribed into `series-08/formal/Series08/ws4.lean`, re-namespaced `Series08.WS4` (see `spec/README.md` §6). WS4 **consumes WS3** (protocol §4): the re-restriction map `ReReStep` and the order `prec` are WS3's, fixed once in `spec/README.md` §2.4; WS4 does not redefine them. The `afford`-inclusion lemma routed here from WS3 (candidate C2) is WS4's depth content.*

## The object at stake

Charter's Consequence 3 (§2, §5.3). The unfolding is *directed*: reaching a deeper relational layer is achieved by holding **more narrowly**, not more broadly — the empirical signature (science resolves the quark by discarding the organism). Depth is the gradient of narrowing. WS4 must make three things theorems on the WS3 map: (a) a re-restriction step **narrows the afforded field** (`afford h' ⊆ afford h`); (b) **depth = the length of the narrowing chain**, and reachability (`SReaches`) is exactly its **trace** — reaching is derived from holds, never axiomatic (charter §3); (c) the honest boundary: on witnesses this is discharged, but "all depth is narrowing across *any* construction" is the un-rangeable quantifier, a pre-registered Partial (like Series 07's trichotomy-exhaustiveness).

The pivot that separates WS4 (narrowing/depth) from WS5 (conservation): WS4 proves the afforded field **shrinks or stays** along `prec` (`⊆`), which is *monotone narrowing*. Whether that shrinkage is **strict** — whether breadth is genuinely *foreclosed* — is NOT WS4's claim; it is the conservation question WS5 owns and tests. WS4 stays at `⊆`; WS5 asks about `⊊` and the breadth cardinal. Keeping this line sharp is what stops WS4 from smuggling conservation (protocol §0.4): WS4's "narrowing" is inclusion of affords, a fact about the map; it does not measure or foreclose breadth.

**Ambient theory.** `spec/README.md` §2.2 (`Hold`, `afford`), §2.4 (`ReReStep`, `prec`, from WS3). The self-loop `twoLoop` (constant afford `{i}`) and a strictly-descending chain (e.g. `omegaState`'s approximations) are the witnesses.

## Candidates

### C1 — A re-restriction step narrows the afforded field (the lead; WS3's C2, landed here)

```lean
theorem ws4_step_narrows {X} (dest : X → PkObj κ X) (h h' : Hold dest)
    (r : ReReStep dest h h') : afford dest h' ⊆ afford dest h
```
The new hold `y↾(y,z)` affords `{w | SReaches dest z w}`, contained in the old hold `x↾(x,y)`'s `{w | SReaches dest y w}` because `z` is a one-step successor of `y` (`ReflTransGen.head`). Narrowing is literal set-inclusion.

- **Ambient:** `afford`; `ReReStep`; `Relation.ReflTransGen.head`.
- **Success condition:** the term typechecks — every re-restriction step affords a sub-field.
- **Failure mode:** *painted-on-order / conservation-assumed.* If "narrows" were stated as strict `⊊`, it would (i) be false on the self-loop (constant afford) and (ii) smuggle foreclosure (WS5's job). C1 stays at `⊆` — true everywhere, and *not* a conservation claim.

**Paper triage.** Decidable: `SReaches dest y ⊇ SReaches dest z` by `ReflTransGen.head` on the edge `y → z`. **Winner (depth-as-narrowing, in the honest `⊆` form).**

### C2 — Depth = chain length; reachability is the trace (the lead for "reach derived")

```lean
theorem ws4_reaches_is_trace {X} (dest : X → PkObj κ X) (x z : X) :
    SReaches dest x z ↔ ∃ (h : Hold dest) (h' : Hold dest),
      h.1.1 = x ∧ prec dest h h' ∧ h'.1.1 = z ∨ z = x       -- reach = a narrowing sequence's trace (or reflexive)
```
`SReaches dest x z` holds iff there is a re-restriction sequence (`prec`) from a hold at `x` to a hold at `z`: reaching is the *trace* of narrowing, derived, not an axiom (charter §3, holding-first).

- **Failure mode:** *reach re-introduced as primitive.* If the ↔ failed in the forward direction (a reach with no hold-sequence), holding-first would break. It does not: every `SReaches` step `a → b` lifts to a `ReReStep` between holds (pick any onward edge), and `prec`'s projection is `SReaches` (WS3's `ws3_prec_is_reach`). The reflexive disjunct handles `z = x` (no edge needed). Fiddly at the base case (a hold at `x` needs `x` to have a successor); stated with the reflexive escape hatch.

**Paper triage.** The forward map (reach ⇒ hold-sequence) needs `x` to have an outgoing edge to *start* a hold; on `SHNE` carriers this always holds (`SHNE.ne_empty`). Decidable with the `SHNE` hypothesis threaded, or with the reflexive disjunct. **Winner (reach-as-trace), with the `SHNE`/reflexive guard flagged.**

### C3 — Breadth falls: the strict-narrowing witness (bridges to WS5, does NOT claim conservation)

```lean
theorem ws4_depth_forecloses_witness (hinf : ℵ₀ ≤ κ) :
    ∃ {X} (dest : X → PkObj κ X) (h h' : Hold dest),
      ReReStep dest h h' ∧ afford dest h' ⊊ afford dest h        -- SOME step strictly narrows (breadth falls)
```
Exhibit *one* construction where a step strictly narrows — the empirical signature (resolving deeper discards siblings). This is the *existence* of foreclosure, not its universality.

- **Failure mode:** *mistaken for conservation.* This witnesses that narrowing *can* forecloses breadth; it does NOT claim *every* step does (that is conservation, WS5, and is expected to fail). Kept as a witness that the phenomenon is real, explicitly scoped away from the universal.

**Paper triage.** Decidable: a two-level tree where `y` has siblings that `z` lacks gives `afford h' ⊊ afford h`. **Winner (the witness that depth-narrowing is inhabited), scoped strictly away from conservation.**

### C4 — The universal form: all depth is narrowing (pre-registered Partial)

```lean
-- ws4_all_depth_is_narrowing : ∀ (construction) (deeper-than relation), deeper ⇒ narrower
theorem ws4_universal_narrowing_partial : True   -- placeholder: the un-rangeable quantifier
```
The charter-strength claim quantifies over *every* construction and *every* notion of "deeper" — the un-rangeable universal (charter §5.3).

- **Failure mode:** *over-claim.* Stating it as a theorem would require quantifying over all coalgebras and depth-notions. **Reject as a theorem; deliver as a defended thesis floored by C1+C2+C3, routed to WS6.**

**Paper triage.** Not paper-decidable at the universal (matches Series 07 WS3 exhaustiveness). **Partial, routed to WS6.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | a step narrows the afforded field (`⊆`) | `ReflTransGen.head` | yes | **win (depth-as-narrowing)** |
| C2 | reach = trace of a narrowing sequence | `ws3_prec_is_reach`, `SHNE.ne_empty` | yes (with `SHNE`/reflexive guard) | **win (reach derived)** |
| C3 | SOME step strictly narrows (foreclosure exists) | two-level tree witness | yes | **win (witness, scoped)** |
| C4 | ALL depth is narrowing (any construction) | un-rangeable | no | Partial → WS6 |

## Winning candidates: C1 (narrowing), C2 (reach-as-trace), C3 (foreclosure witness); C4 Partial → WS6

### Definitions and obligations (cite `spec/README.md` §2; consume WS3)

```lean
namespace Series08.WS4
-- carrier, SReaches, SHNE, ReflTransGen machinery, twoLoop — transcribed (README §6);
-- Hold, afford from WS1; ReReStep, prec, ws3_prec_is_reach from WS3.

/-- **D1 — a step narrows (C1).** Every re-restriction affords a sub-field: reaching deeper is holding
    more narrowly. Stated at `⊆` (honest); strictness is WS5's conservation question, NOT claimed here. -/
theorem ws4_step_narrows (dest : X → PkObj κ X) (h h' : Hold dest)
    (r : ReReStep dest h h') : afford dest h' ⊆ afford dest h := by
  intro w hw
  -- afford h' = {w | SReaches dest h'.1.2 w}; afford h = {w | SReaches dest h.1.2 w}
  -- h'.1.1 = h.1.2 (r.1) and h'.1.2 ∈ (dest h'.1.1).1 (r.2): so h.1.2 → h'.1.2 is an edge
  have hedge : h'.1.2 ∈ (dest h.1.2).1 := by rw [← r.1]; exact r.2
  exact Relation.ReflTransGen.head hedge hw

/-- **D2 — depth is narrowing along the whole chain.** `prec` (a narrowing sequence) affords a
    sub-field: `afford` is antitone along `≺`. The monotone-narrowing law. -/
theorem ws4_depth_is_narrowing (dest : X → PkObj κ X) (h h' : Hold dest)
    (hp : prec dest h h') : afford dest h' ⊆ afford dest h := by
  induction hp with
  | refl => exact subset_rfl
  | tail _ hstep ih => exact (ws4_step_narrows dest _ _ hstep).trans ih

/-- **D3 — reachability is the trace of a narrowing sequence (C2).** `SReaches` projects out of `prec`
    (WS3), and every reach lifts to a hold-sequence: reaching is DERIVED from holding, not axiomatic. -/
theorem ws4_reaches_is_trace (dest : X → PkObj κ X) (h h' : Hold dest) (hp : prec dest h h') :
    SReaches dest h.1.1 h'.1.1 := ws3_prec_is_reach dest h h' hp   -- the trace direction (cited from WS3)

/-- **D4 — foreclosure is inhabited (C3), scoped away from conservation.** SOME re-restriction strictly
    narrows: the empirical signature is real. This does NOT claim every step forecloses (that is WS5). -/
theorem ws4_depth_forecloses_witness (hinf : ℵ₀ ≤ κ) :
    ∃ {X : Type u} (dest : X → PkObj κ X) (h h' : Hold dest),
      ReReStep dest h h' ∧ afford dest h' ⊊ afford dest h := …   -- two-level tree: y has a sibling z lacks
```

**D1/D2 (narrowing)** are the depth law at `⊆` — antitone `afford` along `≺` — proved by `ReflTransGen` induction over `ws4_step_narrows`. **D3 (reach-as-trace)** cites WS3's `ws3_prec_is_reach`: reaching is the trace of narrowing, holding-first honored. **D4 (foreclosure witness)** shows strict narrowing *happens* without claiming it *always* happens — the bridge to WS5, scoped explicitly away from conservation so WS4 does not smuggle it.

## Outcome classes (per charter §7)

- **Discharged:** D1 (step narrows), D2 (depth is narrowing, antitone `afford`), D3 (reach-as-trace, cited from WS3), D4 (foreclosure inhabited).
- **Partial (pre-registered, routed to WS6):** C4, "all depth is narrowing across any construction" — the un-rangeable quantifier (charter §5.3), a defended thesis floored by D1–D4, exactly Series 07's trichotomy-exhaustiveness pattern.
- **Failed (pre-registered honest alternative):** if a re-restriction step were found that *broadens* the afforded field (`afford h' ⊄ afford h`), depth-as-narrowing would fail. Not possible: `ReReStep` follows an edge, so `afford h' ⊆ afford h` always (D1). The direction of narrowing is forced by the carrier, not chosen.
- **Strip test.** Delete **"narrowing"** from `ws4_depth_is_narrowing` and it is the bare **`afford` antitone along `SReaches`** — a reachability/inclusion fact (`ReflTransGen` monotonicity). Delete **"depth/trace"** from `ws4_reaches_is_trace` and it is the bare **`prec` projects onto `SReaches`** (WS3). Both payoffs **survive the strip** as reachability facts; the earned layer is reading `⊆`-antitone-afford as *holding-more-narrowly-to-resolve-deeper* and the chain length as *depth*. WS4 flags this honestly: the mathematics is monotone reachability; the *layering* is the interpretation. The residue that does **not** strip — that reaching is *derived* from holds (D3), not primitive — is the genuine holding-first content.

## Deliverable

`series-08/formal/Series08/ws4.lean`: transcribed carrier (README §6); `ws4_step_narrows` (D1), `ws4_depth_is_narrowing` (D2), `ws4_reaches_is_trace` (D3), `ws4_depth_forecloses_witness` (D4). **Consumes WS3's `ReReStep`/`prec`/`ws3_prec_is_reach`**; does not redefine the order. The universal (C4) is routed to WS6. Axiom check: `#print axioms ws4_depth_is_narrowing` reduces through `ReflTransGen.head` to the standard three.
