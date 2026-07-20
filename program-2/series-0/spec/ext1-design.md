# Charter Extension 1, Design Addendum (WS1 / WS3 / WS5 re-run)

**The design step for the re-run triggered by `charter-extension.md`. It fixes the unified witness and the strengthened signatures that close C1-S1 and C3-S1 as (Fixed). WS2 and WS4 are untouched; `ws3_direction_not_recoverable`, `ws4_*`, `ws5_verdict_*` all stand. This addendum is normative for the re-run; it cites `spec/README.md` §2.1 (imported P1) and adds ONE unified witness.**

## The root cause and the fix

The first build put reification (WS1, on `ℕ`) and the asymmetry (WS3, on `Bool`) on SEPARATE witnesses that share nothing, so reification created nothing that participated (C1-S1) and the passive/active reading was a bare conjunction (C3-S1). The fix (extension R1-R4): ONE witness carrying the self and its reified first other, on which reification CREATES a genuine non-recoverable other and the asymmetry is the self against that other, load-bearing.

## The unified witness (fixed here; ambient for the re-run of WS1/WS3)

Carrier `Fin 3` (monomorphic, `Cardinal.{0}`), three relata:
- `s0` (the self): `attendsU s0 = {s0}` — the self-relation is the self-loop (self attends itself), rank 0.
- `s1` (the reified self-relation, the FIRST OTHER): `attendsU s1 = {s0}` — `s1 = reifyU {s0}` reifies the self-relation and attends the self; rank 1.
- `s2` (the reification iterated): `attendsU s2 = {s1}` — `s2 = reifyU {s1}`; rank 2. (Carries the "the same operation reifies self-to-other relations in turn" proliferation.)

```lean
def attendsU : Fin 3 → Finset (Fin 3) := fun x => if x = s0 then {s0} else if x = s1 then {s0} else {s1}
def rankU    : Fin 3 → ℕ            := fun x => if x = s0 then 0 else if x = s1 then 1 else 2
def reifyU   : Finset (Fin 3) → Fin 3 := fun s => if s = {s0} then s1 else if s = {s1} then s2 else s0
```

The plain relating is the bare out-attention `outDest hinf attendsU` (over which `s0`, `s1` are plain-bisimilar by the imported collapse engine `ws1_atomless_bisim`, both `SHNE`); the labelled structure is the tower-level lift `rankLift (outDest hinf attendsU) rankU` (imported `P1.Reader.rankLift`), whose `plainOf` is the bare relating (`plainOf_rankLift`). The tower level (reification depth) is what the bare relating cannot recover — the mechanism of `P1.Reader.ws2_many_general`.

## The strengthened signatures

### R1 — reification creates the first other (fixes C1-S1)

```lean
theorem ws1_first_other (hinf : ℵ₀ ≤ κ) :   -- κ : Cardinal.{0}
    reifyU {s0} = s1                                    -- reify the self-relation …
  ∧ attendsU (reifyU {s0}) = {s0}                       -- … and it sections it (a real pointwise section)
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0
```

`AttentionDistinguishes … s1 s0`: `s1` (first other) is plain-bisimilar to `s0` (self) over the bare relating yet NOT recoverable (tower-separated). Non-vacuous and PARTICIPATING: `s1` is a relatum the WS3 asymmetry is then stated over (R2). Non-recoverability is the teeth (extension §4): the first other is a MINTED, self-manufactured distinction (Series 13's mint, consistent with Series 07), NOT multiplicity from relating alone — it is non-recoverable precisely because it is a genuine import.

### R3 — the asymmetry over the first other, load-bearing (fixes C3-S1)

Not a bare conjunction. `ws3_passive_constitution` is an IMPLICATION whose directional/reification premises DRIVE the separation:

```lean
theorem ws3_passive_constitution (hinf : ℵ₀ ≤ κ)
    (o : Fin 3) (hreify : reifyU {s0} = o) (hattend : s0 ∈ attendsU o) (hrank : rankU s0 < rankU o) :
    AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) o s0
```

The premises (`o` reifies the self-relation, attends the self, sits at a higher tower level) ENTAIL the label-separation; the proof uses `hrank`/`hattend` (the passivity is load-bearing IN the separation, not conjoined beside it). `ws3_active_passive_distinct` states active (`s1 = reifyU {s0}`, made by what it attends) and passive (`s0 ∈ attendedBy attendsU s1`, made by what attends it) as the two positions occupying the same bare-relating position yet told apart by the reification structure — the separating content IS the directional/reification structure:

```lean
theorem ws3_active_passive_distinct (hinf : ℵ₀ ≤ κ) :
    (s1 = reifyU {s0} ∧ attendsU s1 = {s0})              -- s1 ACTIVE: made by reifying what it attends
  ∧ (s0 ∈ attendedBy attendsU s1 ∧ s1 ∉ attendsU s0)      -- s0 PASSIVE: attended by s1, not attending back
  ∧ AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0
```

`ws3_direction_not_recoverable` (the original Bool-witness `¬ Recoverable (knowLiftD)`) STANDS as the genuine core; it is the general direction-non-recoverability, not the contested passive/active reading.

### R4 — the verdict flag rests on the stronger target

```lean
theorem ws5_flags_justified (hinf : ℵ₀ ≤ κ) :   -- κ : Cardinal.{0}
    (AttentionDistinguishes (rankLift (outDest hinf attendsU) rankU) s1 s0)   -- reif ← ws1_first_other
  ∧ (¬ Recoverable (knowLiftD hinf))                                          -- asym (stands)
  ∧ (∀ {Q} (f : Bool → Q), f true ≠ f false → ¬ ∃ R, IsBisimL (impLift hinf f) R ∧ R true false)  -- imp (stands)
```

The reification flag is now justified by `ws1_first_other`'s separation (the first other genuine), NOT the counting bijection `ws1_reification_exists` (which STAYS as the general "the finite functor admits a section" fact, no longer load-bearing alone). GROUND-ESTABLISHED now depends on the first other being genuine.

## What must NOT change (preserved, extension §4)

- The collapse stays inherited (`ws2_collapse_inherited`), the first other a minted import, not an escape from the One.
- The first other is NON-recoverable (the tower separation), or it has collapsed back into the self.
- No cardinal ceiling (`ws1_bound_is_finite_attention`), the quantified import (`ws4_*`), direction non-recoverability (`ws3_direction_not_recoverable`), the discriminating verdict (`ws5_verdict_*`) all stand.
- Names-not-terms: "the first other," "self," "other," "the mint" are gloss; the theorems name the reified relatum (`s1`), its tower position (`rankU`), and its `¬ Recoverable` / `AttentionDistinguishes` separation.

## Outcome

The verdict stays GROUND-ESTABLISHED only if it now rests on the strengthened flags. If the unified witness resisted (the first other could not be made non-recoverable, or reification would not section the self-relation), OBSTRUCTED / PARTIAL would be reported honestly. C1-S1 and C3-S1 close as **(Fixed)** — the originally intended targets built at strength — not (Relabeled).
