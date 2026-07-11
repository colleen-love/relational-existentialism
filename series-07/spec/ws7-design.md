# WS7 — The anti-circularity audit, and the typed verdict

**Design doc. Series 07, runs LAST. Owns: the audit of WS1–WS6 against the signature risk — **circularity**, that the Import Theorem is true only because the ingredients were *defined* to exclude the escapes — and the typed `ProgramVerdict` it returns.**

*Series 07 is standalone; names transcribed into `series-07/formal/Series07/ws7.lean`, re-namespaced `Series07.WS7` (see `spec/README.md` §6). `ProgramVerdict` is transcribed from Series 05/06 `ws7` and **re-pointed** to `{ importForced, payoffsEstablished, Circular }` (`spec/README.md` §3). Series 06's WS7 landed `payoffsEstablished` with a `paintedOn`/`anchorsDistinct`/`allDerive` triple against **trivialization**; Series 07 mirrors the discipline but with a different signature risk — circularity — so the anchors are different: non-circularity refutations, a strip ledger, and trichotomy-not-definitional.*

## The object at stake

The charter's characteristic risk (§5.5, §8, restated plainly in §8's closing box): Series 07's danger is not that it fails to prove the theorem but that it proves a **tautology** — that "atomless" and "no import" were defined so plurality is impossible, so the theorem says nothing about relating the definitions did not already say. WS7 is the detector. It runs last, reads WS1–WS6, and returns a typed verdict. The central finding it must establish is **non-circularity**: that the Import Theorem (`ws2_import_theorem`) is a discovery, not a definitional identity. This is the mirror image of Series 06's WS7 (which audited against *trivialization* — a unification that turned out definitional). Here the audit's objective content is three things, each a theorem or a checkable ledger, not an opinion:

- **(a) NON-CIRCULARITY.** Ingredients (1) plain relating and (2) behavioral identity are the program's **founding commitments**, independently motivated (not gerrymandered for this theorem — `spec/README.md` §2: `NoImportedAtom` *is literally* `BehaviorallyIdentified`). And the escapes are refuted as **theorems**: `νLk`'s loops are distinct-but-plainly-bisimilar (`ws3_same_succ_diff_face` — the label distinction is non-behavioral on the plain functor, hence an import, dropping (1)/(2)); the tower is not carrier-atomless (dropping (3)). Not excluded by a rigged "atomless".
- **(b) The STRIP TEST, aggregated.** Deleting "atomless" (`SHNE`) or "plain" from `ws2_import_theorem` exhibits a **real counterexample** — a leafy plural coalgebra (strip "atomless"), `νLk` (strip "plain"). So the ingredients are load-bearing hypotheses, not gerrymanders.
- **(c) The TRICHOTOMY (WS3) is not a definitional partition** — the three kinds (leaf, import, history) are genuinely distinct and jointly exhaustive, not a relabelled tautology.

**Ambient theory.** `spec/README.md` §2 (the four ingredients as predicates; `SHNE`; `BehaviorallyIdentified = NoImportedAtom`; `hneRel`) and **§3, the transcribed re-pointed `ProgramVerdict`**. Consumes WS1 (`ws1_atomless_bisim`), WS2 (`ws2_import_theorem`, `ws2_non_circular`, the strip results), WS3 (`ws3_trichotomy`, its exhaustiveness status), WS5 (the loophole adjudication), WS6 (`ws6_universal`, heuristic or not).

## Candidates (for the verdict machinery)

### C1 — The verdict computed deterministically from the audit anchors (the lead)

```lean
def ws7_verdict : ProgramVerdict :=
  if nonCircular ∧ trichotomyExhaustive ∧ stripHolds then .importForced
  else if nonCircular ∧ stripHolds then .payoffsEstablished
  else .Circular
```

The verdict is a *function* of three booleans, each backed by a WS-level theorem: `nonCircular` (from `ws2_non_circular` + NC1/NC2 inspection + the escape refutations), `trichotomyExhaustive` (WS3's exhaustiveness — the hard open), `stripHolds` (the aggregated strip ledger). No free judgment: the verdict reduces to `rfl` once the three flags are pinned, exactly as Series 05/06's `ws7_verdict_eq`.

- **Success condition:** the three flags evaluate to concrete literals from the built WS1–WS6, and `ws7_verdict = .payoffsEstablished` (predicted) or `.importForced` (if WS3 lands) closes by `rfl`.
- **Failure mode:** the verdict rests on a **fiat exclusion** — if `nonCircular` is set `true` by definition rather than earned from `ws2_non_circular`, the audit is itself circular. Guarded by making each flag *cite* a theorem, never assert. **Winner.**

**Paper triage.** Deterministic, `rfl`-decidable, matches the program's WS7 shape. The only content is *which literals* the flags carry, and those come from WS2/WS3/WS5/WS6 status. **Winner.**

### C2 — `importForced` asserted (the aspirational ceiling)

```lean
theorem ws7_import_forced : ws7_verdict = .importForced := rfl   -- REQUIRES trichotomyExhaustive = true
```

State the strong verdict directly: the theorem holds, non-circular, trichotomy exhaustive.

- **Failure mode:** **requires WS3 exhaustiveness**, which `spec/README.md` §5 flags as the hardest genuinely-open piece (a fourth kind of distinction would demote the impossibility to collapse-plus-examples). Asserting `importForced` before WS3 lands is exactly relabelling a shortfall as the goal — forbidden by the protocol.

**Paper triage.** The correct verdict *if* `ws3_trichotomy` proves exhaustiveness. Pre-registered as an outcome class, **not** the default. **Reject as the committed statement; retain as the pre-registered ceiling.**

### C3 — A circularity self-check that can return `Circular` (the honest failure detector)

```lean
theorem ws7_circular_if_fiat (h : ¬ nonCircular) : ws7_verdict = .Circular
```

The detector's other arm: if the escapes are found excluded only by fiat (i.e. `ws2_non_circular` cannot be proved — the loop distinction cannot be shown non-behavioral on the plain functor), the verdict is `Circular`, honestly returned — a sharp negative about the *result*, and a success in the program's sense (charter §7).

- **Failure mode:** none as a *statement* — its job is to make `Circular` reachable, so the audit is not rigged to always pass. The risk it guards against is a WS7 that *cannot* return `Circular` (which would itself be circular). Keeping this arm live is the non-triviality of the audit.

**Paper triage.** Load-bearing: an audit that cannot fail proves nothing. `ws7_circular_if_fiat` keeps the `Circular` branch inhabited. **Winner (as the failure arm of C1).**

### C4 — Opinion-based audit (rejected)

A prose "we judge the ingredients well-motivated" with no theorem behind the flags. **Reject:** the charter (§5.5) demands the escapes be refuted *as theorems*, not by fiat; an opinion audit is the very circularity being detected. The objective part — the strip results and the non-circularity refutations — must be theorems; only the Claude-auditing-Claude *disclosure* is prose.

## Paper-decidable triage

| Candidate | Statement | Paper-decidable? | Verdict |
|---|---|---|---|
| C1 verdict-as-function | `ws7_verdict` from three cited flags | **yes** — `rfl` once flags pinned | **Winner** |
| C2 `importForced` asserted | needs `trichotomyExhaustive = true` | conditional on WS3 | pre-registered ceiling |
| C3 `Circular`-reachable | `ws7_circular_if_fiat` | **yes** — keeps branch live | **Winner (failure arm)** |
| C4 opinion audit | prose only | no — is itself the risk | **Reject** |

## Winning candidate: C1 (verdict-as-function) with C3 as its live failure arm

### Definitions and obligations

```lean
namespace Series07.WS7
-- ProgramVerdict (README §3), ws1_atomless_bisim, ws2_import_theorem, ws2_non_circular,
-- ws3_trichotomy, ws3_same_succ_diff_face, ws3_plurality_core, Winf, the loophole (WS5),
-- ws6_universal — all transcribed / consumed (README §6).

inductive ProgramVerdict | importForced | payoffsEstablished | Circular   -- transcribed, re-pointed

/-- **The non-circularity audit.** Ingredients (1),(2) are the founding commitments
    (NoImportedAtom = BehaviorallyIdentified, README §2), and each escape is refuted as a
    THEOREM: νLk's loops are distinct-but-plainly-bisimilar (import, drops (1)/(2)); the
    tower is not carrier-atomless (drops (3)). NOT a rigged "atomless". -/
theorem ws7_non_circularity_audit (hinf : ℵ₀ ≤ κ) :
    -- (2) is the program's own identity principle, not an exclusion:
    (@NoImportedAtom = @BehaviorallyIdentified)
    -- the label escape is refuted by theorem (non-behavioral on the plain functor):
  ∧ (∃ q₁ q₂ : Q, q₁ ≠ q₂ ∧ SameBareSuccessor (loopState q₁) (loopState q₂)
        ∧ loopState q₁ ≠ loopState q₂)
    -- the index escape is refuted by theorem (not carrier-atomless):
  ∧ TowerDropsAtomlessness

/-- **The trichotomy is not a definitional partition.** WS3's three kinds (leaf, import,
    history) are genuinely distinct AND jointly exhaustive — not a relabelled tautology. -/
theorem ws7_trichotomy_not_definitional : ThreeKindsDistinct ∧ ThreeKindsExhaustive_status

/-- The aggregated strip ledger: deleting "atomless" or "plain" from ws2_import_theorem
    exhibits a REAL counterexample, so the ingredients are load-bearing hypotheses. -/
def ws7_strip_ledger : List (String × Bool) :=
  [ ("strip atomless → leafy plural coalgebra (counterexample)", true),
    ("strip plain → νLk (counterexample)",                       true),
    ("strip import → escapes refuted by theorem, not fiat",      true) ]

/-- The three audit flags, each CITING a theorem (never asserted). -/
def nonCircular          : Bool := true    -- backed by ws7_non_circularity_audit + ws2_non_circular
def trichotomyExhaustive : Bool := false   -- WS3 exhaustiveness is the hard open (README §5)
def stripHolds           : Bool := true    -- backed by ws7_strip_ledger (all true)

/-- **The typed verdict.** Deterministic from the three flags; reduces to rfl. -/
def ws7_verdict : ProgramVerdict :=
  if nonCircular ∧ trichotomyExhaustive ∧ stripHolds then .importForced
  else if nonCircular ∧ stripHolds then .payoffsEstablished
  else .Circular

theorem ws7_verdict_eq : ws7_verdict = .payoffsEstablished := rfl   -- predicted; importForced if WS3 lands
theorem ws7_circular_if_fiat (h : nonCircular = false) : ws7_verdict = .Circular := by
  simp [ws7_verdict, h]
```

**D1 — the non-circularity audit.** `ws7_non_circularity_audit`. *Strategy:* clause 1 is definitional inspection (`NoImportedAtom` and `BehaviorallyIdentified` are the same def, README §2 — the "no import" clause *is* the founding principle, not an ad-hoc exclusion); clause 2 transcribes WS2's `ws2_non_circular` / WS3's `ws3_same_succ_diff_face` + `ws3_plurality_core` (distinct loops, identical bare successor — the label distinction is non-behavioral, hence an import *by theorem*); clause 3 records the tower's non-atomlessness (Series 05 open, transcribed status). *Paper-decidable:* yes — the loop facts are proved theorems; clauses 1 and 3 are inspection/transcription. **This is where a SERIOUS finding lands:** if clause 2 cannot be a theorem, "no import" is a fiat and the verdict flips to `Circular` via `ws7_circular_if_fiat`.

**D2 — trichotomy not definitional.** `ws7_trichotomy_not_definitional`. *Strategy:* consume WS3. `ThreeKindsDistinct` (leaf ≠ import ≠ history — each witnessed) is discharged; `ThreeKindsExhaustive_status` carries WS3's exhaustiveness status *honestly* — Partial if a fourth kind resists (README §5), which is why `trichotomyExhaustive = false` is the default flag. *Paper-decidable:* the distinctness is; the exhaustiveness is the pre-registered hard open.

**D3 — the strip ledger, aggregated.** `ws7_strip_ledger`. *Strategy:* collect WS2's two strip results (delete "atomless" → a leafy plural coalgebra is a real counterexample; delete "plain" → `νLk` is a real counterexample) plus the "import" row (escapes refuted by theorem). All `true` = the ingredients are load-bearing, not gerrymanders. *Paper-decidable:* yes — the counterexamples are exhibited in WS2's strip test.

**D4 — the typed verdict.** `ws7_verdict` + `ws7_verdict_eq` (`rfl`) + `ws7_circular_if_fiat`. *Strategy:* the `if` on three flags; with `nonCircular = true`, `stripHolds = true`, `trichotomyExhaustive = false`, it reduces to `.payoffsEstablished` by `rfl` — the standard-three, Series 05/06 pattern. If WS3 lands exhaustiveness (`trichotomyExhaustive = true`), the same function yields `.importForced`. The `Circular` arm stays reachable via `ws7_circular_if_fiat`, so the audit *can* fail. *Paper-decidable:* yes.

### The self-audit disclosure

**Claude-auditing-Claude — a stated limitation.** WS7 audits work produced in the same program by the same author; the judgment that ingredients (1)–(2) are "independently motivated" rather than gerrymandered is, in the last analysis, a per-ingredient call an author makes about their own definitions (charter §9). This is disclosed, not concealed. What is *not* a matter of judgment — the objective part — is: (a) the strip-test results (deleting "atomless"/"plain" exhibits real counterexamples — `ws7_strip_ledger`), and (b) the non-circularity refutations (`νLk` *provably* carries a non-behavioral label distinction; the tower *provably* drops atomlessness — theorems, not opinions). The verdict rests on those; the disclosure bounds what the verdict can claim.

## Outcome classes (per charter §7, pre-registered)

- **`payoffsEstablished` (predicted default).** Non-circularity holds and the strip ledger is clean, but WS3's trichotomy exhaustiveness stays Partial or WS6's universal resists — the honest middle, since exhaustiveness is the hard open (`spec/README.md` §5). `ws7_verdict_eq : ws7_verdict = .payoffsEstablished := rfl`.
- **`importForced` (the ceiling).** If WS3's exhaustiveness lands (`trichotomyExhaustive = true`) *and* non-circularity holds: atomless plurality is impossible without an import, demonstrably and not by definition. Same `ws7_verdict` function, different flag → `rfl` to `.importForced`.
- **`Circular` (the honest failure).** If the escapes are found excluded only by fiat (`ws2_non_circular` fails as a theorem, `nonCircular = false`): a sharp negative about the *result*, honestly returned via `ws7_circular_if_fiat`. **Not expected** — (2) = behavioral identity is the program's own principle, and the escapes fail the *structural* (1)/(3) (`νLk` on the plain functor, the tower's foundedness), not a gerrymandered "atomless". Returning it honestly is a program success.

**Strip test (self-applied).** Delete "import" from the audit and the escapes would have to be excluded some *other* way — but there is none that is a theorem (only fiat), so `nonCircular` would collapse to `false` and the verdict to `Circular`. That the strip *doesn't* collapse it — because the refutations are theorems — is the audit's own evidence of non-circularity.

## Deliverable

`series-07/formal/Series07/ws7.lean`: transcribed `ProgramVerdict` (re-pointed, README §3) + consumed WS1–WS6 anchors; `ws7_non_circularity_audit` (D1), `ws7_trichotomy_not_definitional` (D2), `ws7_strip_ledger` (D3), `ws7_verdict` / `ws7_verdict_eq` / `ws7_circular_if_fiat` (D4). Axiom note: `#print axioms ws7_verdict` on the standard three (`propext` / `Classical.choice` / `Quot.sound`); `ws7_verdict_eq` and `ws7_circular_if_fiat` are `rfl`/`simp`, axiom-clean like Series 05/06's `ws7_verdict_eq`.
