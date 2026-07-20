# WS3, The asymmetry of knowing (THE KNOT, the genuinely-uncertain obligation)

**Design doc. Series 0, the knot. Owns: the KNOWING-LABELLED LIFT `knowLift` (each symmetric neighbor tagged with the knowing bit) and its plain reduct `plainOf_knowLift = symDest`; the passive witness (`a` attends `b`, `b` attends nothing); and the three payoffs: direction NOT recoverable from the symmetric relating (`ws3_direction_not_recoverable`), passive constitution real and LOAD-BEARING (`ws3_passive_constitution`), active and passive genuinely two (`ws3_active_passive_distinct`). The razor: the asymmetry must be a genuine STRUCTURAL distinction, not an inert label laid over the symmetric relating (the Series 11 Bookkeeping failure), and must survive the strip.**

*Series 0 IMPORTS `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `ws1_atomless_bisim` (README §2.1). WS3 DEFINES the knowing-labelled lift (README §2.3) and its witness. The two signature risks are discipline 2 (the asymmetry a bare label: strip passive constitution and the relatum is unchanged, or plain and labelled do the same work) and discipline 3 (direction assumed recoverable/non-recoverable rather than PROVED). Both are foreclosed by making every payoff a `Recoverable`/`AttentionDistinguishes` fact about the genuine coalgebra `knowLift`, mirroring `P1.Reader`'s `ws2_attention_makes_real` / `ws4_labelLoop_not_recoverable`.*

## The object at stake

The charter's WS3 (§2, the knot): seat knowing's directionality as the plain/labelled split — the symmetric relating is the PLAIN structure (`plainOf`, blind to who attends whom), the directed knowing is the LABELLED structure. Prove direction is NOT recoverable from the symmetric relating (so "you attend me and I do not attend you" is a fact the plain relation cannot see); prove PASSIVE constitution real and load-bearing (a relatum attended-but-not-attending whose identity depends on the incoming gaze, distinct from the same relatum in a mutual relation, the directed structure a genuine reader NOT a bare tag); prove active and passive are two. The pre-registered sin (discipline 2, §4.a): if passive constitution strips and the relatum is unchanged, or the plain and labelled structures do the same work, the asymmetry is an inert tag — the exact Series 11 failure.

**Ambient theory.** README §2.1 (imported `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `ws1_atomless_bisim`, `SHNE`), §2.2 (`sym`, `knows`, `attendedBy`), §2.3 (`knowLift`, `plainOf_knowLift`, `AttentionDistinguishes`).

## The witness (fixed here, shared by all three payoffs)

The two-state PASSIVE carrier `DCar := ULift Bool`, `a := ⟨true⟩`, `b := ⟨false⟩`:

```lean
def attendsD : DCar → Finset DCar := fun x => if x = a then {b} else ∅   -- a attends b; b attends nothing
```

- Symmetric relating: `{y | sym attendsD a y} = {b}` (a attends b), `{y | sym attendsD b y} = {a}` (b attended by a). The single undirected edge `a — b`. No self-loops.
- Directed knowing: `a knows b` (`b ∈ attendsD a`), `¬ (b knows a)` (`a ∉ attendsD b = ∅`). So `a` is ACTIVE toward `b`, `b` is PASSIVE (attended-but-not-attending: `a ∈ attendedBy b`, `attends b = ∅`).
- The knowing-labelled lift on the witness: `knowLift a = {(⟨true⟩, b)}` (label = `a knows b` = true), `knowLift b = {(⟨false⟩, a)}` (label = `b knows a` = false). Plain reduct `a ↦ {b}, b ↦ {a}`, the symmetric relating (`plainOf_knowLift`).
- The swap `σ : a ↔ b` is an automorphism of the PLAIN (symmetric) structure but reverses direction, so it is NOT a labelled automorphism — the engine of non-recoverability.

Both `a`, `b` are `SHNE` over `plainOf knowLift` (each reaches only `{a, b}`, all successors nonempty singletons), so `ws1_atomless_bisim` gives the plain bisimulation.

## Candidates (framings of the three payoffs)

### C1, direction non-recoverable, via the plain swap (the lead, discipline 3)

```lean
theorem ws3_direction_not_recoverable (hinf : ℵ₀ ≤ κ) : ¬ Recoverable (knowLiftD hinf)
```

`¬ Recoverable`: SOME plain (symmetric) bisimulation is not a label-bisimulation. Proof mirrors `ws4_labelLoop_not_recoverable`: the constant-`True` relation is a plain bisimulation relating `a, b` (both self-loop plainly through the edge), but no label-bisimulation relates them, because `a`'s outgoing edge carries label `⟨true⟩` and `b`'s carries `⟨false⟩` (`ws4_label_survives_quotient` shape). Direction is a PROOF term, not an assumption (discipline 3).

- **Ambient:** `plainOf_knowLift`, `plainOf_labelLoop_true_bisim` shape, `ws4_label_survives_quotient` shape.
- **Success condition (GROUND):** `¬ Recoverable (knowLiftD hinf)` typechecks; the label separates `a, b` that the plain relation identifies.
- **Failure mode:** *direction assumed (discipline 3).* Foreclosed: the non-recoverability is derived from the label mismatch, not posited. **Winner (audit c).**

### C2, passive constitution load-bearing, via `AttentionDistinguishes` (the lead, discipline 2)

```lean
theorem ws3_passive_constitution (hinf : ℵ₀ ≤ κ) :
    (a ∈ attendedBy attendsD b ∧ attendsD b = ∅)                  -- b is PASSIVE: attended, attends nothing
  ∧ AttentionDistinguishes (knowLiftD hinf) a b                    -- yet plain-bisimilar to the ACTIVE a, label-separated
```

Passive constitution is REAL and LOAD-BEARING: `b` (attended by `a`, attending nothing) is plain-bisimilar to the ACTIVE `a` (they occupy symmetric positions the plain relating cannot tell apart) yet NOT label-bisimilar over `knowLift` — so what makes `b` passive is the directed reader, not the plain relating. `AttentionDistinguishes` (README §2.3, `P1.Reader`) is the load-bearing shape: `(∃ R, IsBisim (plainOf knowLift) R ∧ R a b) ∧ ¬ ∃ R, IsBisimL knowLift R ∧ R a b`. The conjunct `a ∈ attendedBy b ∧ attendsD b = ∅` makes `attendedBy`/`attends` LOAD-BEARING in the statement (a genuine reader, not a bare tag): strip the labelled structure (go plain) and `b` is indistinguishable from `a`, so passive constitution is EXACTLY what the label adds.

- **Ambient:** `AttentionDistinguishes`, `ws1_atomless_bisim`, `ws4_label_survives_quotient` shape.
- **Success condition (GROUND):** typechecks; the passivity conjunct is non-vacuous (`attendsD b = ∅` by `decide`), and the `AttentionDistinguishes` conjunct holds.
- **Failure mode:** *the asymmetry a bare label (discipline 2, SERIOUS).* Foreclosed: `ws3_direction_not_recoverable` PROVES the plain cannot see the direction, so the label does work the plain does not; and `attendedBy`/`attends` are in the statement, so stripping them changes it. **Winner (audit b).**

### C3, active and passive genuinely two (the lead)

```lean
theorem ws3_active_passive_distinct (hinf : ℵ₀ ≤ κ) :
    (attendsD a ≠ attendsD b)                                     -- active a ({b}) ≠ passive b (∅)
  ∧ (∃ R, IsBisim (plainOf (knowLiftD hinf)) R ∧ R a b)           -- yet plain-bisimilar
  ∧ (¬ ∃ R, IsBisimL (knowLiftD hinf) R ∧ R a b)                  -- label-separated: the two modes are two
```

Active constitution (`attends a = {b}`, `a` made by what it reaches) and passive constitution (`attends b = ∅`, `b` made only by what reaches it) yield the SAME plain position (plain-bisimilar) but the directed structure tells them apart. `attendsD a ≠ attendsD b` is the "two modes" content; the plain-bisimilar-yet-label-separated pair is invisibility to `symDest`. So the reaching and the being-reached are two becomings, not one.

- **Success condition (GROUND):** typechecks; `{b} ≠ ∅` by `decide`, the bisim/label-sep conjuncts as in C1/C2.
- **Failure mode:** *the two modes coincide.* Foreclosed: `{b} ≠ ∅`, exhibited. **Winner.**

### C4, the asymmetry as a bare tag on the symmetric relating (the pullback sin, rejected)

```lean
def dirTag (attends) (x : X) : Bool := decide (attends x ≠ ∅)   -- a free label, no reader   -- REJECT
theorem ws3_dir_tag (…) : dirTag ≠ const   -- REJECT: a label that does no structural work
```

Attach a free direction TAG and note it varies. **Reject as the central sin (discipline 2, SERIOUS):** a tag that no bisimulation reads is the Series 11 Bookkeeping failure — `attends` does no work, the reader is inert. The winner C2/C3 make the direction a fact about the GENUINE coalgebra `knowLift` (whose plain reduct IS the symmetric relating), so the label is READ by `IsBisimL` and its non-recoverability is a `Recoverable` theorem, not a tag. **Reject.**

### C5, direction recoverability assumed as a hypothesis (rejected, discipline 3)

```lean
theorem ws3_from_assumed (h : ¬ Recoverable (knowLiftD hinf)) : … := …   -- REJECT: assumes the payoff
```

Take `¬ Recoverable` as a hypothesis and derive the rest. **Reject (discipline 3, SERIOUS):** direction's non-recoverability is the OBLIGATION, not an assumption. C1 proves it. **Reject.**

## Paper-decidable triage

| Cand | What it claims | Ambient | Paper-decidable? | Verdict |
|---|---|---|---|---|
| C1 | `¬ Recoverable knowLift` (direction) | `plainOf_knowLift`, label mismatch | yes, `⟨true⟩ ≠ ⟨false⟩` | **win (audit c)** |
| C2 | passive constitution load-bearing | `AttentionDistinguishes`, `ws1_atomless_bisim` | yes, `attends b = ∅` + bisim/label-sep | **win (audit b)** |
| C3 | active/passive two | `attends a ≠ attends b` + bisim/label-sep | yes, `{b} ≠ ∅` | **win** |
| C4 | asymmetry as a free tag | — | yes, does no work | **reject (Bookkeeping, SERIOUS)** |
| C5 | non-recoverability assumed | — | yes, assumes the payoff | **reject (discipline 3, SERIOUS)** |

## Winning candidates: C1 + C2 + C3 (one witness, three load-bearing payoffs)

### Definitions and obligations (cite README §2.1–§2.3)

```lean
-- attendsD, a, b, knowLiftD, plainOf_knowLiftD                          (the witness, README §2.3 instantiated)
-- ws3_direction_not_recoverable                                        (C1, audit c)
-- ws3_passive_constitution                                             (C2, audit b)
-- ws3_active_passive_distinct                                          (C3)
```

**Proof architecture.** The witness `knowLiftD hinf : DCar → LkObj κ (ULift Bool) DCar` is defined concretely on the finite `DCar` (so `toPk`/`pkSingleton` apply, no `hcar` needed: `DCar` finite ⇒ `mk DCar < ℵ₀ ≤ κ`), with `knowLiftD a = pkSingleton hinf (⟨true⟩, b)`, `knowLiftD b = pkSingleton hinf (⟨false⟩, a)`. The plain-bisimilarity of `a, b` is `ws1_atomless_bisim (plainOf knowLiftD) a b (SHNE a) (SHNE b)` (or the constant-`True` relation, `plainOf_labelLoop_true_bisim` shape); `SHNE` holds because every reachable state has a nonempty singleton successor. The label-separation `¬ ∃ R, IsBisimL knowLiftD R ∧ R a b` mirrors `ws4_label_survives_quotient`: from `R a b`, `a`'s edge `(⟨true⟩, b)` must match an edge of `b` with equal FIRST component, but `b`'s only edge is `(⟨false⟩, a)`, and `⟨true⟩ ≠ ⟨false⟩` (`by decide`). `AttentionDistinguishes` bundles the two. `plainOf_knowLiftD` (the plain reduct is the symmetric relating) is proved by `Set.image_singleton` / `funext`, mirroring `plainOf_labelLoop_val`. **Dependencies:** imported `plainOf`, `Recoverable`, `IsBisim`, `IsBisimL`, `ws1_atomless_bisim`; the general `plainOf_knowLift = symDest` lemma (README §2.3) certifies the label really is over the symmetric relating. **The witness is shared; each payoff adds a distinct load-bearing conjunct, exactly as `P1.Reader` shares `WCar` across `ws2_many_witness` / `ws2_attention_makes_real` / `ws2_reification_loadbearing`.**

## Outcome classes (per charter §5)

- **GROUND (the WS3 payoff):** `ws3_direction_not_recoverable` (direction a proof term, audit c), `ws3_passive_constitution` (a genuine reader, load-bearing, audit b), `ws3_active_passive_distinct` (two becomings).
- **OBSTRUCTED (pre-registered, first-class, the knot's honest terminus):** the asymmetry provably COLLAPSES TO A LABEL — `Recoverable (knowLift …)` holds, the plain and labelled structures do the same work, `attends` does no reading. Then the ground is wrong here, reported with the precise obstruction, and the carrier goes back to the drawing board BEFORE S1 builds the tick on it. **The design says so explicitly: WS3 OBSTRUCTED ⟹ series OBSTRUCTED.**
- **PARTIAL (pre-registered):** the asymmetry lands only per-instance (the single witness, no general `plainOf_knowLift = symDest` reader), so passive constitution is real but not shown structural in general; reported PARTIAL.
- **Strip test.** Delete "knowing / attention / active / passive / gaze" from `ws3_direction_not_recoverable` and it is *"`¬ Recoverable (knowLiftD)`: a plain bisimulation that is not a label-bisimulation"*; from `ws3_passive_constitution`, *"an `attends`-`∅` state is plain-bisimilar (by `ws1_atomless_bisim`) to a non-`∅` state yet not label-bisimilar over `knowLiftD`, `attends`/`attendedBy` load-bearing"* — exactly what the charter says WS3 SHOULD strip to. No name is a term.

## Deliverable

`program-2/series-0/formal/P2S0/ws3.lean`: `import P1`; the general `knowLift`/`plainOf_knowLift` (README §2.3); the witness `attendsD`/`knowLiftD`; `ws3_direction_not_recoverable`, `ws3_passive_constitution`, `ws3_active_passive_distinct`. **WS3 is the knot; OBSTRUCTED (asymmetry a label) is pre-registered and would send the ground back.** Axiom check: `#print axioms ws3_passive_constitution` reduces through `ws1_atomless_bisim` and the finite witness to the standard three. **The asymmetry of knowing is genuine, non-recoverable, and load-bearing, or it is honestly OBSTRUCTED; the razor is discipline 2.**
