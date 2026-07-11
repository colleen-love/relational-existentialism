# Series 8 — Blind Whole-Series Adversarial Review (Phase D)

**Reviewer:** Claude (Claude-reviewing-Claude; not independent — the stated program limitation).
**Branch:** `claude/series-8-setup-cleanup-xgo4df`.
**Scope:** All of `series-8/formal/Series8/` (ws1–ws7, `Series8.lean`, `AxiomCheck.lean`), read against `charter.md`, the seven `spec/wsNN-design.md`, `charter-status.md`, `protocol.md` §0.3–0.5.
**Method:** Source-level unfolding only. The build was **not** run (per instruction). Every claim below is checked by reading the actual Lean terms, not by trusting the prose or the status ledger.

---

## Snapshot verdict

The build is genuinely `sorry`-free and declares no custom `axiom` (grep-confirmed: the only hits for `sorry`/`axiom` are in comment strings). The mathematics that is present is real and correctly typed as far as source inspection goes. The honest ledger (`charter-status.md`) and the designs pre-flag most of the interpretive gaps candidly — this is a disciplined build, not a smuggled one.

The two SERIOUS checks the protocol names as the sharpest (Spinozist retreat §0.5, conservation-by-fiat §0.4) come out **split**: conservation-by-fiat is **clean** (a genuine success), but the Spinozist retreat is **not fully closed as a theorem** — the god's-eye node is collapsed only *under the hypothesis that it is `Recoverable`*, and the one concrete witness that `Recoverable` is inhabited is a degenerate single-face node, not an all-faces totality. That is one SERIOUS finding. Everything else is REAL (correctly-labelled gaps) or COSMETIC.

| Check | Owning WS | Result |
|---|---|---|
| Spinozist retreat (§0.5) | WS1 | **SERIOUS** — collapse is hypothetical-on-`Recoverable`; witness is one-face, not all-faces |
| Conservation-by-fiat (§0.4) | WS3/WS5 | **CLEAN** — foreclosure not in the map; kill condition run; verdict Partial, honest |
| Kill-condition depth-opening witness | WS5 | **REAL** — only the self-loop `h→h` built; the depth-advancing constant-branching witness designed but absent |
| Verdict is a function of the audit | WS7 | **REAL** — `verdict` is a constant function; ignores its certificate |
| Strip test on every payoff | WS1–WS5 | **ACCEPTABLE** — all flagged surviving payoffs are honestly disclosed in the designs |
| Freeness verdict (monism-broken) | WS2 | **CLEAN** (leans on the WS1 gap — see laundering) |
| Endogenous order | WS3 | **CLEAN** |
| No-leaf (NL) | WS3 | **CLEAN** |
| Axiom-check actually run | AxiomCheck | **REAL** — the `.lean` exists but the log is a static transcript; not re-verified here |

---

## SERIOUS findings

### S1 — WS1: the no-god's-eye theorem collapses a *hypothesis*, not the *all-faces node*. The Spinozist retreat is not fully closed as a theorem.

**What the charter/protocol demand (§0.5, §5.5).** The all-faces (god's-eye) node must be *proved* bisimilar to the trivial self-loop and hence collapsed **by the engine**, not asserted positionless or excluded by a definitional clause. "Holds all faces symmetrically" must be *literally* `Recoverable`, and that must be shown, not stipulated.

**What the code delivers.** `ws1_no_gods_eye` (ws1.lean:290) is:

```
(hrec : Recoverable dest) (hbehav : BehaviorallyIdentifiedL dest)
(hatom : ∀ x, SHNE (plainOf dest) x) → Subsingleton X
```

This is `ws4_recoverable_atomless_collapses` re-named. It proves: *if* a labelled coalgebra is recoverable, behaviorally identified, and atomless, *then* it is a subsingleton. `Recoverable` is a **hypothesis**, not a proved property of a god's-eye node. The theorem never establishes that the node "holding all faces symmetrically" *is* recoverable. It says "any recoverable such node collapses."

**Why this is the retreat smuggled, in the precise sense of §0.5.** The load-bearing bridge — "symmetric / all-faces ⟹ `Recoverable`" — is supplied by the *one concrete witness* `facedLoop` (ws1.lean:248), proved `Recoverable` by `ws1_symmetric_hold_recoverable`. But `facedLoop` has label type `Q = ULift Unit` — a **one-element** face space carrying the single constant label `()`. It is recoverable *because* it distinguishes nothing: a node with exactly one trivial face. That is not "holds all faces symmetrically"; it is "holds one face." The monist's actual claim — the totality is relationally identified *because* it hosts a rich plurality of faces symmetrically — is never instantiated. The node with a genuinely plural, symmetric face space is neither built nor proved recoverable. So the collapse bites only on a node that was already trivial, and the Spinozist's fat totality slips between "`Recoverable` (hypothesis)" and "the one-face witness."

The design doc is honest that this is the risk (ws1-design.md C1 failure mode, and the strip note: delete "face" and the spine *is* bare `ws4_recoverable_atomless_collapses`). But honesty in the margin does not discharge the theorem. As it stands, monism's escape hatch — "the totality is recoverable-and-therefore-identified, so it exists and is the One containing all faces" — is left formally open while `Series8.lean`'s prose says the all-faces node "collapses to the One by the engine."

**Correction owed (no goalpost-moving).** *Prove that*, for a face space `Q` with |Q| ≥ 2 carrying genuinely distinct labels symmetrically, either (a) the symmetric all-faces node **is** `Recoverable` (closing symmetric ⟹ recoverable as a theorem, so the collapse lands on the real totality), or (b) it is **not** recoverable — in which case it is *free*, does *not* collapse, and **monism wins on the totality**, which must be reported as Failed for the spine per charter §8.1. Alternatively, build the charter's literal C3 form (`ws1_gods_eye_bisim_trivial` on the coproduct carrier) so "all-faces node bisimilar to the trivial self-loop" is an actual cross-carrier bisimulation, not a re-reading of a `Recoverable` hypothesis. Until one of these lands, relabel the headline: it is **"recoverable god's-eye nodes collapse,"** not **"no god's-eye node exists."**

---

## REAL findings (genuine gaps, correctly labelled once fixed — none sink the series)

### R1 — WS5: the kill condition fires on a self-loop `h→h`, not on a depth-*advancing* witness.

The charter §5.4 kill condition demands *"a re-restriction that opens depth without foreclosing breadth."* `ws5_kill_condition` (ws5.lean:54) supplies `⟨h, h, ⟨rfl, hmem⟩, lt_irrefl _, …⟩` on `twoLoop`: source and target are the **same hold**. It is a genuine `ReReStep` on a genuinely atomless field (`twoLoop_HNE`), and it genuinely forecloses no breadth. But because `h' = h`, depth does not actually advance — the "opening" is a cycle back to the same hold. The design (ws5-design.md §17, C3) pre-registered the stronger, correct witness: a **constant-branching tree** (breadth `b → b` while depth genuinely descends). That witness is **not built** (grep: no `tree`/`branch` in ws5.lean; the WS4 `treeStep` is a different, foreclosing witness and lives in ws4.lean).

This does not overturn the verdict: strict conservation is still genuinely false (`ws5_strict_refuted` via `lt_irrefl` on breadth 1 < 1 is independently valid), and Partial is honestly labelled. But the *kill condition as the charter phrased it* ("opens depth") is only witnessed at the degenerate depth-zero step.

**Correction owed.** *Build the constant-branching witness* (a `dest` with fixed branching `b ≥ 2` at every node, a re-restriction `h → h'` with `h' ≠ h` descending one level, and `breadth h' = breadth h`) and route it into `ws5_kill_condition` so the depth genuinely advances. Cheap and paper-decidable. Until then, note in the ledger that the kill condition is witnessed *at a self-loop*, and the depth-advancing form is owed.

### R2 — WS7: `verdict` is a constant function; it does not read its certificate.

`verdict` (ws7.lean:59) is `fun _cert _settled => .perspectiveEstablished`. Both arguments are ignored. Consequently `ws7_audited_not_monism` / `ws7_audited_not_circular` are proved by `decide` on the enum (`perspectiveEstablished ≠ monismStands`) — facts about three distinct constructors, **not** facts about the audit. The genuine anti-hand-setting content lives entirely in the `Audit` **structure** (ws7.lean:35): its five fields are real theorems (`spineCollapses`, `freenessTheorem`, `orderEndogenous`, `noLeaf`, `conservationTested`), so you cannot *construct* an `Audit` without discharging them, and `ws7_audit` does discharge them. That part is sound. But the claim in the doc-comment that "the verdict is a function of it [and] cannot be hand-set" overstates: the verdict *selection* is hand-set to a constant; only the *existence of a certificate* is earned.

**Correction owed.** *Relabel* the WS7 prose: the audit certificate is load-bearing and honest; the verdict-selector is a constant tag on a discharged certificate, not a decision procedure over it. Or *prove that*: make `verdict` actually branch (e.g. return `monismStands` when a `Recoverable`-and-plural node is exhibited, `Circular` when a definitional-exclusion flag is set), so the three-way type is inhabited by a real function of the audit contents rather than a constant. This is a labelling/strengthening item, not a soundness hole — `ws7_audit` genuinely holds.

### R3 — Axiom check is a static transcript, not a re-verified run here.

`AxiomCheck.lean` contains the 29 `#print axioms` commands and would, on a build, print the dependency sets. `spec/axiom-check-log.md` records `[propext, Classical.choice, Quot.sound]` for all 29. I did **not** run `lake build` (per instruction), so I cannot independently confirm the printout matches the log. The source contains no `sorry`/`admit`/custom `axiom` (grep-confirmed), which is consistent with the claim. But the log is a committed artifact from a prior run, not a live result. Per §0.6/the protocol's own standard, "was `#print axioms` actually run" is answered: *the command file exists and is wired into the build; the log is asserted from a 2026-07-11 build; not re-verified in this review.*

**Correction owed.** *Run it* in the Phase E code session (`lake build Series8 Series8.AxiomCheck`) and confirm the live printout equals the log, citing the commit hash — the log itself asks for exactly this.

---

## Per-check ledger (the questions asked, answered plainly)

**Spinozist-retreat check (§0.5).** See **S1**. The all-faces node is *not* proved bisimilar to the trivial loop; it is collapsed under a `Recoverable` hypothesis whose only inhabited witness is a one-face node. Neither "proved-collapsed" nor "excluded-by-clause" cleanly — it is "collapsed-if-recoverable, recoverability-witnessed-only-degenerately." **SERIOUS.**

**Conservation-by-fiat check (§0.4).** **CLEAN.** Unfolding `ReReStep` (ws3.lean:34): `fun h h' => h'.1.1 = h.1.2 ∧ h'.1.2 ∈ (dest h'.1.1).1`. It follows the edge (new source = old target; new target a valid successor) and touches **no sibling/breadth set**. `breadth` (ws5.lean:29) is defined separately as `Cardinal.mk (↥(dest h.1.2).1)` — a fact about `dest`, measured outside the map. So "breadth is conserved" is a *tested* property of the map, refutable by witness, not a clause inside it. **Conservation is NOT baked in.** The kill condition *was* run (`ws5_kill_condition`, `ws5_strict_refuted`) and produced **Refuted (strict) / Partial (verdict)** — see R1 for the one caveat on the witness's depth.

**Strip test (§0.3).** Every payoff strips exactly as the designs pre-flag, and each surviving residue is honestly disclosed:
- Delete "perspective" from plurality (`ws2_perspective_breaks_merge`) → bare `ws4_free_label_is_import` (a free-label / plain-bisimilar-but-not-label-bisimilar fact). Survives. **Flagged, disclosed.**
- Delete "narrowing" from depth (`ws4_depth_is_narrowing`) → bare `afford` antitone along `ReflTransGen`, i.e. a reachability-inclusion fact (`ReflTransGen.head`). Survives. **Flagged, disclosed** — but note this residue is a *genuine map fact*, which is what keeps WS5 honest (see laundering).
- Delete "re-restriction" from forced-dynamics (`ws3_dynamics_forced`) → bare `SHNE`-seriality (every atomless state has an atomless successor). Survives. **Flagged, disclosed.**
- Delete "face" from the no-god's-eye collapse (`ws1_no_gods_eye`) → bare `ws4_recoverable_atomless_collapses` (recoverable+atomless+behav-id ⟹ subsingleton). Survives. **Flagged** — and this is exactly the surface S1 exploits: the mathematical content is Series 7's engine; "god's-eye / all faces" is interpretive layer.
- Delete "hold" from the bound (`ws5_kill_condition`) → bare breadth-constancy (`lt_irrefl` on a constant cardinal). Survives. **Flagged, disclosed.**

None of these is a *hidden* strip — the ledger in `charter-status.md` and every design's strip-test section name them. Verdict: **ACCEPTABLE**, because the perspectival readings are declared as earned surplus, not passed off as new bisimulation content. The one that becomes SERIOUS is the "face" strip, not because the strip is hidden but because the un-stripped `Recoverable` hypothesis (S1) is never discharged on a real totality.

**Freeness verdict (WS2).** The code delivers **monism-broken** (`ws2_monism_broken`, ws2.lean:49): `¬ Recoverable (labelLoop)` ∧ plain-bisimilar ∧ not-label-bisimilar. This is a genuine free-label import (the Series 4/WS4 semantic test: `ws4_free_label_is_import`), not a defined-in freeness — `labelLoop` carries each node's own identity as its label, and freeness is proved (`ws4_labelLoop_not_recoverable`), not stipulated. **CLEAN as a standalone.** Its dependency on WS1 is the laundering item L1.

**Endogenous-order verdict (WS3).** `prec := ReflTransGen ReReStep` (ws3.lean:39) — derived from `dest` alone, **not** an imported stage-index. The §4.2 guard `ws3_imported_index_refuted` (ws3.lean:83) exhibits a genuine self-loop step `ReReStep h h` on `twoLoop`, so `≺` cycles and no strict monotone external counter represents it. The signature correction (from the unrealizable `h ≠ h'` to the self-loop step) is logged in `charter-status.md` and is a faithful fix, not a retarget. Forced dynamics (`ws3_dynamics_forced`) is a **theorem** (SHNE-seriality: every atomless hold has an atomless-target successor), not an intuition between definitions. **CLEAN.**

**No-leaf verdict (WS3).** `ws3_rerestriction_no_leaf` (ws3.lean:46): from an SHNE hold there is always a next re-restriction whose source is again SHNE. Re-restriction preserves SHNE and never empties a node. No transient bare relatum anywhere in the map. **CLEAN** — the constraint Series 8 exists to respect is honored.

**Cross-workstream laundering.**
- **L1 (WS2 ⟵ WS1 freeness).** WS2's plurality leans on perspective being free. WS2 proves freeness *directly* for `labelLoop` (`ws4_labelLoop_not_recoverable`), so it does **not** launder through the open S1 hypothesis — the *local* freeness of the directed hold is a theorem. What WS2 does *not* need, and correctly does not claim, is the *global* freeness (no-totality) that S1 leaves open. So WS2 is clean **provided its claim is read as "these two holds don't merge,"** not "no totality recovers all holds." The `charter-status.md` result-tracker row for WS2 ("freeness is a theorem") is accurate for the local fact. **No laundering, but see the scope note.**
- **L2 (WS5 ⟵ WS3 order endogenous).** WS5's conservation test runs along `ReReStep`/`prec`; those are genuinely endogenous (WS3 clean). No laundering.
- **L3 (WS4 ⟵ WS3 genuinely narrowing).** WS4's depth leans on re-restriction genuinely narrowing. `ws4_step_narrows` derives `afford h' ⊆ afford h` from the `ReReStep` edge (a real fact), not from a definitional narrowing clause. No laundering.

**Coincidence rule.**
- **WS1 no-god's-eye vs. relational identity.** The "forced" spine `ws1_no_gods_eye` unfolds *definitionally* to `ws4_recoverable_atomless_collapses` → `ws2_import_theorem_static` (the relational-identity collapse). It is **not independent** of its definitional partner: strip "face" and it *is* the collapse. This is the coincidence-rule failure that underlies S1 — the "no god's-eye node" theorem is the recoverable-collapse theorem wearing a hat.
- **WS3 forced-dynamics vs. finitude.** `ws3_dynamics_forced` unfolds to the same construction as `ws3_rerestriction_no_leaf` (both pick a successor `z` via `SHNE.ne_empty`). They coincide — forced-dynamics *is* iterated no-leaf. This is acknowledged in the design ("(NL) sharpened to seriality") and is acceptable: the seriality reading is the earned layer, and the theorem is genuinely SHNE-seriality. Independent enough — the extra content is `hs.succ hz` (target stays atomless). **Passes.**
- **WS5 conservation vs. re-restriction.** Conservation is measured *outside* `ReReStep` (the whole point of §0.4). Its refutation (`ws5_kill_condition`) is independent of the map definition — it is a fact about `breadth` on `twoLoop`. **Passes** (modulo R1's witness caveat).

**Conservation verdict, stated plainly.** The code delivers **Partial** (`ws5_conservation_verdict = .partialV`, ws5.lean:75), justified by `ws5_verdict_justified`: strict conservation **Refuted** (`ws5_strict_refuted`) + kill condition fires (`ws5_kill_condition`), weak conservation **Discharged on a non-increasing class** (`ws5_conserves_if_nonincreasing`, hypothesis on `dest`, not on the map). It is one of {Discharged, Refuted, Partial}, honestly labelled, and the "self-limiting universe" is explicitly retracted (`ws6_conservation_retracted`). **This is a first-class honest outcome, exactly as pre-registered.** Never assumed-and-unstated. (R1 is the only blemish: the depth-advancing witness is owed.)

**Axiom-check status.** See R3. Command file present and wired; log asserted from a prior build; not re-verified here; source is `sorry`/`axiom`-free.

---

## What survives cleanly

- **The engine, transcribed and correct.** `hneRel_isBisim`, `ws1_atomless_bisim`, `ws2_import_theorem_static`, `ws4_recoverable_atomless_collapses` are faithfully re-namespaced and typecheck as written. The Series 7 collapse is intact.
- **Conservation is genuinely open and genuinely settled by test, not fiat.** The single sharpest methodological risk of the series (§0.4, "the cardinal sin") is **avoided**: foreclosure is nowhere in `ReReStep`; `breadth` is external; the kill condition runs and produces an honest Partial with the strong law retracted. This is the series' cleanest win.
- **The endogenous order.** `≺` is the re-restriction closure, cycles on the self-loop, and is provably not a strict external index. The Series 5 trap is escaped by theorem.
- **No-leaf (NL).** SHNE preserved everywhere; the limit-atomlessness rejection is honored with no transient bare relatum.
- **Narrowing as a real map fact.** `ws4_step_narrows` is a genuine `afford`-inclusion from the edge, so WS4's depth and WS5's conservation are not built on a fake narrowing.
- **Plurality (local).** Two directed holds of a shared relation genuinely fail to merge, via a proved free label — monism-broken at the level of the pair.
- **Honesty of the ledger.** `charter-status.md` and the designs pre-flag every strip residue and the WS3 signature fix. Nothing SERIOUS was found *hidden*; S1 is a gap the designs half-admit but do not close.

---

## Honest bottom line

Series 8 is a disciplined build whose bound-side risk (conservation-by-fiat) is cleanly avoided and whose central open law is honestly settled as a Refuted-in-general / Partial verdict — a real, first-class outcome, not a smuggled success. The engine, the endogenous order, no-leaf, and the local plurality all survive scrutiny.

The one SERIOUS finding is on the positive side, exactly where the protocol warned it would be sharpest: **the no-god's-eye spine is proved only as "recoverable god's-eye nodes collapse," with the bridge from "all faces symmetrically" to "`Recoverable`" witnessed only by a degenerate one-face node.** The all-faces totality with a genuinely plural symmetric face space is never shown to be recoverable (which would land the collapse on it) or shown to be free (which would mean monism wins and the spine Failed). Until that fork is resolved as a theorem, the headline "no god's-eye node exists" overstates what the code proves, and the Spinozist retreat is left formally ajar.

This is not fatal and it is not a lowered bar: the correction is *prove the ≥2-face symmetric node is recoverable (spine lands) or free (monism wins, report Failed)*, or *build the literal coproduct bisimilarity (C3)*. Two REAL items (the depth-advancing kill witness R1; the constant verdict-selector R2) are cheap relabels/strengthenings, and R3 (run `#print axioms` live) is procedural. No goalposts moved: every correction is "prove that / build the witness / relabel / run it," never "lower the bar."

**Recommended dispositions for Phase E:**
1. **S1 (WS1):** attempt the charter-strength theorem — symmetric ⟹ recoverable for |Q| ≥ 2 — first; if it resists, deliver the honest Failed-or-Partial with the obstruction precise. Do not ship "no god's-eye node" until then; relabel to "recoverable god's-eye nodes collapse" in the interim.
2. **R1 (WS5):** build the constant-branching depth-advancing witness; route into `ws5_kill_condition`.
3. **R2 (WS7):** relabel the verdict prose, or make `verdict` branch on its certificate.
4. **R3 (build):** run `lake build Series8 Series8.AxiomCheck`; confirm the live axiom printout equals the committed log; cite the commit.

Then loop back to a fresh Phase D pass. Exit only when the S1 fork is a theorem or a correctly-labelled terminal Impossibility/Failed — not when "the build finally passes."
