# Series 08 — Independent Adversarial Whole-Series Review

**Reviewer:** Claude, adversarial pass, source-level only.
**Branch:** `claude/series-08-setup-cleanup-xgo4df`.
**Scope:** `series-08/formal/Series08/` (ws1–ws7, `Series08.lean`, `AxiomCheck.lean`) read against `charter.md`, the seven `spec/wsNN-design.md`, `spec/README.md`, `charter-status.md`, and `protocol.md` §0.3–0.6. The two prior in-repo passes (`spec/series-review-1.md`, `spec/series-review-2.md`) were read *after* forming my own conclusions, only to avoid duplicating labels and to check goalpost movement.
**Method:** the build was NOT run (per instruction). Every claim is checked by unfolding the actual Lean terms. `grep` confirms no `sorry`, no `admit`, no `native_decide`, no `opaque`, no `unsafe`, and no custom `axiom` anywhere but comment strings. Every `decide` is on decidable `ULift Bool` (in)equalities and is legitimate. The closure gate is sound: Series 08 imports resolve only to `Series08.*` + Mathlib (grep-confirmed; nothing from `series-07/`, `series-04/`, `archive/`).

---

## Snapshot verdict

The bound side is genuinely clean and, on the point pass 1 flagged, genuinely fixed: conservation is not baked into the map, the kill condition is built and depth-advancing, and the verdict (Partial) is honestly labelled. The engine (WS3), no-leaf (NL), forced-dynamics-as-seriality, and endogenous order all hold as written and are correctly scoped.

The positive side still fails at its sharpest point. The Spinozist retreat (§0.5) is **still not closed**. Between pass 2 and now, the response was to *redefine* the god's-eye node as the positionless (constant-`dest`) node `Symmetric := ∀ x y, dest x = dest y` and prove that collapses. That is precisely the move §0.5 forbids: the god's-eye node is **asserted positionless by a definitional clause**, not **proved** to collapse from holding a genuine plurality of faces. The one honest multi-face symmetric witness in the file (`symLoop`) is shown *not* to be relationally identified, so the spine's hypotheses are jointly inhabited only by subsingletons. The charter's literal target — a real all-faces node *proved* bisimilar to the trivial self-loop — is still unbuilt (design C3, still owed). **One SERIOUS finding stands.** It is the same finding pass 1 and pass 2 raised; the third response relabelled rather than closed it.

Everything else is REAL (correctly labelled) or ACCEPTABLE.

| Check | Owning WS | Result |
|---|---|---|
| Spinozist retreat (§0.5) | WS1 | **SERIOUS** — god's-eye node defined positionless (`∀ x y, dest x = dest y`); bisimilarity holds by definitional rewrite; the genuine multi-face symmetric node is excluded via `¬ BehaviorallyIdentifiedL`, not collapsed |
| Conservation-by-fiat (§0.4) | WS3/WS5 | **CLEAN** — `breadth` measured outside `ReReStep`; kill condition run and depth-advancing; verdict Partial, honest |
| Strip test on every payoff (§0.3) | WS1–WS6 | **ACCEPTABLE** — every residue is a bare bisimulation / subset / seriality / cardinality fact; all disclosed in-code by `ws7_strip_ledger`. The "face" strip is the S1 surface |
| Freeness verdict (WS2) | WS2 | **REAL** — delivers monism-broken as a *local pair-fact*; the *global* (no-totality) freeness the charter leans on is only as strong as the spine, i.e. currently not at charter strength |
| Endogenous order (WS3) | WS3 | **CLEAN** — `prec` is `ReflTransGen ReReStep`, `dest`-only; the imported-index branch is refuted by a real self-loop step |
| Forced-dynamics vs finitude (coincidence) | WS3 | **CLEAN** — independent content is `SHNE.succ` (seriality), not the definition of `ReReStep` |
| No-leaf (NL) | WS3 | **CLEAN** — `SHNE` preserved; no transient bare relatum |
| Conservation verdict {D/R/P} | WS5 | **Partial, honestly labelled** — a first-class outcome, correctly reported |
| Axiom-check actually run | AxiomCheck | **REAL** — all 37 `#print axioms` lines are wired, but the log is a static committed transcript; not re-verifiable without a build |
| Verdict is a function of the audit (WS7) | WS7 | **ACCEPTABLE** — `verdict` is a constant selector; the load-bearing object is the `Audit` structure, honestly relabelled |

---

## SERIOUS findings

### S1 — WS1: the Spinozist retreat is smuggled past by a definitional clause; the god's-eye node is *asserted* positionless, not *proved* to collapse.

**What §0.5 / charter §5.1, §5.5 demand.** The all-faces (god's-eye) node must be *proved* bisimilar to the trivial self-loop and hence collapsed by the engine — "not merely asserted positionless / excluded by a definitional clause." "Holds all faces symmetrically" must be shown to *be* the collapsing object.

**What the code does (ws1.lean:321–344).** The current charter-strength spine defines

```lean
def Symmetric (dest : X → LkObj κ Q X) : Prop := ∀ x y, dest x = dest y
```

and proves `ws1_symmetric_bisim_trivial : Symmetric dest → IsBisimL dest (fun _ _ => True)` followed by `ws1_gods_eye_collapses : Symmetric dest → BehaviorallyIdentifiedL dest → Subsingleton X`.

Two problems, both matching the §0.5 "smuggled" pattern.

**(A) The god's-eye node is defined positionless.** `∀ x y, dest x = dest y` does not say "one node holds all faces symmetrically." It says *every node has a literally identical successor structure* — every node IS the same node. That is a definitional clause asserting positionlessness, not a property derived from all-faces-holding. Consequently the bisimilarity is not earned: the proof of `ws1_symmetric_bisim_trivial` is `rw [← hsym x y]` / `rw [hsym x y]` — it discharges the all-true relation as a bisimulation *by rewriting the definitional equality*. The theorem does no collapse work beyond restating the definition. This is the charter's own C3 target ("bisimilar to the trivial self-loop") in name, but obtained by making the carrier constant rather than by relating a genuine all-faces node to `twoLoop` (the coproduct-carrier construction the design triaged as "owed" and never built).

**(B) The genuine multi-face symmetric node is excluded, not collapsed.** The one honest witness of a symmetric node with ≥2 faces is `symLoop` (ws1.lean:349, `dest _ = {(true,true),(false,false)}`, constant, genuinely two-faced). But `ws1_symLoop_not_behav` proves `¬ BehaviorallyIdentifiedL (symLoop)`. So `symLoop` does **not** satisfy the spine's second hypothesis; it is never collapsed by `ws1_gods_eye_collapses`. It simply fails to be relationally identified. Because the theorem itself forces `Symmetric ∧ BehaviorallyIdentifiedL → Subsingleton`, the two hypotheses are jointly inhabited only by subsingletons (≤1 state). The "totality that genuinely holds many faces and then collapses to the One" — the object the spine exists to annihilate — is never exhibited. The collapse bites only on constant/degenerate coalgebras.

**Why this is the retreat, still ajar.** The charter's Spinozist rebuttal is: *a node genuinely holding a plurality of faces symmetrically is bisimilar to the trivial loop and collapses.* The code instead (i) redefines "god's-eye" as constant-`dest` (positionless by fiat) and (ii) shows the genuine multi-face symmetric node is merely not-relationally-identified. Neither is "the all-faces totality collapses." Both are the definition or the hypotheses excluding the multi-face case — exactly the "excluded by a definitional clause" that §0.5 names as the SERIOUS outcome. Across three attempts (pass-1 `Recoverable`-fork, pass-2 rejection, this positionless redefinition) the object has been narrowed until the collapse is trivial, rather than the collapse being proved on a fixed, faithful object.

**Coincidence-rule note.** `ws1_gods_eye_collapses` is not independent of relational identity: its proof is literally `hbehav` applied to a bisimulation that holds by definitional equality. Unfold "forced collapse" and you reach "behavioral identity on a constant coalgebra" — the forced theorem unfolds into its definitional partner. The coincidence rule fails here.

**Grade rationale (protocol §0.6).** SERIOUS = the verdict rests on it / flagship payoff laundering / the Spinozist retreat smuggled. The headline verdict `perspectiveEstablished` (WS7) rests on `Audit.spineCollapses`, which is now `ws1_gods_eye_collapses`. The spine is the blocking gate; nothing downstream is at charter strength until it lands. This is the sharpest risk the charter names, resolved by definition.

**Correction owed (no goalpost move).** *Prove that / strip and re-prove.* Either:
- build design C3 honestly: exhibit a single relationally-identified node whose face-set includes ≥2 distinct perspectival restrictions, and *prove* it bisimilar to `twoLoop` on the coproduct carrier `X ⊕ ULift Bool`, collapsing by the engine; or
- prove the bridge the design promised — "genuine-plural-faces-held-symmetrically ⟹ `Recoverable`" — so that `ws1_no_gods_eye` bites on a real multi-face node rather than only on `facedLoop` (one constant `Unit` label).

Until one of these lands, relabel: `ws1_gods_eye_collapses` is a **constant-coalgebra collapse**, and the spine's status is **Partial / Spinozist retreat OPEN**, not "Impossibility proved at charter strength." Do not lower the bar; the bar is "collapse a genuine all-faces node," and it has not yet been cleared.

---

## REAL findings (genuine gaps, correctly labelled once fixed)

### R1 — WS2: freeness delivered is local (a pair-fact), while the charter leans on global (no-totality) freeness.

`ws2_perspective_breaks_merge` / `ws2_monism_broken` establish, for `labelLoop`, that `⟨true⟩` and `⟨false⟩` are plain-bisimilar but not label-bisimilar, and `¬ Recoverable (labelLoop)`. This is sound and it is the correct freeness *witness*. But the charter's payoff (§4.1, README §2.3) needs freeness to be **global**: "no single node recovers all faces, because the node that would is the god's-eye node, which does not exist." That "does not exist" is supplied by the spine — which is currently at constant-coalgebra strength (S1). So the global freeness WS2 imports from WS1 is only as strong as S1 permits. As a local pair-fact WS2 is CLEAN; as the global freeness the charter's plurality claim requires, it inherits S1's shortfall. Correction owed: once S1 is closed, state explicitly which freeness (local pair vs global no-totality) each WS2 headline delivers, and route the global one through the fixed spine.

### R2 — AxiomCheck: the axiom-clean claim is a static transcript, not a verified run.

`AxiomCheck.lean` contains all 37 `#print axioms` lines (grep-confirmed: 37 lines, matching the 37 bullets in `spec/axiom-check-log.md`; the earlier 29/34/37 drift is reconciled in `charter-status.md`). The wiring is correct and complete. But the pass/fail evidence is a committed markdown transcript asserting every headline prints `[propext, Classical.choice, Quot.sound]`. Without building, this cannot be independently confirmed here, and the log itself notes it should cite a specific commit hash and clean-build log. Correction owed: *run it* — regenerate the log from a live `lake build Series08 Series08.AxiomCheck` and record the commit hash. (This is procedural, not a math gap; the theorems inspected use only standard tactics, so the claim is plausible — but "was `#print axioms` actually run?" cannot be answered yes from the repository state alone.)

### R3 — WS7: `verdict` is a constant selector, already relabelled but worth restating.

`verdict _cert _settled := .perspectiveEstablished` ignores its arguments; it cannot branch on a `Prop` certificate (proof-irrelevant). The load-bearing anti-hand-setting content is the `Audit` structure, whose five fields are theorems. This was flagged and relabelled in pass 1 (R2) and the docstrings are now honest about it. It is correctly labelled, so ACCEPTABLE — but note that with S1 open, `Audit.spineCollapses` discharges only the constant-coalgebra collapse, so a green `Audit` currently certifies less than "perspective established at charter strength."

---

## COSMETIC / ACCEPTABLE

- **Strip-test residues (§0.3), all disclosed.** `ws7_strip_ledger` states in-code that each payoff, stripped of its structural word, is a bare fact: plurality → label-vs-plain bisimulation; depth → subset-monotonicity of reachable sets along `ReflTransGen`; forced-dynamics → seriality (`SHNE.succ`); the bound → `PkObj`'s κ-cardinality bound. This honest disclosure is the correct handling: the mathematical cores are Series 07/04 machinery and the perspectival readings are named as interpretive surplus. ACCEPTABLE because it is labelled, not hidden. (The one strip residue that is *not* merely interpretive is the "face" strip on the spine — that is S1, graded SERIOUS above.)
- **`ws6_universal_theses : True := trivial`** is honest scaffolding for "defended above the floor, off the machine," not a claimed theorem. Fine.
- **Count reconciliation** (30 → +4 → −2 +5 → 37) is internally consistent between `AxiomCheck.lean` and the log.

---

## What survives cleanly

These hold as written under source unfolding and meet their stated (honest) targets:

1. **The re-restriction engine (WS3).** `ReReStep h h' := h'.1.1 = h.1.2 ∧ h'.1.2 ∈ (dest h'.1.1).1` follows the edge and touches no sibling set — foreclosure is *not* baked in. `prec := ReflTransGen ReReStep` is `dest`-only and endogenous. `ws3_imported_index_refuted` exhibits a genuine self-loop step `ReReStep h h`, refuting any strict monotone external index. CLEAN.
2. **No-leaf (NL).** `ws3_rerestriction_no_leaf` preserves `SHNE` and never empties a node; the rejection of limit-atomlessness (§4.3) is honored. No transient bare relatum appears anywhere. CLEAN.
3. **Not-a-function (NF).** `ws3_rerestriction_not_function` gives two distinct re-restrictions from a two-successor node. CLEAN.
4. **Forced dynamics.** `ws3_dynamics_forced` is seriality on an atomless field, honestly the bare fact `SHNE.succ`; it does not overclaim. CLEAN, and the coincidence rule passes (independent of the `ReReStep` definition).
5. **Depth-is-narrowing (WS4).** `ws4_step_narrows` / `ws4_depth_is_narrowing` give `afford h' ⊆ afford h` along `prec`, and `ws4_depth_forecloses_witness` inhabits *strict* `⊂` on `treeDest` without claiming universality. The `⊆`/`⊂` scoping (leaving strict universal foreclosure to WS5) is honest. CLEAN on the mechanized core; universal form correctly left to WS6.
6. **Conservation-by-fiat check (§0.4) — CLEAN, the sharpest on the bound side.** `breadth h := mk (dest h.1.2).1` is defined *outside* `ReReStep`. Conservation is a *fact about the map* (`Conserves`, `ConservesStrict` quantify over `ReReStep`), never a clause inside it. The kill condition was **actually run**: `ws5_kill_condition` **builds** a witness (`pingPong`, two states `⟨true⟩ ↔ ⟨false⟩`) with a genuine depth-advancing step `h ≠ h'` and breadth preserved — so strict conservation is **Refuted** (built, not assumed impossible), `ws5_strict_refuted` confirms it on `twoLoop`, and `ws5_conserves_if_nonincreasing` gives the weak form on a hypothesis-gated class. Verdict `partialV`. This is the charter §5.4 fork resolved honestly: strict Refuted, weak Discharged-on-a-class, overall Partial, "self-limiting universe" retracted (`ws6_conservation_retracted`). The coincidence rule passes: refutation is a fact about `pingPong`, independent of `ReReStep`'s definition.
7. **The conservation verdict, stated plainly:** **Partial** (strict form Refuted-by-witness, weak form Discharged on a non-increasing class). It is one of {Discharged, Refuted, Partial}, and it is honestly labelled and consumed by WS7's `Audit.conservationTested` and the strip ledger. Not assumed; not unstated.
8. **Closure / hygiene.** `sorry`-free, no custom axioms, gate-clean, self-contained transcription.

---

## Honest bottom line

The bound side of Series 08 is a success and is reported honestly: conservation was genuinely tested, the kill condition genuinely fired on a genuinely depth-advancing witness, and the "self-limiting universe" was genuinely retracted. That is the charter's hardest methodological discipline (§0.4, §5.4) met in full. WS3/WS4/WS5/WS6 hold at their stated (appropriately modest) strength.

The positive side does not yet reach the bar its own charter set. The spine — the blocking gate the whole series rests on — still does not *collapse a genuine all-faces node*. Three successive responses have narrowed the god's-eye object (from `Recoverable`-conditional, through a tautological fork, to a positionless-by-definition constant coalgebra) so that the collapse becomes trivial, instead of proving the collapse on a fixed faithful object. The current `Symmetric := ∀ x y, dest x = dest y` is the "asserted positionless / excluded by a definitional clause" outcome that §0.5 pre-registers as SERIOUS. The genuine multi-face symmetric node is handled by denying it relational identity, not by collapsing it.

So the correct program-level status today is: **conservation fork settled (Partial), honestly; spine Partial with the Spinozist retreat OPEN; verdict `perspectiveEstablished` overstated at charter strength.** The fix is not to lower the bar but to build the collapse the design already specified (C3, coproduct carrier) or the bridge lemma (plural-symmetric ⟹ recoverable), and — until then — to relabel the spine as a constant-coalgebra collapse and the retreat as open. Everything needed to do this honestly is already in the repo; what is missing is the one theorem that was triaged as "owed" and never written.
