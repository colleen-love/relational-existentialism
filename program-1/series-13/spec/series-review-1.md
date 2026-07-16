# Series 13, Series Review 1 (Phase D)

**The blind whole-series review of the Phase C build on branch `claude/series-13-design-docs-s7uthq`, per protocol §2 Phase D. Findings carry stable IDs (SR1-N) for the Phase E closure and the pass-2 recurrence check.**

**Disclosure (protocol §0.1).** This review is NOT blind in the protocol's strict sense, and the breach is worse than Series 12's: the reviewer read `charter.md` in full, including its motivating prose (the wound and the rescue, the fit, the given/chosen fork), BEFORE reading the code, and read the design docs before forming findings. Protocol §0.1 requires the reviewer see the code, the design signatures, and the charter's success criteria, and NOT the motivating prose. That condition is not met. This artifact is therefore a **non-blind adversarial review**, and its clean verdicts on the discipline checks should be discounted accordingly: a reviewer who has read the prose is exactly the reviewer most likely to see the prose's claims in the code. The anchors that keep it honest despite this: every finding below cites an exact declaration and an exact defect, and every check was run mechanically against the source (greps, statement-by-statement comparison of built signatures to design signatures). A genuinely blind pass should still be run before Phase F.

**Second disclosure: the axiom and sorry-freeness claims are UNVERIFIED in this session.** No Lean toolchain was available and `leanprover-community` is outside the sandbox's network allowlist, so `lake build` could not run. `spec/axiom-check-log.md` records a clean three-series build (30 `propext` records, standard three only); this review could not reproduce it. The `sorry`/`axiom` greps are clean at the source level (matches are docstring prose only), which is necessary but not sufficient. **SR1-6 below.**

**Scope.** `series-13/formal/Series13/{ws1..ws5, AxiomCheck}.lean` + `Series13.lean` (1,039 lines), `spec/*.md`, `charter-status.md`, `lake/lakefile.toml`, `scripts/gate.sh`, against the design contracts and the charter's success criteria (§6) and false escapes (§4).

---

## 0. Hygiene

**Source-level hygiene: PASS.** No `sorry`, no `admit`, no custom `axiom`, no `native_decide` in `formal/` (greps hit docstring prose only). Imports resolve to `Mathlib` and `Series13.*` only — no cross-series imports, the standalone discipline held at the source level (but see SR1-4: the gate does not check this).

**Names-not-terms (§0.6b): PASS.** Grep over `formal/` for declarations named `given`, `chosen`, `consciousness`, `God`, `choice`, `compass`, `origin`, `genealogy`: clean. No declaration, proof term, or discharged obligation carries a name from the interpretive vocabulary. The words `given`/`chosen` appear in docstrings and module prose only.

**The fork stays open (§0.4, the central sin): PASS.** This is the check the series most needed to pass and it passes in substance. `ws4_mint_not_surjective` states `¬ ∃ insp, labEquiv h₀ (mintL h₀ insp) (outWit h₀ h₁)` — pure location, no sorting predicate. No `Origin` type, no `genealogy` function, no theorem or definition anywhere partitions out-of-image imports. The prose glosses the remainder as where the given stands; the core locates and stops. **The central sin is not committed.**

**Recurrence check (§0.2a):** not applicable. This is review pass 1; there is no prior review artifact and no design-review-1 for Series 13. Findings below establish the ID space for pass 2.

---

## 1. The protocol's Phase D checks, run

**The strip test (§0.3).** Run per payoff, deleting "duality / fit / wound / rescue / given / chosen / mint / factory / connection / defect":
- **Transport** strips to *"for every inspection, the two-region labelled coalgebra broadcasting `(residue insp, insp h₀)` fails `Recoverable`, by `ws2_residue_distinct`"* — exactly what §0.3 demands it strip to. **PASS.**
- **Connection** strips to *"a `GaloisConnection` between two preorders whose interior round trip is not the identity at `bRefActive`."* **PASS**, with the non-triviality caveat of SR1-1.
- **Defect** strips to *"a `¬ Recoverable` two-label struct not order-equivalent to any mint, the exclusion by the diagonal link."* **PASS as a fact about `Lab`**, not about labelled coalgebras — SR1-3.

**The genuine-connection check (§0.5, promoted first-class).** Requires both orders proved non-trivial AND a proved non-identity round trip. The round trip half is genuine: `ws3_roundtrip_not_identity` exhibits `bRefActive` with the interior strictly below the identity, the active reference-bit making the fold drop `h₀`. Real content, correctly proved. The non-triviality half **FAILS the design's own bar: SR1-1, SR1-2 below.**

**The exogeneity check (§0.6, promoted first-class).** `ws2_mint_exogenous` is a genuine proof term, not a docstring gloss: two inspections with identical plain projections receive different mints. And `ws2_mint_not_plain_function` **strengthens beyond what the charter asked** — it refutes the existence of ANY function from the plain relating reproducing the mint, rather than merely exhibiting a separating pair. The plain projection `plainOf_coalg_val` is proved constant in `b` (`i ↦ {i}`), which is the honest ground for the whole argument. **PASS, exceeding contract.**

**The structural-defect check (§0.6a).** `ws4_exclusion_structural` discharges charter §4.d properly, in three conjuncts that together do the work: `≈` preserves the link data (`cT` fully, `cF` at `h₀`); every mint is on the link (`cT h₀ = ¬ cF h₀`, by `rfl` — the diagonal, structurally); `outWit` is off it. The exclusion is by the witness's own label, not by cardinality, universe level, or typing. Testing mintability up to `labEquiv` rather than literal equality is the right call and is disclosed as such (literal equality would be DUAL-by-construction, a fake). **PASS.**

**The verdict is computed, not hand-set.** `ws5_fork` cases on `∃ h₁ : Hold dest, h₁ ≠ h₀` via `dite`; both branches are reachable and both are reached by theorems (`ws5_verdict_eq → Dual`, `ws5_verdict_degenerate → Total`). `verdictOfFit` genuinely branches over a four-constructor data-level `FitFork`, each constructor carrying its own proof. The falsifiability triple (`ws5_verdict_not_total`, `_not_disconnected`, `_not_partial`) routes through the fork. This is the Series 12 `verdictOfFork` pattern applied correctly. **PASS.**

**Cross-workstream laundering.** Every `Audit` field traces to a genuine WS1–WS4 theorem: `orders_nontrivial` → `ws1_orders_*_nontrivial`, `transport` → `ws2_transport_forall`, `exogenous` → `ws2_mint_exogenous`, `connection` → `ws3_galois`, `roundtrip_defect` → `ws3_roundtrip_not_identity`, `fork` → `ws5_fork`. No field is discharged by a weaker adjacent fact. **PASS in mechanism**, though `orders_nontrivial` inherits SR1-1's scope defect.

**The layer-stability open.** Correctly scoped, correctly confined to prose (`ws5.lean:155-157` is a comment, not a term), and correctly bounds the TOTAL branch ("TOTAL AT THE FLAT LAYER"). This is the honest-reporting discipline working. **PASS.**

---

## 2. Findings

### SR1-1 (SERIOUS) — the non-triviality theorems certify the orders only at hand-picked constant points, but the audit consumes them as carrier-wide. Owner: WS1.

`ws1_orders_insp_nontrivial` and `ws1_orders_lab_nontrivial` each prove `(∃ a b, a ≤ b ∧ a ≠ b) ∧ (∃ a b, ¬ a ≤ b)`. Both conjuncts are individually valid refutations of discreteness and indiscreteness *as global properties*, and the proofs are correct. The defect is scope, and it is load-bearing.

Charter §2 sets the bar as non-trivial "**on the carriers of interest**"; `ws1-orders-design.md:9` restates it as "neither discrete `= equality` nor indiscrete `= all-related` on the carriers of interest." Both built theorems discharge this using only the two constant inspections `⊤i := fun _ _ => True` and `⊥i := fun _ _ => False` (and, on the labelled side, two struct literals built from constant `HoldPred`s). Nothing in either theorem rules out the order being discrete or indiscrete on every **non-constant** inspection — which is the entire population `ws3_galois` quantifies over (`∀ insp b`) and the population `ws2_transport_forall` ranges across.

This matters because §0.5 is promoted to first-class precisely to prevent connection-by-fiat, and `ws1-orders-design.md:69` names the non-triviality theorems as "**exactly the certificate** that the winner A-C2 is neither" trivial order. A certificate evaluated at two constant points does not certify the carrier. WS5's `Audit.orders_nontrivial` then consumes the pair under a name that advertises more than the theorems deliver, and `ws5_audit_genuine_connection` reports the check as passed.

**Correction owed (exactly one of):** (a) strengthen both theorems to exhibit related-unequal and unrelated pairs among inspections the mint genuinely separates — the design already notes at `ws1-orders-design.md:28` that "incomparable singletons exist if `|Hold| ≥ 2`", which is the material for a real carrier-wide statement and would additionally exercise the non-constant population; or (b) rename the audit field and both theorems to state their true scope (non-triviality *witnessed*, not non-triviality *on the carriers of interest*), record the scope restriction as a charter discrepancy in `charter-status.md`, and demote the §0.5 genuine-connection check to **Partial**. Per §0.2a this must close as **Fixed** (the originally specified target built) or **Relabeled** (obstruction recorded, payoff demoted). It is currently neither.

### SR1-2 (SERIOUS) — `ws1_orders_lab_nontrivial` builds a different, weaker theorem than the design specifies, and the substitution retires the one witness that would have tested the antitone reference-position. Owner: WS1.

Design (`ws1-orders-design.md:181-190`) specifies:

```lean
theorem ws1_orders_lab_nontrivial {X} (dest) (h₀ : Hold dest) (hinf : ℵ₀ ≤ κ) :
    (∃ a b : Lab dest, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest, ¬ a ≤ b) := by
  refine ⟨⟨(fun _ => toPk hinf ∅), mintL dest h₀ (fun _ _ => True), ?_, ?_⟩,
          ⟨mintL dest h₀ (fun _ _ => False), mintL dest h₀ (fun _ _ => True), ?_⟩⟩
```

— the non-discreteness witness is **the empty coalgebra** `d⊥ := fun _ => toPk hinf ∅`, `≤ mintL ⊤i` vacuously (no edges to dominate), and the non-indiscreteness witness is a pair of **actual mints**, `mintL ⊥i ≰ mintL ⊤i`.

Build (`ws1.lean:397-400`) drops the `hinf` parameter entirely and substitutes four struct literals:

```lean
theorem ws1_orders_lab_nontrivial {X : Type u} (dest : X → PkObj κ X) (h₀ : Hold dest) :
    (∃ a b : Lab dest h₀, a ≤ b ∧ a ≠ b) ∧ (∃ a b : Lab dest h₀, ¬ a ≤ b) := by
  refine ⟨⟨⟨(fun _ => False), (fun _ => False)⟩, ⟨(fun _ => True), (fun _ => False)⟩, …
```

This is protocol §0.2a's explicitly prohibited third move: *"built a different, weaker theorem adjacent to the specified target and considered the finding addressed."* Three consequences, in increasing severity:

1. **No mint appears in the theorem.** The design's witnesses were mints; the build's are literals. The order is no longer certified non-trivial *at the points the mint occupies*.
2. **No coalgebra appears in the theorem.** The empty-coalgebra witness would have exercised the order against a genuine `LkObj`; the substitute never leaves the struct.
3. **Every witness has identical `cF` (`fun _ => False`).** So the antitone reference-position — the second conjunct of `instLELab`, and the entire contested half of B-C3 — is **never exercised by the non-triviality certificate**. Both `≤` checks pass their reference-clause vacuously (`False → False`).

Point 3 is why this is SERIOUS rather than REAL. `ws1-orders-design.md:157-159` pre-registers exactly this exposure and grades it: *"an order **reverse-engineered from the mint's own output** to force monotonicity and non-iso… a reviewer is entitled to ask whether that antitone choice is PRINCIPLED… or TUNED (chosen because it is what makes `mintL` monotone and `mintL ∘ readInsp` non-identity). If tuned, the connection is genuine only by fiat: the order was solved for the map… **SERIOUS if tuned.**"* The design assigns `ws1_orders_lab_nontrivial` a role in the defense against that charge. The built theorem cannot play it: it is silent on the antitone bit. The defense currently rests entirely on `ws1-orders-design.md`'s prose argument — which may well be right, but §0.5 requires a certificate, not an argument.

**Correction owed:** build the design's specified theorem (empty coalgebra + mint pair, `hinf` restored), which restores the antitone position to the certificate; or record the substitution as a charter/design discrepancy in `charter-status.md`, state that the tuned-vs-principled question is discharged by prose only, and demote accordingly. Fixed or Relabeled, not the current third thing.

### SR1-3 (REAL) — the payoffs are theorems about `Lab`, a two-field struct, not about labelled coalgebras; the charter's WS4 claim is broader than the built theorem. Owner: WS1 (definition), WS4 (claim), `charter-status.md` (discrepancy).

`ws1.lean:336` defines `Lab` as a struct of two `HoldPred`s, with `coalg` realizing it as a genuine `LkObj` on a two-element carrier. This is **disclosed** in the module docstring ("a faithful realization of the design's `MCar → LkObj` shape (disclosed in `charter-status.md`)"), and the disclosure is honest as far as it goes: every `Recoverable` fact is stated about `coalg b`, so those are facts about a real coalgebra. The realization itself is faithful.

But `instLELab` orders `Lab`, not coalgebras. So `ws3_galois`, `ws4_mint_not_surjective`, and the computed verdict are all statements about a two-label struct under a hand-chosen relation, transported to coalgebras only through `coalg`. Charter §2 WS4 asks for *"a labelled coalgebra failing `Recoverable` that no inspection mints"*; the built theorem delivers *"a `Lab` failing `Recoverable`-after-`coalg` that no inspection mints up to `labEquiv`."* Every two-region self-loop coalgebra is in `coalg`'s range, but the class of labelled coalgebras over `dest` is vastly larger, and non-surjectivity onto a two-point struct-image is a materially narrower claim than non-surjectivity onto the labelled coalgebras. `ws4_mint_not_surjective`'s name states the broader claim.

Compounding: the docstring says the disclosure lives in `charter-status.md`, and **it does not** — the ledger's discrepancy subsection still reads *"None yet… No design or build exists, so no discrepancy between the charter and built code can yet arise."* The disclosure points at an empty box.

**Correction owed:** record the `Lab`-vs-`LkObj` narrowing as a charter discrepancy in `charter-status.md` (the box the docstring already promises), and either rename `ws4_mint_not_surjective` to state its true domain or add a conjunct/corollary carrying the claim to the coalgebra level.

### SR1-4 (REAL) — `scripts/gate.sh` does not check Series 13. Owner: `scripts/gate.sh`.

The gate is the repo's stated mechanism for the standalone property (README: *"`scripts/gate.sh` confirms no cross-series imports"*). It runs `check series-07` and `check series-12` and exits. Series 13 is registered in `lakefile.toml` (`defaultTargets = ["Series07", "Series12", "Series13"]`) and asserts standalone-ness in three module docstrings and a lakefile comment, but no tool verifies it. By inspection the imports ARE clean (`Mathlib`, `Series13.*` only), so this is a gap in verification, not a leak. One line closes it:

```bash
check series-13 "^import Series13(\.[A-Za-z0-9_]+)*$"
```

### SR1-5 (REAL) — the ledger contradicts the branch it is on. Owner: `charter-status.md`.

`charter-status.md` is the instrument the recurrence guard (§0.2a) runs on, and on this branch it is stale to the point of falsity. It states *"Phase A has run; the charter, this ledger, and the protocol are written; **no design or build exists yet**"* — on a branch containing five design docs and seven Lean files. The phase table reads B/C/D/E/F **Not started**; all five workstream sections read **Not started**; every row of the result tracker reads **Not started**; all five open obligations read **Open**. The discrepancy subsection reads *"None yet"* (see SR1-3, which needs it).

Series 12's review caught the same class of defect (SR1-4 there, "27 stale 'Not started' occurrences") — this is that pattern recurring in a new series, not a §0.2a RECURRING (which tracks IDs within a series).

**Correction owed:** sweep the ledger to the post-build state before Phase E closes anything, since Phase E's closures must be recorded in it and named Fixed or Relabeled.

### SR1-6 (REAL) — sorry-freeness and axiom-cleanliness are unverified by this review. Owner: Phase E / Phase F.

`spec/axiom-check-log.md` claims capture from `lake build Series13.AxiomCheck` with 30 standard-three records and a successful three-series build. This session had no Lean toolchain and no network route to `leanprover-community`, so the log could not be reproduced. Source greps for `sorry`/`admit`/`axiom`/`native_decide` are clean, which rules out the crude failures but not, e.g., a `sorryAx` reached through a transcribed lemma. The charter's bar (§7) is "sorry-free and axiom-clean or it is not done."

**Correction owed:** re-run `lake build Series13 Series13.AxiomCheck` on a machine with the Mathlib cache and confirm the log before Phase F. Not a defect in the build — a gap in this review's coverage, recorded so pass 2 does not inherit the assumption.

### Cosmetic (fix opportunistically; none blocks)

- **SR1-7.** `ws1.lean:59` `toPk` requires `[Finite X]` and `ws1.lean:69` `pkSingleton` exists precisely to dodge it for infinite label types. The design's empty-coalgebra witness (SR1-2) uses `toPk hinf ∅` on `MCar` (finite, so fine), but the interaction is worth a docstring line so a later reader does not reach for `toPk` on a `HoldPred`-labelled type.
- **SR1-8.** `ws4.lean:36` `labEquiv` is defined as `b ≤ b' ∧ b' ≤ b` but is not registered as a `Setoid` or given `≈` notation, while three docstrings write `≈`. Either add the notation or write `labEquiv` in the prose.
- **SR1-9.** `FitFork.perInstance (hp : True)` (`ws5.lean:49`) is a constructor whose payload is contentless. It is never constructed (`ws5_fork` produces only the first two), so `Partial` is unreachable by construction — which makes `ws5_verdict_not_partial` true but vacuous in an uninteresting way. Either give the constructor a real payload or note in the docstring that `Partial` is reserved for a hand-report and cannot be computed.
- **SR1-10.** `ws5.lean:48` `FitFork.ordersTrivial`'s payload is `(∀ a b, a ≤ b) ∨ (∀ a b, a ≤ b → a = b)` — indiscrete-or-discrete on **inspections only**, with no clause for the labelled order. If `Disconnected` is ever to be computed, the labelled order needs its own disjunct. Currently unreachable, so latent.
- **SR1-11.** `ws1.lean:118` `ws1_recovers_static` and `ws1.lean:174` `ws4_recoverable_not_import` are transcribed but unused by anything in WS1–WS5 (grep: no call sites). Harmless transcription surplus; either cite them in the module docstring as touchstones or drop them.

---

## 3. What survives cleanly

The engine and the two payoffs the series was most likely to fake.

**WS2 is the strongest work in the series.** `ws2_mint_lands_in_opening` genuinely runs on the diagonal: the proof forces `residue insp = insp h₀` at the `(⟨true⟩, ⟨false⟩)` label-match and hands it to `ws2_residue_distinct`, which is `ws1_no_self_total_hold` — Cantor. Nothing is painted on; delete the diagonal and the theorem dies. `ws2_mint_exogenous` is a real proof term, and `ws2_mint_not_plain_function` overshoots the charter's ask in the honest direction (refuting all plain-recovering functions rather than exhibiting a pair). `plainOf_coalg_val` — the plain projection is constant in `b` — is the correct ground for exogeneity and is proved, not assumed. Charter §4.c is discharged.

**WS4's structural-exclusion argument survives the check it was designed against.** Testing up to `labEquiv` rather than literal equality is the honest resolution and is reasoned for explicitly (literal equality would make DUAL true by construction). `ws4_exclusion_structural`'s three conjuncts do the work jointly: the equivalence preserves the link data, every mint is on the link by `rfl`, `outWit` is off it. That is exclusion by the label, which is what §4.d and §0.6a demand. The degenerate TOTAL branch is built and reported rather than hidden, and bounded to the flat layer.

**The fork stays open.** The check the whole series turns on. Grep-clean, structurally clean: WS4 locates and never sorts, and there is no type, function, or obligation anywhere that partitions the out-of-image remainder. The prose does the interpretive work and stays in the prose.

**The verdict is computed and falsifiable.** `ws5_fork` cases on the carrier; both branches fire; both are theorems; the falsifiability triple is real. `Dual` is an earned output of a function that would have said `Total` on a different carrier — and does, in `ws5_verdict_degenerate`.

**WS3's non-identity round trip is genuine.** `ws3_roundtrip_not_identity` is not decorative: the reference-fold `gb` is lossy exactly when `b.cF h₀` holds, `bRefActive` activates it, and the interior lands strictly below. `ws3_galois`'s iff is exact rather than approximate because the fold was designed to make it so. The connection is not an isomorphism in disguise.

---

## 4. Honest bottom line

**Two SERIOUS findings, both at WS1, both about the same thing: the orders are certified by witnesses that do not exercise what the orders are made of.** SR1-1 (certification at constant points only, consumed as carrier-wide) and SR1-2 (the specified witness replaced by a weaker one that never touches the antitone reference-position) together mean the §0.5 no-connection-by-fiat discipline — **promoted to first-class by this series' own protocol precisely because this is its signature risk** — is not yet discharged in Lean. The design anticipated the exact charge (the reverse-engineered order, "SERIOUS if tuned") and assigned `ws1_orders_lab_nontrivial` to answer it; the built theorem cannot answer it. The tuned-vs-principled question is currently settled by `ws1-orders-design.md`'s prose defense alone.

This does not make the verdict wrong. `Dual` is defensible at the flat layer, for the `Lab` order, and the mathematics under it is sound as far as this reviewer traced it — WS2's transport is genuinely diagonal-driven, WS4's exclusion is genuinely structural, WS3's defect is genuinely non-identity, and the central sin is genuinely not committed. What is not yet earned is the claim that the order those results live on is principled rather than solved-for-the-map. Until SR1-1 and SR1-2 close, `Dual` rests on an order whose non-triviality certificate is evaluated at four constant points, two of which are the same point.

Three REAL findings are bounded and mechanical (SR1-3 the `Lab`/`LkObj` claim gap and its missing disclosure, SR1-4 the ungated series, SR1-5 the stale ledger), and one (SR1-6) is this review's own coverage gap on the axiom claim.

**Recommended Phase E:** close SR1-1 and SR1-2 first and name each **Fixed** or **Relabeled** in the ledger (§0.2a admits no third option); take SR1-3 through SR1-5 mechanically; re-run the axiom check for SR1-6. Then run series-review-2 — and per §0.1 it should be **genuinely blind**, seeded with the code, the design signatures, and the charter's §6 criteria only, with no motivating prose. This review was not, and says so; a blind pass on the WS1 orders is exactly what the tuned-vs-principled question deserves and exactly what this reviewer, having read the charter's prose first, was least equipped to give.

Per the canonical run (B → C → D → E → D → E), series-review-2 runs the §0.2a recurrence check on SR1-1 through SR1-6 before anything else.
