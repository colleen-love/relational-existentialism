# Program 2 Series 5 (2.5), Charter Status

**The living ledger. The charter is the fixed bar; this file records what is proved, what is open, and how every SERIOUS finding closed (Fixed or Relabeled, per protocol section 0.2a). It never edits the target to record progress.**

*Current phase: B (design committed). Current verdict: TBD (not computed until WS5). No formal build exists yet. All targets below are OPEN. This is the second series of Phase 2 (the physics of the built universe, `charter-extension.md`), THE LOOP: closed time, on the fold as its ground.*

---

## 0. Snapshot

- **Phase:** B complete (design batch committed: `spec/ws1-design.md`…`ws5-design.md`, `spec/README.md`). C (design review) next. **Precondition:** Series 2.4 landed (DISTINCT, including Charter Extension 1).
- **Verdict:** TBD.
- **Build state:** no series `formal/` sources yet. The imported chain (`P2S4`, `P2S3`, `P2S2`, `P2S1`, `P2S0`, `P1`) is built and registered, reaching all lower layers transitively.
- **Axiom state:** the imported layers are axiom-clean on the standard three. Series build N/A.
- **Gate state:** green upstream. S5's `formal/` will import `P2S4` only (gate `(P2S4|P2S5)`), reaching S3/S2/S1/S0/P1 transitively.
- **Costume gate (Phase-2 discipline):** PASSES at charter — the knot is DIAGONAL/CYCLE-powered (the coexistence of cyclic relating and acyclic time, and the fold's uniqueness), not import-powered, and NOT rank-well-foundedness alone. To be verified at Phase F (audit c).
- **Open SERIOUS findings:** none (no review has run).

## 1. The carrier — the fold on the imported chain

**S5 stands on the imported chain** (`program-2/series-4`, namespace `P2S4`, reaching `P2S3` / `P2S2` / `P2S1` / `P2S0` / `P1` transitively). Its working material is chiefly the Series 2.1 tick/causation and the P1 diagonal. Like S4, it builds its topological object — the fold — fresh. The pieces S5 builds on:

| Carrier piece | Where |
|---|---|
| The tick and causation: `ws4_causal_order_endogenous` (reification raises rank), the reification rank | `P2S1` (transitive) |
| The cycle-reification: `ws1_cycle_reifies` (a attends b attends c attends a reifies) | `P2S0` / `P2S1` (transitive) |
| The diagonal (makes the fold): `ws2_residue_free`, `ws1_no_self_total_hold`, the residue | `P1.Reader` (transitive) |
| Collapse engine, recoverability, atomlessness (no leaf, no smallest) | `P1.Core` / `P2S0` (transitive) |
| **The fold** (no poles; the largest bending into the smallest through the diagonal; Ω = {Ω} the seam) | **built at S5 WS1** |

**Design note (from `charter-extension.md` §4, 2.5):** poles/fold ALONE would be a corollary-assembly of already-proved facts (the K1/Bookkeeping trap at series scale). The weight sits on the LOOP (a genuine fork); the fold is its ground. This charter anchors there.

## 2. Targets (all OPEN until built and reviewed)

| WS | Target theorem(s) | Status | Closed how |
|----|-------------------|--------|-----------|
| WS1 | `ws1_no_pole_below`, `ws1_no_pole_above`, `ws1_fold`, `ws1_no_total_count` (the topology of the whole: no poles, the fold, the whole uncountable from within) | OPEN | — |
| WS2 | `ws2_relating_cycles` (attention genuinely cycles and reifies) | OPEN | — |
| WS3 | `ws3_causation_acyclic` (the reification-dependency raises rank, well-founded, no return among distinct relata) | OPEN | — |
| WS4 (the knot) | `ws4_loop_only_at_fold` (the fold the sole candidate) + the fork (ACYCLIC / LOOPED / SHAPE-DRAWN), LOOPED reachable, no fiat, no costume | OPEN | — |
| WS5 | verdict function + audit (`ws5_verdict_eq`, `ws5_verdict_discriminates`, `ws5_flags_justified`, audit a–e) | OPEN | — |

Names are the charter's provisional targets; Phase B fixes exact signatures, and any rename is recorded here with its reason (and note the §6 forbidden-word grep: "time"/"loop"/"self"/"fold" etc. may not appear in identifiers).

## 3. Audit clauses (WS5, all UNVERIFIED until Phase F)

- (a) NO POLES DECIDED ABSOLUTELY — the topology is stated structurally (no smallest, no largest, the fold), self-relative where a quantity is involved. UNVERIFIED.
- (b) THE FORK NOT BY FIAT — LOOPED genuinely reachable, causation's acyclicity proved from the rank-lift (not definitional), the verdict discriminating. UNVERIFIED.
- (c) THE KNOT IS THE COEXISTENCE, NOT WELL-FOUNDEDNESS (the costume gate) — the verdict rests on cyclic-relating-with-acyclic-time and the fold's uniqueness, not on rank being well-founded alone. UNVERIFIED.
- (d) THE FOLD IS THE DIAGONAL — `ws1_fold` / `ws4_loop_only_at_fold` rest on the P1 diagonal (`ws2_residue_free`), not on a seated import. UNVERIFIED.
- (e) NAMES-NOT-TERMS — grep clean of the forbidden content-names. UNVERIFIED.

## 4. Findings ledger (recurrence guard, protocol section 0.2a)

Empty. Phase C (design review) and Phase F (code review) findings are recorded here with stable IDs, grades (SERIOUS / REAL / COSMETIC), and closure (Fixed / Relabeled).

| ID | Phase | Grade | Summary | Closure |
|----|-------|-------|---------|---------|
| — | — | — | (none yet) | — |

## 5. Deviations from charter (disclosed)

None yet. Any narrowing between charter and design, or design and build, is disclosed here at the moment it happens.

## 6. Permanent opens (inherited, untouched)

- The content of the compass / orientation.
- The direction of convergence.
- The differentiating act.
- The classification of the out-of-image imports.

Series 2.5 adds none and closes none; it draws the shape of the whole and the acyclicity of time sharper.

## 7. Phase log

- **2026-07-21 — Phase A.** Charter committed (`charter.md`). Series 2.5 established as THE LOOP, the second series of Phase 2: build THE FOLD (the topology of the whole — no smallest by atomlessness, no largest by unbounded reification, the largest bending into the smallest through the diagonal, the seam Ω = {Ω}, and the whole uncountable from within) as the ground; prove the relating genuinely cycles (WS2) yet causation is acyclic (WS3, on Series 2.1's rank-raising causation); and at the knot prove the sole candidate for a closed causal loop is the fold, forking ACYCLIC / LOOPED / SHAPE-DRAWN, no fiat and no costume (the knot on the coexistence of cyclic relating and acyclic time, not on rank-well-foundedness alone). Costume gate passes at charter (diagonal/cycle-powered). Scaffold (`spec/`, `formal/`) to be created at Phase B. Next: Phase B, write `spec/wsNN-design.md` for WS1–WS5 and `spec/README.md`, committed as a batch before any series build. Weigh the witness: the Series 2.4 world (or a small cycle carrier) for the attention loop, a reification-dependency relation given structurally so its acyclicity is proved (not definitional), and a self-membered witness for the fold.
- **2026-07-21 — Phase B.** Design batch written and committed as one unit (`spec/ws1-design.md`…`ws5-design.md`, `spec/README.md`), before any `formal/` file (Phase B gate). Primitives fixed: the causal relation `causalDep attends comp t u := comp u ∧ t ∈ attends u` (a structural reification-dependency, NO rank in the definition, so audit (b) holds and acyclicity is proved not stipulated); the fold as the P1 diagonal (`ws1_no_self_total_hold` / `ws2_residue_distinct`, audit (d)). Two witnesses, both `Cardinal.{0}` on `Fin`: the tick carrier `TCar = Fin 7` (reached from `P2S1`) for the ACYCLIC zone (the relating cycles `p0 ⇄ p1` while `causalDep` strictly raises `rankT`, no self-membered composite), and the fold carrier `FCar = Fin 1` (fresh) for the LOOPED-reachable zone (a self-membered `om = {om}` gives a genuine causal self-loop admitting no rank-lift, so the fork is not by fiat). Verdict `verdict : Bool⁵ → Outcome`, `= acyclic` by `rfl`, discriminating, flags earned by the WS1–WS4 headlines; ACYCLIC demands the WS2 cyclic-relating flag AND the LOOPED-reachable flag, so the knot rests on the coexistence not on well-foundedness alone (audit c). All signatures VALIDATED against the compiler in a throwaway target (imports `P2S4`, sorry-free, axioms within the standard three) before commit, so Phase E builds to proven-buildable contracts. `P2S5` module naming fixed (Phase E registration recipe in `protocol.md`). Next: Phase C, generate `spec/blind-seed-C.md` and spawn a blind reviewer.
