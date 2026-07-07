**Outcome class: Failed** (at the level of the charter obligation WS1 was set to discharge), with a fully precise account of why — which is exactly what the charter asks for in this case.

Here is the mapping.

**What the charter asked WS1 to deliver.** Charter §4 (WS1) and §6 (deliverable 2) require an *existence/uniqueness theorem* for the groundless carrier: confirm the reflexive, relation-only objects exist, unique up to bisimulation, non-degenerate. The design document (§5) operationalizes this as `ws1_C1`: a `GroundlessCarrier` exists for every infinite regular κ, built from terminality of `P_κ`, with terminality *derived* from the one sanctioned black box (`stabilization_theorem`) via Corollary 2.2.

**What the Lean file actually proves.** The file proves everything *downstream* of terminality cleanly and sorry-free: Lambek (`lambek`), bisimulation = identity (`bisim_eq`), non-degeneracy, `Ω = {Ω}` (`omega_selfsingleton`), the solution lemma (`ws1_C2`), and Ω-consistency (`omega_consistency`). Per the file's own `#print axioms` accounting, those all rest only on Mathlib's standard axioms. That is real, verified mathematics.

**Why it nonetheless fails the workstream obligation.** The existence of the carrier — the actual content of the WS1 deliverable — is not proved. It is *assumed*, via `exists_terminal_coalg`, which asserts `∃ U, IsTerminalCoalg U` outright. The file's header is scrupulously honest that this axiom sits *downstream* of the design's sanctioned boundary and is strictly stronger than it. The design sanctioned exactly one black box: `stabilization_theorem`, which concludes only a stabilizing iso on the terminal sequence, under `hacc` (Lemma 1.2) and `hbdd`. Terminality was to be *derived* from that via the Corollary 2.2 transfinite inductions. Instead, `exists_terminal_coalg` folds three registered obligations into an axiom rather than discharging them:

- Lemma 1.2 (κ-accessibility of `P_κ`) — assumed;
- Corollary 2.2 cone-map existence (recursion) — assumed;
- Corollary 2.2 cone-map uniqueness (induction), the §7 tier-2 risk co-equal with stabilization itself — assumed.

So the single hardest, highest-risk component of WS1 — the one the design calls "the single most expensive sub-formalization," for which Mathlib has no reusable terminal-sequence/final-coalgebra infrastructure — is precisely the part not done. `ws1_C1` is therefore conditional on a hypothesis *strictly stronger* than the design's own sanctioned axiom. An obligation that is assumed rather than derived is not discharged.

**Why not "Partial."** Partial would require the obstruction-to-the-rest to be the residue after the core obligation is met. Here the unmet part *is* the core obligation (existence of the carrier), not a peripheral extension. The conditional assembly is genuine and valuable, but conditioning the deliverable on an axiom that assumes the deliverable's hardest half is a failure to achieve the obligation, not a partial achievement of it. (Had the file axiomatized at the *sanctioned* `stabilization_theorem` boundary and proved terminality from it, leaving only, say, Lemma 1.2 open, "Partial" would be defensible. It does the opposite: it axiomatizes past the boundary.)

**Why not "Impossibility proved."** Nothing negative is established; the gap is unfinished construction, not a proof that construction is blocked.

**Also flag (not part of the classification, but material to the charter mapping):** even the conditional result realizes Commitment 1 against the *bounded* `P_κ` reading, the declared WS1↔WS7 drift from charter §3.1's full-powerset/AFA carrier. That drift is a separate, openly-declared concession; it does not change the outcome class but should not be silently absorbed into a "success" report.

**Methodology note triggered (per your rule that a failed result triggers a note, not a reframe).**

The failure is localized and the path to closing it is already specified, which is the useful output here. Three items return to the open ledger as the WS1 critical path: (1) restate the axiom at the sanctioned `stabilization_theorem` boundary — a stabilizing iso on `finalSeq.connectingMap` under `hacc`/`hbdd` — rather than at `IsTerminalCoalg`; (2) construct `finalSeq` per §2.1 and prove `IsTerminalCoalg` from the stabilizing iso via both Corollary 2.2 inductions, with explicit attention to the limit-stage uniqueness invariant flagged as tier-2; (3) discharge Lemma 1.2, checking step (b)/(c) against Mathlib's `IsCardinalFiltered` API before reproving. Prior to any of that, the separately-scoped bound-pinning sub-task from §2.2 (verifying `α ≤ κ.ord` against Worrell / Adámek–Milius–Moss) must be signed off, since a wrong bound would typecheck against a false external fact with no local proof to catch it. The downstream results (Lambek, bisim=identity, C2, Ω-consistency) need not be revisited — they are already unconditional given terminality — so the entire remaining cost is concentrated in the existence layer.

One additional note for downstream consumers: no workstream should cite `ws1_C1` as establishing the carrier's existence. It may be cited only as "*given* terminality of `P_κ`, the carrier has the following bundled properties" — and the WS1↔WS7 boundedness obligation (§0.1, §8) remains open regardless.
