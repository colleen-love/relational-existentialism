# paper-1 exploration — archived structural reference

This is the **fuller exploration** that found and surrounds paper one's headline result
(*self-relation generates the irreversibility of time*, kept live in [`../../../paper-1/`](../../../paper-1)).
It is preserved here as **structural reference — not deleted, not on the build path, not gated.** Paper one
itself stands on a single definition and a single theorem; this is everything that established the arena
around it.

## Why archived

The live paper was focused down to one self-contained claim. The results below are real and were mechanized
(or argued at paper level with the boundary disclosed), but they are **not needed to communicate the
headline**, so they were moved out of the paper to keep it legible. Mine them when the relational re-grounding
of the downstream papers (time / energy / conservation) resumes.

## Lean (`formal/Paper1/`) — was mechanized; now reference only

| File | What it established |
|---|---|
| `Existence.lean` | a fixed self-relation exists (relational Knaster–Tarski); `τ`-free |
| `Seam.lean` | the seam / reflexive opacity (Lawvere; **0 axioms**, arena-independent) |
| `TraceSeam.lean` | the feedback trace `Tr = D1` is `τ`-free; `Tr` vs the factor trace `τ` (verdict **B**, the dimension-function bridge) |
| `TypeIII.lean` | the `τ`-free results port to type III; the equilibrium-self entry point |
| `RaisingDynamics.lean` | the re-entry dynamics (selves are idempotents); the passivity→KMS bridge reduction |
| `ModularInterface.lean` | the cited, non-relational modular-theory interface (Tomita–Takesaki, KMS, Takesaki duality) as assumed axiom-fields |
| `ModularBuild.lean` | `A3 = σ ⊕ arrow` proved **relative to the interface**; `#print axioms` disclosure |
| `Frontier.lean` | the order-proxy of the raising dynamics; obstruction statements |

*(The headline's `reenter` definition and the irreversibility theorem now live in the live paper —
`paper-1/formal/Paper1/{Arena,Arrow}.lean` — so these files are reference, not imported.)*

## Spec (`spec/`) — the exploration record

`03-theorem-debt.md` (the graded ledger) · `04-provenance.md` · `05-trace-seam.md` (does `Tr` = `τ`?) ·
`06-type-III-modular.md` (the move to type III; *is A3 the modular flow?*) · `07-interface.md` (the
assumed/constructed boundary + disclosure table) · `08-raising.md` (deriving A3; the collapses) ·
`09-arrow.md` (the full arrow verdict the live `02-foundation.md` distills) · `10-open-questions.md`.

These docs cross-reference each other and the Lean beside them; their links resolve **within this folder**.
This is a layer **distinct** from the older traced-SMC archive ([`../INDEX.md`](../INDEX.md)) — that one is
the *previous arena*; this one is the *relational exploration* behind the current paper.
