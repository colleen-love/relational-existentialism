# T.05 — Lived-identity coinduction

> *Node `T.05`.* Lean: `Theory.We` (`theory/formal/Theory/We.lean`); imports mathlib only.

Lived identity is the **greatest bisimulation** `≈ := νΘ` on a behaviour coalgebra `(obs, step)` — the
coinductive equality of states with the same forward behaviour, built via `OrderHom.gfp` (Knaster–Tarski).
`≈` is reflexive, symmetric, transitive, and the **finest real identity** (you are your relating). This node
is the coinductive base the A2-priority result (`T.06`) descends to the world of selves `𝔼 = D/≈`.

*(Paper one carries its own lived-identity node, [`P1.05-lived-identity.md`](../../paper-1/spec/P1.05-lived-identity.md),
for theorem 3.2; `Theory.We` is the copy `theory/`'s `Priority`/`Axioms` need, since `theory/` cannot import a
paper.)*

Consumed by **T.06** (`Priority`). Canonical axioms: [`AXIOMS.md`](AXIOMS.md).
