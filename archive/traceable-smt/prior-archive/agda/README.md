# `archive/agda/` — archived Agda witness (paper three)

The Agda half of the **sparsity** result, set aside with the rest of paper-three material:
[`RelExist/Sparsity.agda`](RelExist/Sparsity.agda) — topological sparsity (the carrier of selves is nowhere
dense in the cylinder topology, `selves-nowhereDense`, with the sharp dichotomy `trivial→allSelf`).

It is `--safe --guardedness` and imports the *live* `RelExist.Coinductive`
([`../../agda/RelExist/Coinductive.agda`](../../agda/RelExist/Coinductive.agda)), so checking it in place
needs the live `agda/` library on the include path; like the rest of [`../`](..) it is **not built** here and
its cross-links are unmaintained. See [`../spec/03.7-sparsity.md`](../spec/03.7-sparsity.md) and the live
[`../../agda/README.md`](../../agda/README.md).
