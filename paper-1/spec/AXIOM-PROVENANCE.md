# paper-1 — axiom & lemma provenance

**Status: canonical home of its own closure.** Under the lazy-fork discipline (handoff XIII), paper one's
modules are *not* forked from `theory/` — they live here canonically, frozen, and `theory/` forks *forward*
from here when (and only when) it first diverges. So today there is nothing "forked in" to drift-check; the
provenance is the inverse of the eager template.

- **Canonical here (frozen):** paper one's axiom spine (`RelExist.Mirror/Relating/Seam/SeamBridge`,
  aggregator `RelExist`) and its kept mathlib closure (`Scratch.*`, aggregator `Scratch`). Module names are
  byte-for-byte the pre-reorg names; only file *locations* and six import lines changed in the reorg.
- **Imported (not forked):** `foundation/` — the traced-SMC typeclass (`Foundation.Traced`), at `fe935a6`.
  Safe to import: `foundation` only generalizes (backward-compatible), toward an eventual mathlib PR.
- **Forked *out* of here (by `theory/`, on demand):** `Theory.We`, `Theory.RotatingSpectrum`,
  `Theory.BandCoincidence`, `Theory.BandFromAxioms` are frozen copies `theory/` took from this root at
  `fe935a6` because its frontier modules (`Priority`, `MutualCoupling`) consume them. They may now diverge;
  see `theory/spec/PROVENANCE.md` for the drift note. This root does not depend on those copies.

**Deliberately divergent (future):** when `theory/`'s axiom readings move ahead of paper one's
(A3 = `νΦ_c`-at-trace-limit here vs. the modular/phase-bearing reading in `theory/`), this file records the
split per affected module. **Intended identical (today):** everything, because no divergence has landed yet.

**Drift check:** diff this root's `Scratch.*`/`RelExist.*` against the corresponding `theory/` forks; any
*accidental* difference in an "intended identical" module is a bug to reconcile, any *deliberate* one is the
sequel's content and belongs in the list above.
