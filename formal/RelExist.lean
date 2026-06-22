-- Relational Existentialism — formal development (root module).
--
-- Layer-by-layer mechanization of docs/spec. Currently:
--   * RelExist.Sparsity — the discrete core of Lemmas 3.1 & 3.2 (sparsity of Stab).
--   * RelExist.Loop     — step 3: the loop bridge from resource threshold to the
--                         A4 fixed-point definition of a self.
--   * RelExist.Mirror   — A6 (σ-side): Lawvere's theorem, the mirror that can't close.
import RelExist.Sparsity
import RelExist.Loop
import RelExist.Mirror
