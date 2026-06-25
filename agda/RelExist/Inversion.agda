{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- # The inversion in Agda: `≈ ⊊ ≅` over a NONDETERMINISTIC system
--
-- The doctrine's headline (A2 restated): the lived identity `≈` (bisimulation)
-- is STRICTLY finer than observational equality `≅` (trace equivalence) — there
-- is a first-person surplus the outside cannot read. In `RelExist.Coinductive`
-- the model is *deterministic* (a single `step`), where `≈ ⟺ ≅` collapse — no
-- surplus. The surplus is a **nondeterminism** phenomenon: it is the trace of
-- the branches *not taken*. So here we give a genuinely nondeterministic system
-- (the classic "early vs late choice", the same witness as Lean's
-- `Scratch/Identity.lean`) and prove `≈ ⊊ ≅`, matching the Lean development.
--
--   p0 ──a──▶ p1 ──b──▶ pB           q0 ──a──▶ qL ──b──▶ qLB
--                └─c──▶ pC             └──a──▶ qR ──c──▶ qRC
--
-- Both have trace language { [a], [a m], [a m b], [a m c] }, so `p0 ≅ q0`; but
-- `p0`'s single a-successor can still do *both* b and c, while neither of `q0`'s
-- can — so `¬ (p0 ≈ q0)`. The choice `q0` makes *early* is exactly the lived
-- distinction no outside trace records.
------------------------------------------------------------------------

module RelExist.Inversion where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

-- observations
data Obs : Set where
  oA oM oB oC : Obs

-- states of the witness system
data St : Set where
  p0 p1 pB pC q0 qL qR qLB qRC : St

obs : St → Obs
obs p0  = oA
obs p1  = oM
obs pB  = oB
obs pC  = oC
obs q0  = oA
obs qL  = oM
obs qR  = oM
obs qLB = oB
obs qRC = oC

-- the **nondeterministic** transition relation: one constructor per edge
-- (q0 genuinely branches to qL and qR — that branching is the whole point)
data Step : St → St → Set where
  p0→p1  : Step p0 p1
  p1→pB  : Step p1 pB
  p1→pC  : Step p1 pC
  q0→qL  : Step q0 qL
  q0→qR  : Step q0 qR
  qL→qLB : Step qL qLB
  qR→qRC : Step qR qRC

------------------------------------------------------------------------
-- The lived identity `≈` — bisimulation on a nondeterministic system:
-- equal observation, and every move of one is **matched** by a move of the
-- other into bisimilar states (forward and backward).

record _≈_ (x y : St) : Set where
  coinductive
  field
    obs≈ : obs x ≡ obs y
    fwd  : ∀ {x'} → Step x x' → Σ[ y' ∈ St ] (Step y y' × x' ≈ y')
    bwd  : ∀ {y'} → Step y y' → Σ[ x' ∈ St ] (Step x x' × x' ≈ y')
open _≈_

------------------------------------------------------------------------
-- Observational equality `≅` — the outside view: the same finite trace set.

data HasTrace : St → List Obs → Set where
  single : ∀ {x}      → HasTrace x (obs x ∷ [])
  cons   : ∀ {x x' w} → Step x x' → HasTrace x' w → HasTrace x (obs x ∷ w)

_≅_ : St → St → Set
x ≅ y = ∀ w → (HasTrace x w → HasTrace y w) × (HasTrace y w → HasTrace x w)

------------------------------------------------------------------------
-- Soundness: `≈ ⊆ ≅` — lived sameness ⇒ observed sameness. (Holds in any
-- model.) Bisimilar states realize the same traces, forward and backward,
-- by structural recursion on the (finite) trace, matching with `fwd`/`bwd`.

trace-fwd : ∀ {x y w} → x ≈ y → HasTrace x w → HasTrace y w
trace-fwd p single     = subst (λ o → HasTrace _ (o ∷ _)) (sym (obs≈ p)) single
trace-fwd p (cons s h) =
  let (y' , sy , q) = fwd p s
  in subst (λ o → HasTrace _ (o ∷ _)) (sym (obs≈ p)) (cons sy (trace-fwd q h))

trace-bwd : ∀ {x y w} → x ≈ y → HasTrace y w → HasTrace x w
trace-bwd p single     = subst (λ o → HasTrace _ (o ∷ _)) (obs≈ p) single
trace-bwd p (cons s h) =
  let (x' , sx , q) = bwd p s
  in subst (λ o → HasTrace _ (o ∷ _)) (obs≈ p) (cons sx (trace-bwd q h))

≈⇒≅ : ∀ {x y} → x ≈ y → x ≅ y
≈⇒≅ p w = trace-fwd p , trace-bwd p

------------------------------------------------------------------------
-- Strictness: the witness. `p0 ≅ q0` (same traces) but `¬ (p0 ≈ q0)`.

-- From outside, p0 and q0 are identical — same trace language. Agda's
-- dependent pattern matching does the trace inversion for us.
p0≅q0 : p0 ≅ q0
p0≅q0 w = f , g
  where
    f : ∀ {w'} → HasTrace p0 w' → HasTrace q0 w'
    f single                              = single
    f (cons p0→p1 single)                 = cons q0→qL single
    f (cons p0→p1 (cons p1→pB single))    = cons q0→qL (cons qL→qLB single)
    f (cons p0→p1 (cons p1→pC single))    = cons q0→qR (cons qR→qRC single)
    g : ∀ {w'} → HasTrace q0 w' → HasTrace p0 w'
    g single                              = single
    g (cons q0→qL single)                 = cons p0→p1 single
    g (cons q0→qL (cons qL→qLB single))   = cons p0→p1 (cons p1→pB single)
    g (cons q0→qR single)                 = cons p0→p1 single
    g (cons q0→qR (cons qR→qRC single))   = cons p0→p1 (cons p1→pC single)

-- From inside, they differ: p0's a-successor (p1) can do both b and c; neither
-- of q0's (qL, qR) can — so the move p0 ─a─▶ p1 cannot be matched.
¬p0≈q0 : ¬ (p0 ≈ q0)
¬p0≈q0 p with fwd p p0→p1
¬p0≈q0 p | qL , q0→qL , r with fwd r p1→pC
¬p0≈q0 p | qL , q0→qL , r | qLB , qL→qLB , r2 with obs≈ r2
¬p0≈q0 p | qL , q0→qL , r | qLB , qL→qLB , r2 | ()
¬p0≈q0 p | qR , q0→qR , r with fwd r p1→pB
¬p0≈q0 p | qR , q0→qR , r | qRC , qR→qRC , r2 with obs≈ r2
¬p0≈q0 p | qR , q0→qR , r | qRC , qR→qRC , r2 | ()

------------------------------------------------------------------------
-- **The inversion, in Agda.** `≈ ⊊ ≅`: soundness (`≈⇒≅`) gives `≈ ⊆ ≅`, and
-- the witness gives a `≅`-equal, `≈`-distinct pair — the first-person surplus.
-- Same theorem as Lean's `Identity.bisim_ne_obsEq`, now over a nondeterministic
-- system in Agda. (The deterministic collapse `≈ ⟺ ≅` of `RelExist.Coinductive`
-- is the boundary case: a clockwork, with no branches not taken, has no surplus.)
surplus : (p0 ≅ q0) × ¬ (p0 ≈ q0)
surplus = p0≅q0 , ¬p0≈q0
