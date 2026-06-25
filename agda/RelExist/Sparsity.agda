{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- # Relational Existentialism — topological sparsity in the ν-layer (Agda)
--
-- **Step 4 of the sparsity proof strategy** ([spec 03 §3.5]) — the *topological*
-- form of the dichotomy, mechanized in the second proof assistant (the Layer-5 /
-- §5 ν-layer). The Lean development counts: under a finite attention budget the
-- carrier of selves `Stab` is finite, so its density `→ 0`
-- (`Scratch.SparsityReal.stab_density_tendsto_zero`). The spec's Conjecture 3.3
-- asks for the *infinite-state* form — that `Stab` is **nowhere dense** in the
-- space of states under "the natural topology on states `I → D`" — and §3.5
-- names Agda's coinductive ν-layer as the natural host, now that the categorical
-- infrastructure (`Cl(𝕋)`) it lifts into exists.
--
-- States are **behaviours in the final coalgebra** ([RelExist.Coinductive]); the
-- natural topology is the **cylinder topology** — basic opens are finite-prefix
-- determined. The looped selves (D1) are exactly the *constant* behaviours
-- `repeat a`. This module proves, over only the standard library:
--   * `Const ⟺ isSelf` — the topological "Stab" *is* the doctrine's self predicate;
--   * `nonConst-open`  — the non-selves are open, i.e. the selves are **closed**
--                        (constructively: their positive complement is open);
--   * `selves-emptyInterior` — every cylinder contains a non-self, so the selves
--                        have **empty interior**;
--   * `selves-nowhereDense` — hence (given two distinct observations) the selves
--                        are **nowhere dense** — sparsity, topological form;
--   * `trivial→allSelf` — the sharp dichotomy: a *trivial* observation alphabet
--                        makes **every** state a self (`Stab` dense), exactly as
--                        dropping the budget does (Lemma 3.2). Two distinct
--                        observations is the expressivity hypothesis; without it
--                        the theory is the universal solvent.
------------------------------------------------------------------------

module RelExist.Sparsity where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Rel; DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import RelExist.Coinductive

private variable A : Set

------------------------------------------------------------------------
-- The state space: behaviours, observed coordinate-by-coordinate.
-- `nth n x` is the n-th observation along x — the n-th coordinate of the state
-- as a point of `I → D` (here `I = ℕ`, the moments of observation).

nth : ℕ → Behaviour A → A
nth zero    x = obs x
nth (suc n) x = nth n (step x)

nth-repeat : ∀ n (b : A) → nth n (repeat b) ≡ b
nth-repeat zero    b = refl
nth-repeat (suc n) b = nth-repeat n b

------------------------------------------------------------------------
-- The self-set `Stab`, and its positive complement.
--
-- A behaviour is a **self** (D1: a looped, stationary self) when every later
-- observation repeats the first — i.e. it is the constant behaviour `repeat (obs x)`.
-- `NonConst` is the *positive* complement: a concrete moment that already differs.
-- Constructively this apartness, not the double negation `¬ Const`, is the open set.

Const : Behaviour A → Set
Const x = ∀ n → nth n x ≡ nth 0 x

NonConst : Behaviour A → Set
NonConst x = Σ ℕ λ n → nth n x ≢ nth 0 x

-- the two are genuine complements: pointwise opposite (the reverse direction is
-- where decidability enters — a moment is either equal or apart).
const→¬nonConst : {x : Behaviour A} → Const x → ¬ NonConst x
const→¬nonConst c (n , d) = d (c n)

¬nonConst→const : (_≟_ : DecidableEquality A) →
                  {x : Behaviour A} → ¬ NonConst x → Const x
¬nonConst→const _≟_ {x} ¬nc n with nth n x ≟ nth 0 x
... | yes e = e
... | no  d = ⊥-elim (¬nc (n , d))

------------------------------------------------------------------------
-- `Const` is exactly the doctrine's `isSelf` (Coinductive.agda) — so the
-- topological "Stab" is the very same set D1 calls the looped selves.

isSelf→Const : {x : Behaviour A} → isSelf x → Const x
isSelf→Const     s zero    = refl
isSelf→Const {x = x} s (suc n) =
  trans (isSelf→Const {x = step x} (step≈ s) n) (sym (obs≈ s))

-- `Const x` says x agrees with the constant behaviour at every coordinate — which
-- is exactly the lived identity (≈) unfolded. So a self *is* `repeat (obs x)`.
Const→≈repeat : {A : Set} {x : Behaviour A} → Const x → x ≈ repeat (obs x)
Const→≈repeat {A = A} {x = x} c =
  coinduction bisim λ n → trans (c n) (sym (nth-repeat n (obs x)))
  where
    R : Rel (Behaviour A) 0ℓ          -- agreement at every coordinate
    R u v = ∀ n → nth n u ≡ nth n v
    bisim : Bisimulation R
    obs-resp  bisim r = r 0
    step-resp bisim r = λ n → r (suc n)

Const→isSelf : {x : Behaviour A} → Const x → isSelf x
Const→isSelf {x = x} c = isSelf-≈ (Const→≈repeat c) (repeat-isSelf (obs x))

------------------------------------------------------------------------
-- The cylinder topology on the behaviour space.
--
-- A basic open (cylinder) is fixed by a finite observation prefix `p : List A`:
-- `agrees p x` says x's first `length p` observations are exactly `p`. A set is
-- `Open` when every point sits in a cylinder contained in the set.

agrees : List A → Behaviour A → Set
agrees []      _ = ⊤
agrees (a ∷ p) x = (nth 0 x ≡ a) × agrees p (step x)

Open : {A : Set} → (Behaviour A → Set) → Set
Open {A} U = ∀ {x} → U x → Σ (List A) λ p → agrees p x × (∀ {y} → agrees p y → U y)

-- the canonical prefix of length n read off x itself, and that x lies in it
prefix : ℕ → Behaviour A → List A
prefix zero    _ = []
prefix (suc n) x = nth 0 x ∷ prefix n (step x)

agrees-prefix : ∀ n (x : Behaviour A) → agrees (prefix n x) x
agrees-prefix zero    x = tt
agrees-prefix (suc n) x = refl , agrees-prefix n (step x)

-- anything agreeing with x's length-(suc n) prefix shares its 0-th and n-th
-- observations — the two coordinates the openness proof actually pins down.
prefix-agree : ∀ n {x y : Behaviour A} → agrees (prefix (suc n) x) y →
               (nth 0 y ≡ nth 0 x) × (nth n y ≡ nth n x)
prefix-agree zero    (e , _)        = e , e
prefix-agree (suc n) {x} {y} (e , r) = e , proj₂ (prefix-agree n {step x} {step y} r)

------------------------------------------------------------------------
-- **Closed.** The non-selves are open: a single moment of difference `nth n ≢ nth 0`
-- is witnessed by the length-(suc n) prefix, and *every* behaviour sharing that
-- prefix differs at the same two coordinates — so it too is a non-self. Hence the
-- selves `Const` are closed (their positive complement `NonConst` is open).

nonConst-open : {A : Set} → Open (NonConst {A})
nonConst-open {x = x} (n , d) =
    prefix (suc n) x
  , agrees-prefix (suc n) x
  , λ {y} ag → n , λ eq → d (trans (sym (proj₂ (prefix-agree n {x} {y} ag)))
                                    (trans eq (proj₁ (prefix-agree n {x} {y} ag))))

------------------------------------------------------------------------
-- A constant tail, used to escape any cylinder into a non-self.

prepend : List A → Behaviour A → Behaviour A
prepend []      s = s
obs  (prepend (a ∷ p) s) = a
step (prepend (a ∷ p) s) = prepend p s

agrees-prepend : ∀ (p : List A) (s : Behaviour A) → agrees p (prepend p s)
agrees-prepend []      s = tt
agrees-prepend (a ∷ p) s = refl , agrees-prepend p s

nth-length-prepend : ∀ (p : List A) (s : Behaviour A) →
                     nth (length p) (prepend p s) ≡ nth 0 s
nth-length-prepend []      s = refl
nth-length-prepend (a ∷ p) s = nth-length-prepend p s

------------------------------------------------------------------------
-- The non-triviality hypothesis: at least two distinct, decidable observations.
-- This is the expressivity condition — the topological avatar of `ε > 1` / a
-- discriminating alphabet. Under it the selves are nowhere dense.

module _ (_≟_ : DecidableEquality A) (a₀ a₁ : A) (a₀≢a₁ : a₀ ≢ a₁) where

  -- some observation provably different from a given one
  other : A → A
  other c with c ≟ a₀
  ... | yes _ = a₁
  ... | no  _ = a₀

  other-≢ : ∀ c → other c ≢ c
  other-≢ c with c ≟ a₀
  ... | yes e = λ eq → a₀≢a₁ (trans (sym e) (sym eq))
  ... | no ¬e = λ eq → ¬e (sym eq)

  -- a non-self inside an arbitrary cylinder: continue the prefix with a constant
  -- tail chosen to disagree with the prefix's first observation (empty prefix:
  -- emit a₀ then a₁… , already non-constant).
  witness : List A → Behaviour A
  witness []      = prepend (a₀ ∷ []) (repeat a₁)
  witness (c ∷ p) = prepend (c ∷ p)  (repeat (other c))

  -- **Empty interior.** No cylinder is contained in the selves: every basic open
  -- meets the non-selves. So `Const` has empty interior — no observation prefix,
  -- however long, forces selfhood.
  selves-emptyInterior : ∀ (p : List A) →
                         Σ (Behaviour A) λ x → agrees p x × NonConst x
  selves-emptyInterior [] =
      witness []
    , tt
    , (1 , λ eq → a₀≢a₁ (sym eq))
  selves-emptyInterior (c ∷ p) =
      witness (c ∷ p)
    , agrees-prepend (c ∷ p) (repeat (other c))
    , ( length (c ∷ p)
      , λ eq → other-≢ c (trans (sym (nth-length-prepend (c ∷ p) (repeat (other c)))) eq) )

  -- **Sparsity, topological form.** Closed + empty interior = nowhere dense.
  -- "Selves are an achievement" reading: the looped selves are a closed,
  -- nowhere-dense set — meagre among all behaviours.
  selves-nowhereDense :
      Open (NonConst {A})                                        -- closed
    × (∀ p → Σ (Behaviour A) λ x → agrees p x × NonConst x)      -- empty interior
  selves-nowhereDense = nonConst-open , selves-emptyInterior

------------------------------------------------------------------------
-- **The sharp dichotomy.** Remove the expressivity hypothesis — a *trivial*
-- observation alphabet (all observations equal) — and **every** behaviour is a
-- self: `Stab` is the whole space, dense, the theory says nothing. This is the
-- topological mirror of Lemma 3.2 (`β = ⊤ ⇒ Stab = Φ`, density 1): finiteness of
-- the alphabet's discriminating power is *necessary* for sparsity.

trivial→allSelf : (∀ (a b : A) → a ≡ b) → ∀ (x : Behaviour A) → Const x
trivial→allSelf triv x n = triv (nth n x) (nth 0 x)
