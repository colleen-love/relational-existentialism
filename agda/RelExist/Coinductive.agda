{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- # Relational Existentialism — the coinductive ν-layer (Agda)
--
-- Layer 5 of the formalization plan: a *second* proof assistant. The Lean
-- development mechanizes the doctrine's greatest-fixed-point modality `ν`
-- through `OrderHom.gfp` (Knaster–Tarski on a complete lattice). Agda hosts the
-- *same* content with **native coinduction** — coinductive records and
-- copatterns — which is the idiom the doctrine's ≈ (3.2) and looped self (D1)
-- were reaching for all along.
--
-- This module builds, from scratch (only the standard library):
--   * `Behaviour`   — a system as the final coalgebra of the observation functor;
--   * `_≈_`         — 3.2: the **lived identity** `≈` (the greatest bisimulation);
--   * `_≅_`         — **observational equality** (the bounded outside view: same
--                     observation stream), with the deterministic collapse `≈ ⟺ ≅`;
--   * `≈-refl/sym/trans`, `SharedWorld` — ≈ is an equivalence; `𝔼 := D/≈` is a Setoid;
--   * `coinduction` — the coinduction principle: every bisimulation is ⊆ ≈
--                     (≈ *is* the ν — proved by guarded corecursion, not a lattice);
--   * `fixpoint-isStationary` — D1: a fixed point of the dynamics is a stationary
--                     self (the eigenform νΦ), via the coinduction principle.
------------------------------------------------------------------------

module RelExist.Coinductive where

open import Level using (Level; 0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; cong)

private variable A : Set

------------------------------------------------------------------------
-- A system as a behaviour: the final coalgebra of the observation functor.
-- At each moment a system *exhibits* something observable and *steps* onward.
-- (This is the cartesian/relational shadow of the doctrine's systems-sort `D`.)

record Behaviour (A : Set) : Set where
  coinductive
  field
    obs  : A             -- what is observable now
    step : Behaviour A   -- the system, one moment on
open Behaviour public

------------------------------------------------------------------------
-- 3.2 — the **lived identity** `≈`, the GREATEST bisimulation.
--
-- Two systems share a lived identity when they agree now and stay so
-- forever. As a coinductive record this *is* the ν-closure: there is no
-- "construct a witness" — a proof of `x ≈ y` is an infinite, productive
-- agreement, exactly the final-coalgebra reading of the doctrine's ≈.
-- (`≡` here is propositional equality — the doctrine's literal `=`, the bare
-- carrier; `≈` is the lived identity built on top of it; `≅` below is the
-- coarser observed shadow.)

record _≈_ (x y : Behaviour A) : Set where
  coinductive
  field
    obs≈  : obs x ≡ obs y
    step≈ : step x ≈ step y
open _≈_ public

-- ≈ is reflexive, symmetric, transitive — each by copattern corecursion.
≈-refl : ∀ {x : Behaviour A} → x ≈ x
obs≈  ≈-refl = refl
step≈ ≈-refl = ≈-refl

≈-sym : ∀ {x y : Behaviour A} → x ≈ y → y ≈ x
obs≈  (≈-sym p) = ≡.sym (obs≈ p)
step≈ (≈-sym p) = ≈-sym (step≈ p)

≈-trans : ∀ {x y z : Behaviour A} → x ≈ y → y ≈ z → x ≈ z
obs≈  (≈-trans p q) = ≡.trans (obs≈ p) (obs≈ q)
step≈ (≈-trans p q) = ≈-trans (step≈ p) (step≈ q)

≈-isEquivalence : IsEquivalence (_≈_ {A})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

-- 𝔼 := D/≈ — the **shared world** (3.2): behaviours up to lived
-- identity, as a setoid. The "between" is the quotient, not the points.
SharedWorld : (A : Set) → Setoid 0ℓ 0ℓ
SharedWorld A = record
  { Carrier       = Behaviour A
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

------------------------------------------------------------------------
-- The coinduction principle — ≈ is the ν (the greatest bisimulation).
--
-- A bisimulation is any relation respecting observation and closed under
-- stepping. The principle says **every** bisimulation is contained in ≈: to
-- prove two systems share a lived identity (bisimilar), exhibit a bisimulation relating
-- them. Where Lean invokes `OrderHom.le_gfp`, here it is one guarded definition.

record Bisimulation (R : Rel (Behaviour A) 0ℓ) : Set where
  field
    obs-resp  : ∀ {x y} → R x y → obs x ≡ obs y
    step-resp : ∀ {x y} → R x y → R (step x) (step y)
open Bisimulation public

coinduction : ∀ {R : Rel (Behaviour A) 0ℓ} → Bisimulation R →
              ∀ {x y} → R x y → x ≈ y
obs≈  (coinduction B r) = obs-resp B r
step≈ (coinduction B r) = coinduction B (step-resp B r)

------------------------------------------------------------------------
-- Observational equality `≅` — the *outside* view — and the deterministic
-- collapse `≈ ⟺ ≅`.
--
-- `≅` compares only the **stream of observations**: `x ≅ y` iff `x` and `y`
-- exhibit the same observation at every depth. This is the bounded outside
-- observer of the Lean development (`Scratch/Identity.lean`, `ObsEq`). The
-- doctrine's three identities, used consistently across both proof assistants:
--   `≡`  literal equality (the bare carrier)   = Lean `=`
--   `≈`  bisimulation (the lived identity)      = Lean `We.bisim`
--   `≅`  observational equality (the shadow)    = Lean `Identity.ObsEq`
--
-- Because `Behaviour` is **deterministic** (a single `step`), here `≈` and `≅`
-- *coincide* — with no branching, the observation stream determines the system.
-- This is the **boundary case**: a clockwork, with no branches *not* taken, has
-- no first-person surplus. The doctrine's headline — the strict gap `≈ ⊊ ≅` — is
-- a **nondeterminism** phenomenon (the surplus is the trace of the branches not
-- taken), and it is proved in `RelExist.Inversion` (Agda) and
-- `Scratch/Identity.lean` (Lean), each over a nondeterministic system. So both
-- proof assistants now mechanize *both* facts: the gap (`Inversion` / `Identity`)
-- and the deterministic collapse here.

obsAt : ℕ → Behaviour A → A
obsAt zero    x = obs x
obsAt (suc n) x = obsAt n (step x)

-- observational equality: the same observation at every depth
_≅_ : Behaviour A → Behaviour A → Set
x ≅ y = ∀ n → obsAt n x ≡ obsAt n y

-- soundness — lived sameness ⇒ observed sameness (holds in any model)
≈⇒≅ : {x y : Behaviour A} → x ≈ y → x ≅ y
≈⇒≅ p zero    = obs≈ p
≈⇒≅ p (suc n) = ≈⇒≅ (step≈ p) n

-- completeness — observed sameness ⇒ lived sameness, **because deterministic**.
-- Guarded corecursion: the observation stream rebuilds the bisimulation.
≅⇒≈ : {x y : Behaviour A} → x ≅ y → x ≈ y
obs≈  (≅⇒≈ p) = p zero
step≈ (≅⇒≈ p) = ≅⇒≈ (λ n → p (suc n))

------------------------------------------------------------------------
-- D1 — the looped self: a fixed point of the dynamics is a stationary self.

-- the stationary system (one observation, forever)
repeat : A → Behaviour A
obs  (repeat a) = a
step (repeat a) = repeat a

-- the orbit of a dynamics `f` from a seed `a` (corecursion = the trace/feedback)
orbit : (A → A) → A → Behaviour A
obs  (orbit f a) = a
step (orbit f a) = orbit f (f a)

-- a system is a **self** when stepping leaves it unchanged up to lived identity
isSelf : Behaviour A → Set
isSelf x = x ≈ step x

repeat-isSelf : (a : A) → isSelf (repeat a)
repeat-isSelf a = ≈-refl

-- **The eigenform.** `f a ≡ a` ⇒ the orbit from `a` collapses to the stationary
-- self: a fixed point of the dynamics *is* a looped self (D1 / the eigenform
-- `νΦ`). Proved by the coinduction principle — exhibit the bisimulation that
-- relates the orbit to the stationary self, the iterates never leaving `a`.
fixpoint-isStationary : {f : A → A} {a : A} → f a ≡ a → orbit f a ≈ repeat a
fixpoint-isStationary {A = A} {f = f} {a = a} eq =
  coinduction bisim (refl , refl)
  where
    R : Rel (Behaviour A) 0ℓ
    R x y = (x ≡ orbit f a) × (y ≡ repeat a)
    bisim : Bisimulation R
    obs-resp  bisim (refl , refl) = refl
    step-resp bisim (refl , refl) = (cong (orbit f) eq , refl)

-- being a self is invariant under lived identity
isSelf-≈ : {x y : Behaviour A} → x ≈ y → isSelf y → isSelf x
isSelf-≈ p s = ≈-trans p (≈-trans s (≈-sym (step≈ p)))

-- Hence the fixed point itself is a self (it is ≈ the stationary self).
fixpoint-isSelf : {f : A → A} {a : A} → f a ≡ a → isSelf (orbit f a)
fixpoint-isSelf {a = a} eq = isSelf-≈ (fixpoint-isStationary eq) (repeat-isSelf a)
