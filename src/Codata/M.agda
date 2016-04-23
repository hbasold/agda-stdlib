------------------------------------------------------------------------
-- The Agda standard library
--
-- M-types (the dual of W-types) implemented with copatterns.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Codata.M where

open import Level
open import Size
open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Transformer
open import Codata.Simulations

-- The M-type for arbirtrary container.

record M {i : Size} {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  coinductive
  field out : ∀{j : Size< i} → Σ A (λ x → B x → M {j} A B)

open M public

-- Projections.

root : ∀ {i a b} {A : Set a} {B : A → Set b} →
       ∀ {j : Size< i} → M {i} A B → A
root x = proj₁ (out x)

branch : ∀ {i a b} {A : Set a} {B : A → Set b} →
       ∀{j : Size< i} → (x : M A B) → B (root x) → M A B
branch x = proj₂ (out x)

module Bisimilarity {ℓ}
       (S : Setoid ℓ ℓ)
       {B : Setoid.Carrier S → Set ℓ}
       (subst : Substitutive (Setoid._≈_ S) ℓ)
       where
  infix 4 _~_

  open Setoid S renaming (Carrier to A; isEquivalence to S-equiv)
  module SE = IsEquivalence S-equiv

  record _~_ {i : Size} (s t : M A B) : Set ℓ where
    coinductive
    field
      root≈ : root s ≈ root t
      branch~ : ∀{j : Size< i} →
                ∀ x → _~_ {j} (branch s x) (branch t (subst B root≈ x))

  open _~_ public

  -- | Relation transformer that characterises bisimulations
  Φ : Rt (M A B) (M A B) ℓ
  Φ R s t = Σ (root s ≈ root t) λ p →
            ∀ x → R (branch s x) (branch t (subst B p x))

  Φ-mono : Monotone Φ
  Φ-mono R⇒S (r≈ , bR) = (r≈ , (λ x → R⇒S (bR x)))

  ~-isSim : IsSim Φ _~_
  ~-isSim x~y = (root≈ x~y , branch~ x~y)

  -- | Bisimulation proof principle
  ∃-bisim→~ : ∀ {i R} → IsSim Φ R → {s t : M A B} → R s t → _~_ {i} s t
  root≈ (∃-bisim→~ R-isBisim q) = proj₁ (R-isBisim q)
  branch~ (∃-bisim→~ {i} {R} R-isBisim q) {j} x =
    ∃-bisim→~ {j} {R} R-isBisim (proj₂ (R-isBisim q) x)

  isSim : Sim _ _
  isSim = record
    { Carrier = M A B
    ; _≲_ = _~_
    ; CharRt = Φ
    ; isMono = Φ-mono
    ; isSim = ~-isSim
    ; final = ∃-bisim→~
    }

  -- The following needs some properties abou the setoid A. For example,
  -- we could really use subst P SE.refl b ≡ b... I am not sure what
  -- the best approach here is for now. So I leave it open.
  {-
  isBisim : EquivSim _
  isBisim = record
    { sim = isSim
    ; weak-refl-pres = λ {R} p {x} →
      (SE.refl
      , (λ y → let u = p {branch x y}
               in subst (λ t → R (branch x y) (branch x {!!})) {!!} {!!}))
    ; weak-flip-pres = λ p → (SE.sym (proj₁ p) , (λ x → {!!}))
    ; weak-comp-pres = λ {
      (_ , p , q) → (SE.trans (proj₁ p) (proj₁ q)
                    , {!!})
      }
    }

  M-setoid : Setoid _ _
  M-setoid = record
    { Carrier = M A B
    ; _≈_ = _~_
    ; isEquivalence = bisim-is-equiv isBisim
    }

  import Relation.Binary.EqReasoning as EqR

  module ~-Reasoning where
    module _ where
      open EqR (M-setoid) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _~⟨_⟩_; begin_ to begin_; _∎ to _∎)
  -}
