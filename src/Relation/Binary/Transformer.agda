------------------------------------------------------------------------
-- The Agda standard library
--
-- Relation transformers
--
-- TODO: Factor out into general module for n-ary relations, n ∈ ℕ
------------------------------------------------------------------------

module Relation.Binary.Transformer where

open import Level
open import Function
open import Data.Product
-- open import Relation.Nullary
open import Relation.Unary using (∅; U; ∁)
open import Relation.Binary

------------------------------------------------------------------------

-- Heterogeneous and homogeneous relation transformers

RT : ∀ {a b c d} → Set a → Set b → Set c → Set d → (ℓ₁ ℓ₂ : Level) → Set _
RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂ = REL A₁ A₂ ℓ₁ → REL B₁ B₂ ℓ₂

Rt : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set _
Rt A B ℓ = RT A B A B ℓ ℓ

-- Monotone operators

Monotone : ∀ {a b ℓ₁ ℓ₂} {A₁ A₂ : Set a} {B₁ B₂ : Set b} →
           RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂ → Set _
Monotone F = ∀ {R S} → R ⇒ S → F R ⇒ F S

-- Monotone relation transformations form a category.

id-monotone : ∀{a ℓ A B} → Monotone {a} (id {_} {REL A B ℓ})
id-monotone R⇒S = R⇒S

∘-pres-monotone : ∀ {a b c ℓ₁ ℓ₂ ℓ₃}
                    {A₁ A₂ : Set a} {B₁ B₂ : Set b} {C₁ C₂ : Set c} →
                    {G : RT B₁ B₂ C₁ C₂ ℓ₂ ℓ₃} {F : RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂} →
                    Monotone G → Monotone F → Monotone (G ∘ F)
∘-pres-monotone G-mon F-mon R⇒S xGFRy = G-mon (F-mon R⇒S) xGFRy

------------------------------------------------------------------------
-- Operations on predicates extend pointwise to predicate transformers

module _ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b} where

  -- The bottom and the top of the predicate transformer lattice.

  abort : RT A₁ A₂ B₁ B₂ zero zero
  abort = λ _ _ → ∅

  magic : RT A₁ A₂ B₁ B₂ zero zero
  magic = λ _ _ → U

  -- Negation.

  ∼_ : ∀ {ℓ₁ ℓ₂} → RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂ → RT A₁ A₂ B₁ B₂ ℓ₁ ℓ₂
  (∼ T) x = ∁ ∘ T x
