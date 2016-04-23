------------------------------------------------------------------------
-- The Agda standard library
--
-- Build equivalence closure for arbitrary relations
--
------------------------------------------------------------------------

module Relation.Binary.EquivalenceClosure where

open import Level
open import Relation.Binary
open import Relation.Binary.Transformer
open import Data.Product

-- | Build equivalence closure
data EquivCls {a ℓ} {A : Set a} (R : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  cls-incl  : {x y : A} → R x y → EquivCls R x y
  cls-refl  : {y : A} → EquivCls R y y
  cls-sym   : {x y : A} → EquivCls R x y → EquivCls R y x
  cls-trans : {x y z : A} → EquivCls R x y → EquivCls R y z → EquivCls R x z

-- | The operation of taking the equivalence closure is monotone.
equivCls-monotone : ∀ {a ℓ} {A : Set a} → Monotone (EquivCls {a} {ℓ} {A})
equivCls-monotone R≤S (cls-incl xRy)  = cls-incl (R≤S xRy)
equivCls-monotone R≤S cls-refl        = cls-refl
equivCls-monotone R≤S (cls-sym p)     = cls-sym (equivCls-monotone R≤S p)
equivCls-monotone R≤S (cls-trans p q) =
  cls-trans (equivCls-monotone R≤S p) (equivCls-monotone R≤S q)

-- | The equivalence closure is indeed a closure operator.
equivCls-expanding : ∀{a ℓ} {A : Set a} {R} → R ⇒ EquivCls {a} {ℓ} {A} R
equivCls-expanding p = cls-incl p

-- | The equivalence closure is indeed a closure operator.
equivCls-idempotent : ∀{a ℓ} {A : Set a} {R} →
                      EquivCls (EquivCls R) ⇒ EquivCls {a} {ℓ} {A} R
equivCls-idempotent (cls-incl p)    = p
equivCls-idempotent cls-refl        = cls-refl
equivCls-idempotent (cls-sym p)     = cls-sym (equivCls-idempotent p)
equivCls-idempotent (cls-trans p q) =
  cls-trans (equivCls-idempotent p) (equivCls-idempotent q)

equivCls-trans-comp : ∀{a ℓ} {A : Set a} {R : Rel A ℓ} →
                      EquivCls R ⍮ EquivCls R ⇒ EquivCls R
equivCls-trans-comp (_ , p , q) = cls-trans p q

-- | Equivalence closure gives indeed equivalence relation
equivCls-equiv : ∀{a ℓ} {A : Set a} (R : Rel A ℓ) → IsEquivalence (EquivCls R)
equivCls-equiv R = record
  { refl  = cls-refl
  ; sym   = cls-sym
  ; trans = cls-trans
  }
