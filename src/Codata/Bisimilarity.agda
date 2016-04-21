-- Abstract characterisation of bisimilarity as final coalgebra for
-- a relation transformer.
--
-- This allows us to prove properties of bisimilarity independently of
-- concrete coinductive types.
--
module Codata.Bisimilarity where

open import Level
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Transformer

-- Characterise a (bi)simulation as coalgebra for a relation transformer.
IsBisim : ∀ {a ℓ} {A : Set a} (Φ : Rt A A ℓ) → Rel A ℓ → Set _
IsBisim Φ R = R ⇒ Φ R

-- A bisimulation relation _~_ on a set A characterised as the largest
-- relation closed under by its characteristic transformation.
--
-- Note that _~_ does not necessarily has to be a bisimulation, it can
-- also be, for example, a simulation.

record Bisim a ℓ : Set (suc (a ⊔ ℓ)) where
  infix 4 _~_
  field
    Carrier : Set a
    _~_     : Rel Carrier ℓ
    CharRt  : Rt Carrier Carrier ℓ
    isMono  : Monotone CharRt
    isBisim : IsBisim CharRt _~_
    final   : {R : Rel Carrier ℓ} → IsBisim CharRt R → R ⇒ _~_
