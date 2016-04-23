-- Abstract characterisation of simulations as final coalgebra for
-- a relation transformer.
--
-- This allows us to prove properties of, for example, bisimilarity
-- independently of concrete coinductive types.
--
module Codata.Simulations where

open import Level
open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Transformer
open import Relation.Binary.PropositionalEquality

-- Characterise a (bi)simulation as coalgebra for a relation transformer.
IsSim : ∀ {a ℓ} {A : Set a} (Φ : Rt A A ℓ) → Rel A ℓ → Set _
IsSim Φ R = R ⇒ Φ R

-- A simulation relation _≲_ on a set A characterised as the largest
-- relation closed under by its characteristic transformation.
--
-- Note that _≲_ does not necessarily has to be a canonical simulation relation.
-- Also, does it have any order properties?

record Sim a ℓ : Set (suc (a ⊔ ℓ)) where
  infix 4 _≲_
  field
    Carrier : Set a
    _≲_     : Rel Carrier ℓ
    CharRt  : Rt Carrier Carrier ℓ
    isMono  : Monotone CharRt
    isSim   : IsSim CharRt _≲_
    final   : {R : Rel Carrier ℓ} → IsSim CharRt R → R ⇒ _≲_

Weak-Refl-Pres : ∀{a ℓ} {A : Set a} → Rt A A ℓ → Set _
Weak-Refl-Pres F = ∀{R} → (∀ {x} → R x x) → (∀ {x} → F R x x)

Weak-Flip-Pres : ∀{a ℓ} {A : Set a} → Rt A A ℓ → Set _
Weak-Flip-Pres F = ∀{R} → flip (F R) ⇒ F (flip R)

-- Weak pullback preservation
Weak-Comp-Pres : ∀{ℓ} {A : Set ℓ} → Rt A A ℓ → Set _
Weak-Comp-Pres F = ∀ {R S} → (F R) ⍮ (F S) ⇒ F (R ⍮ S)

-- Capture the extra properties on the relation transformer that allow
-- us to show that the relation is an equivalence.
record EquivSim ℓ : Set (suc ℓ) where
  field
    sim : Sim ℓ ℓ
    weak-refl-pres : Weak-Refl-Pres (Sim.CharRt sim)
    weak-flip-pres : Weak-Flip-Pres (Sim.CharRt sim)
    weak-comp-pres : Weak-Comp-Pres (Sim.CharRt sim)
  open Sim sim public renaming (_≲_ to _~_)

bisim-is-equiv : ∀{ℓ} → (B : EquivSim ℓ) → IsEquivalence (EquivSim._~_ B)
bisim-is-equiv B = record { refl = r ; sym = s ; trans = t }
  where
    open EquivSim B renaming (CharRt to Φ)

    r : Reflexive _~_
    r = final Δ-bisim refl
      where
        _Δ_ : Rel Carrier _
        _Δ_ = _≡_

        Δ-bisim : IsSim Φ _Δ_
        Δ-bisim refl = weak-refl-pres refl

    s : Symmetric _~_
    s x~y = final R-bisim x~y
      where
        R = flip _~_

        -- R = {(u,v) | v ~ u}
        -- R ⊆ Φ(R) ⇔ (∀ u R v ⇒ u Φ(R) v)
        -- But we have for ∀ u,v:
        -- v ~ u ⇒ v Φ(~) u ⇒ u (flip Φ(~)) v ⇒ u Φ(R) v
        R-bisim : IsSim Φ R
        R-bisim {x} {y} xRy = weak-flip-pres (isSim xRy)

    t : Transitive _~_
    t x~y y~z = final R-bisim (_ , x~y , y~z)
      where
        R : Rel _ _
        R = _~_ ⍮ _~_

        R-bisim : IsSim Φ R
        R-bisim {u} {v} (w , u~w , w~v) =
          let uΦ~w = isSim u~w
              wΦ~v = isSim w~v
          in weak-comp-pres (_ , uΦ~w , wΦ~v)
