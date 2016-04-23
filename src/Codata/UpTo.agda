-- In this module, we define compatible up-to techniques for simulations.
-- The purpose of up-to techniques is that they allow us to strengthen
-- the hypothesis we can use to prove that a relation is a (bi)simulation,
-- see IsSim-upto and compat-sound.
--
-- As specific case, we can show that the equivalence closure is compatible
-- for any equivalence simulation relation.
--
module Codata.UpTo where

open import Level renaming (suc to lsuc)
open import Function
open import Data.Product renaming (map to pmap)
open import Data.Nat
open import Relation.Binary
open import Relation.Binary.Transformer
open import Relation.Binary.EquivalenceClosure
open import Codata.Simulations

-- This record describes compatible up-to techniques. These have been desribed
-- by, for example, Pous, Bonchi, Rot and Petrisan.
--
-- C is the coinductive type under consideration, Φ the transformer
-- describing its bisimilarity and F the Φ-compatible up-to technique.
record Compat {a ℓ} (B : Sim a ℓ) : Set (lsuc (a Level.⊔ ℓ)) where
  C = Sim.Carrier B
  Φ = Sim.CharRt B
  field
    Tech : Rt C C ℓ
    isMono : Monotone Tech
    isCompat : ∀ {R} → Tech (Φ R) ⇒ Φ (Tech R)

-- Simulation up-to a given technique.
IsSim-upto : ∀{a ℓ} {B : Sim a ℓ} → Compat B →
               Rel (Sim.Carrier B) ℓ → Set _
IsSim-upto {B = B} C R = R ⇒ Φ (F R)
  where
    Φ = Sim.CharRt B
    F = Compat.Tech C

-- The following module contains everything we need to prove soundness
-- of compatibule up-to techniques, see compat-sound.
module _ where
  compat-pres-upto : ∀{a ℓ} {B : Sim a ℓ} (P : Compat B)
                     {R : Rel (Sim.Carrier B) ℓ} →
                     IsSim-upto P R → IsSim-upto P (Compat.Tech P R)
  compat-pres-upto P p = Compat.isCompat P ∘ (Compat.isMono P p)

  iterTrans : ∀{a ℓ} {A : Set a} → Rt A A ℓ → ℕ → Rt A A ℓ
  iterTrans F zero R = R
  iterTrans F (suc n) R = iterTrans F n (F R)

  -- Closure of up-to technique, which will be the the bisimulation we generate
  -- from it
  bisimCls : ∀{a ℓ} {A : Set a} → Rt A A ℓ → Rt A A ℓ
  bisimCls F R s t = ∃ λ n → iterTrans F n R s t

  bisimCls-steps : ∀{a ℓ} {A : Set a} {F : Rt A A ℓ} {R} →
                   ∀ n → iterTrans F n R ⇒ bisimCls F R
  bisimCls-steps n x = (n , x)

  bisimCls-steps₂ : ∀{a ℓ} {A : Set a} {F : Rt A A ℓ} {R} →
                    bisimCls F (F R) ⇒ bisimCls F R
  bisimCls-steps₂ (n , p) = (suc n , p)

  iterTrans-monotone : ∀{a ℓ} {A : Set a} {F : Rt A A ℓ} →
                       Monotone F → ∀ n → Monotone (iterTrans F n)
  iterTrans-monotone F-mon zero R⇒S x = R⇒S x
  iterTrans-monotone F-mon (suc n) R⇒S x =
    iterTrans-monotone F-mon n (F-mon R⇒S) x

  bisimCls-monotone : ∀{a ℓ} {A : Set a} {F : Rt A A ℓ} →
                      Monotone F → Monotone (bisimCls F)
  bisimCls-monotone q R⇒S (n , p) = (n , iterTrans-monotone q n R⇒S p)

  bisimCls-expanding : ∀{a ℓ} {A : Set a} {F : Rt A A ℓ} {R} →
                       R ⇒ bisimCls F R
  bisimCls-expanding x = bisimCls-steps 0 x

  bisimCls-compat : ∀{a ℓ} {B : Sim a ℓ} → (P : Compat B) →
    ∀{R} → bisimCls (Compat.Tech P) (Compat.Φ P R)
           ⇒ Compat.Φ P (bisimCls (Compat.Tech P) R)
  bisimCls-compat {B = B} P {R} (n , p) =
    ⇒-trans {S = Φ (iterTrans F n R)}
      (lem n)
      (Sim.isMono B (bisimCls-steps n))
      p
    where
      open Compat P renaming (Tech to F; isMono to F-mono; isCompat to F-compat)

      lem : ∀{R} → ∀ n → iterTrans F n (Φ R) ⇒ Φ (iterTrans F n R)
      lem zero = id
      lem {R} (suc n) =
        ⇒-trans {S = iterTrans F n (Φ (F R))}
          ((iterTrans-monotone {F = F} F-mono n F-compat))
          (lem {F R} n)

  clsIsSim : ∀{a ℓ} {B : Sim a ℓ} → (P : Compat B) →
             ∀ {R} → IsSim-upto P R →
             IsSim (Compat.Φ P) (bisimCls (Compat.Tech P) R)
  clsIsSim {B = B} P {R} p =
    ⇒-trans {S = bisimCls F (Φ (F R))}
      (bisimCls-monotone F-mono p)
      (⇒-trans {S = Φ (bisimCls F (F R))}
        (bisimCls-compat P)
        (Sim.isMono B bisimCls-steps₂))
    where
      open Compat P renaming (Tech to F; isMono to F-mono; isCompat to F-compat)

-- Compatible up-to techniques are sound for any simulation.
compat-sound : ∀{a ℓ} {B : Sim a ℓ} → (P : Compat B) →
  ∀ {R} → IsSim-upto P R → R ⇒ Sim._≲_ B
compat-sound {B = B} P {R} p xRy =
  Sim.final B (clsIsSim P p) (bisimCls-expanding xRy)

-- | Useful general up-to technique: the equivalence closure is compatible
-- for any equivalence-similarity transformer.
equivCls-compat : ∀{ℓ} (B : EquivSim ℓ) → Compat (EquivSim.sim B)
equivCls-compat B = record
  { Tech = EquivCls
  ; isMono = equivCls-monotone
  ; isCompat = compat
  }
  where
    open EquivSim B renaming (CharRt to Φ)
    open Sim sim renaming (isMono to Φ-mono)
    open IsEquivalence

    compat : ∀{R} → EquivCls (Φ R) ⇒ Φ (EquivCls R)
    compat (cls-incl xΦRy) = isMono equivCls-expanding xΦRy
    compat cls-refl = weak-refl-pres cls-refl
    compat (cls-sym p) = weak-flip-pres (Φ-mono cls-sym (compat p))
    compat {R} (cls-trans p q) =
      let p' = compat p
          q' = compat q
      in Φ-mono equivCls-trans-comp (weak-comp-pres (_ , p' , q'))
