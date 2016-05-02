------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
------------------------------------------------------------------------

open import Relation.Binary

module Algebra.Structures where

import Algebra.FunctionProperties as FunctionProperties
open import Data.Product
open import Function
open import Level using (_⊔_)
import Relation.Binary.EqReasoning as EqR

open FunctionProperties using (Op₁; Op₂)

------------------------------------------------------------------------
-- One binary operation

record IsSemigroup {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                   (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    assoc         : Associative ∙
    ∙-cong        : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

  open IsEquivalence isEquivalence public

record IsMonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ) (∙ : Op₂ A) (ε : A)
                {{ isSemigroup : IsSemigroup ≈ ∙ }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

record IsCommutative {a ℓ} {A : Set a} (≈ : Rel A ℓ) (_∙_ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    comm        : Commutative _∙_

identityˡ+comm→monoid : ∀ {a ℓ} {A : Set a} {≈ : Rel A ℓ} {_∙_ : Op₂ A} {ε : A}
                          {{ isSemigroup : IsSemigroup ≈ _∙_ }} →
                          FunctionProperties.LeftIdentity ≈ ε _∙_ →
                          IsCommutative ≈ _∙_ →
                          IsMonoid ≈ _∙_ ε
identityˡ+comm→monoid {≈ = ≈} {_∙_} {ε} {{isSemigroup}} identityˡ isComm
  = record { identity = identity }
  where
    open IsSemigroup isSemigroup public
    open IsCommutative isComm public

    identity : _
    identity = (identityˡ , identityʳ)
      where
      open EqR (record { isEquivalence = isEquivalence })

      identityʳ : _
      identityʳ = λ x → begin
        (x ∙ ε)  ≈⟨ comm x ε ⟩
        (ε ∙ x)  ≈⟨ identityˡ x ⟩
        x        ∎

record IsGroup {a ℓ} {A : Set a} (≈ : Rel A ℓ)
               (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A)
               {{ isSemigroup : IsSemigroup ≈ _∙_ }}
               {{ isMonoid : IsMonoid ≈ _∙_ ε }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  infixl 7 _-_
  field
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : _⁻¹ Preserves ≈ ⟶ ≈

  open IsMonoid isMonoid public

  _-_ : FunctionProperties.Op₂ A
  x - y = x ∙ (y ⁻¹)

record IsAbelianGroup
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (∙ : Op₂ A) (ε : A) (⁻¹ : Op₁ A)
         {{ isSemigroup : IsSemigroup ≈ ∙ }}
         {{ isMonoid : IsMonoid ≈ ∙ ε }}
         {{ isCommutative : IsCommutative ≈ ∙ }}
         {{ isGroup : IsGroup ≈ ∙ ε ⁻¹ }} : Set (a ⊔ ℓ) where
  open IsCommutative isCommutative public
  open IsGroup isGroup public

------------------------------------------------------------------------
-- Two binary operations

record IsNearSemiring {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                      (+ * : Op₂ A) (0# : A)
                      {{ +-isSemigroup : IsSemigroup ≈ + }}
                      {{ +-isMonoid : IsMonoid ≈ + 0# }}
                      {{ *-isSemigroup : IsSemigroup ≈ * }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; identity    to +-identity
                  )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc    to *-assoc
                  ; ∙-cong   to *-cong
                  )

record IsSemiringWithoutOne {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                            (+ * : Op₂ A) (0# : A)
                            {{ +-isSemigroup : IsSemigroup ≈ + }}
                            {{ +-isMonoid : IsMonoid ≈ + 0# }}
                            {{ +-isCommutative : IsCommutative ≈ + }}
                            {{ *-isSemigroup : IsSemigroup ≈ * }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; identity    to +-identity
                  )

  open IsCommutative public
       renaming ( comm to +-comm )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  )

  isNearSemiring : IsNearSemiring ≈ + * 0#
  isNearSemiring = record
    { distribʳ      = proj₂ distrib
    ; zeroˡ         = proj₁ zero
    }

record IsSemiringWithoutAnnihilatingZero
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# 1# : A)
         {{ +-isSemigroup : IsSemigroup ≈ + }}
         {{ +-isMonoid : IsMonoid ≈ + 0# }}
         {{ +-isCommutative : IsCommutative ≈ + }}
         {{ *-isSemigroup : IsSemigroup ≈ * }}
         {{ *-isMonoid : IsMonoid ≈ * 1# }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    distrib               : * DistributesOver +

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; identity    to +-identity
                  )

  open IsCommutative +-isCommutative public
       renaming ( comm to +-comm )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; identity    to *-identity
                  )

record IsSemiring {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                  (+ * : Op₂ A) (0# 1# : A)
         {{ +-isSemigroup : IsSemigroup ≈ + }}
         {{ +-isMonoid : IsMonoid ≈ + 0# }}
         {{ +-isCommutative : IsCommutative ≈ + }}
         {{ *-isSemigroup : IsSemigroup ≈ * }}
         {{ *-isMonoid : IsMonoid ≈ * 1# }}
         {{ isSemiringWithoutAnnihilatingZero :
            IsSemiringWithoutAnnihilatingZero ≈ + * 0# 1# }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    zero : Zero 0# *

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  isSemiringWithoutOne : IsSemiringWithoutOne ≈ + * 0#
  isSemiringWithoutOne = record
    { distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
       using (isNearSemiring)

record IsCommutativeSemiringWithoutOne
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# : A)
         {{ +-isSemigroup : IsSemigroup ≈ + }}
         {{ +-isMonoid : IsMonoid ≈ + 0# }}
         {{ +-isCommutative : IsCommutative ≈ + }}
         {{ *-isSemigroup : IsSemigroup ≈ * }}
         {{ *-isCommutative : IsCommutative ≈ * }}
         {{ isSemiringWithoutOne : IsSemiringWithoutOne ≈ + * 0# }} : Set (a ⊔ ℓ) where

  open IsCommutative *-isCommutative public
    renaming (comm to *-comm)

  open IsSemiringWithoutOne isSemiringWithoutOne public

record IsCommutativeSemiring
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (0# 1# : A)
         {{ +-isSemigroup : IsSemigroup ≈ _+_ }}
         {{ +-isMonoid : IsMonoid ≈ _+_ 0# }}
         {{ +-isCommutative : IsCommutative ≈ _+_ }}
         {{ *-isSemigroup : IsSemigroup ≈ _*_ }}
         {{ *-isMonoid : IsMonoid ≈ _*_ 1# }}
         {{ *-isCommutative : IsCommutative ≈ _*_ }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    distribʳ              : _*_ DistributesOverʳ _+_
    zeroˡ                 : LeftZero 0# _*_

  private
    module +-CM = IsMonoid +-isMonoid
    module *-CM = IsMonoid *-isMonoid
    open IsCommutative *-isCommutative public
      renaming (comm to *-comm)
  open EqR (record { isEquivalence = +-CM.isEquivalence })

  distrib : _*_ DistributesOver _+_
  distrib = (distribˡ , distribʳ)
    where
    distribˡ : _*_ DistributesOverˡ _+_
    distribˡ x y z = begin
      (x * (y + z))        ≈⟨ *-comm x (y + z) ⟩
      ((y + z) * x)        ≈⟨ distribʳ x y z ⟩
      ((y * x) + (z * x))  ≈⟨ *-comm y x ⟨ +-CM.∙-cong ⟩ *-comm z x ⟩
      ((x * y) + (x * z))  ∎

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      (x * 0#)  ≈⟨ *-comm x 0# ⟩
      (0# * x)  ≈⟨ zeroˡ x ⟩
      0#        ∎

  isSemiringWithoutAnnihilatingZero :
    IsSemiringWithoutAnnihilatingZero ≈ _+_ _*_ 0# 1#
  isSemiringWithoutAnnihilatingZero = record { distrib = distrib }

  isSemiring : IsSemiring ≈ _+_ _*_ 0# 1#
               {{isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero}}
  isSemiring = record { zero = zero }

  open IsSemiring isSemiring public
         hiding (distrib; zero)

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne ≈ _+_ _*_ 0# {{isSemiringWithoutOne = isSemiringWithoutOne}}
  isCommutativeSemiringWithoutOne = record {}

record IsRing
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         {{ +-isSemigroup : IsSemigroup ≈ _+_ }}
         {{ +-isMonoid : IsMonoid ≈ _+_ 0# }}
         {{ +-isCommutative : IsCommutative ≈ _+_ }}
         {{ +-isGroup : IsGroup ≈ _+_ 0# -_ }}
         {{ +-isAbelianGroup : IsAbelianGroup ≈ _+_ 0# -_ }}
         {{ *-isSemigroup : IsSemigroup ≈ _*_ }}
         {{ *-isMonoid : IsMonoid ≈ _*_ 1# }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
         renaming ( assoc               to +-assoc
                  ; ∙-cong              to +-cong
                  ; identity            to +-identity
                  ; inverse             to -‿inverse
                  ; ⁻¹-cong             to -‿cong
                  ; comm                to +-comm
                  )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; identity    to *-identity
                  )

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    open EqR (record { isEquivalence = isEquivalence })

    zeroˡ : LeftZero 0# _*_
    zeroˡ x = begin
        (0# * x)                                ≈⟨ sym $ proj₂ +-identity _ ⟩
       ((0# * x) +            0#)               ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
       ((0# * x) + ((0# * x)  + (- (0# * x))))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      (((0# * x) +  (0# * x)) + (- (0# * x)))   ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
             (((0# + 0#) * x) + (- (0# * x)))   ≈⟨ (proj₂ +-identity _ ⟨ *-cong ⟩ refl)
                                                     ⟨ +-cong ⟩
                                                   refl ⟩
                    ((0# * x) + (- (0# * x)))   ≈⟨ proj₂ -‿inverse _ ⟩
                             0#                 ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      (x * 0#)                                ≈⟨ sym $ proj₂ +-identity _ ⟩
      ((x * 0#) + 0#)                         ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
      ((x * 0#) + ((x * 0#) + (- (x * 0#))))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      (((x * 0#) + (x * 0#)) + (- (x * 0#)))  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
      ((x * (0# + 0#)) + (- (x * 0#)))        ≈⟨ (refl ⟨ *-cong ⟩ proj₂ +-identity _)
                                                   ⟨ +-cong ⟩
                                                 refl ⟩
      ((x * 0#) + (- (x * 0#)))               ≈⟨ proj₂ -‿inverse _ ⟩
      0#                                      ∎

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero ≈ _+_ _*_ 0# 1#
  isSemiringWithoutAnnihilatingZero = record { distrib = distrib }

  isSemiring : IsSemiring ≈ _+_ _*_ 0# 1#
    {{isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero}}
  isSemiring = record { zero = zero }

  open IsSemiring isSemiring public
         using (isNearSemiring; isSemiringWithoutOne)

record IsCommutativeRing
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A)
         {{ +-isSemigroup : IsSemigroup ≈ + }}
         {{ +-isMonoid : IsMonoid ≈ + 0# }}
         {{ +-isCommutative : IsCommutative ≈ + }}
         {{ +-isGroup : IsGroup ≈ + 0# - }}
         {{ +-isAbelianGroup : IsAbelianGroup ≈ + 0# - }}
         {{ *-isSemigroup : IsSemigroup ≈ * }}
         {{ *-isMonoid : IsMonoid ≈ * 1# }}
         {{ isRing : IsRing ≈ + * - 0# 1# }}
         {{ *-isCommutative : IsCommutative ≈ * }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring ≈ + * 0# 1#
  isCommutativeSemiring = record
    { distribʳ              = proj₂ distrib
    ; zeroˡ                 = proj₁ zero
    }

record IsLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                 (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-cong        : ∨ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-cong        : ∧ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

record IsDistributiveLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                             (∨ ∧ : Op₂ A)
                             {{ isLattice : IsLattice ≈ ∨ ∧ }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    ∨-∧-distribʳ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A)
         {{ isLattice : IsLattice ≈ ∨ ∧ }}
         {{ isDistributiveLattice : IsDistributiveLattice ≈ ∨ ∧ }} : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-cong                : ¬ Preserves ≈ ⟶ ≈

  open IsDistributiveLattice isDistributiveLattice public
