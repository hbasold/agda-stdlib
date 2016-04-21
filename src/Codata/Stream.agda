{-# OPTIONS --copatterns --sized-types #-}

module Codata.Stream where

open import Level as Level using (zero)
open import Size
open import Function
open import Relation.Binary
open import Relation.Binary.Transformer
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning
open import Codata.Bisimilarity
open import Codata.UpTo

open import Data.List using (List; module List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (map to pmap)

-- Sized streams via head/tail.

record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : ∀ {j : Size< i} → Stream {j} A
open Stream public

-- | Tail on fully defined streams. This can simplify the use of tl
-- in higher order contexts.
tl' : ∀ {a} {A : Set a} → Stream A → Stream A
tl' s = tl s {∞}

-- | Corecursion
corec : ∀ {X A : Set} → (X → A) → (X → X) → (X → Stream A)
hd (corec h s x) = h x
tl (corec h s x) = corec h s (s x)

-- Functoriality.

map : ∀ {a i} {A B : Set a} (f : A → B) (s : Stream {i} A) → Stream {i} B
hd (map f s) = f (hd s)
tl (map f s) = map f (tl s)

-- Derivative
δ : ∀ {a} {A : Set a} → ℕ → Stream A → Stream A
δ 0       s = s
δ (suc n) s = δ n (tl s)

-- Indexing
_at_ : ∀ {a} {A : Set a} → Stream A → ℕ → A
s at n = hd (δ n s)

fromStr = _at_

-- | Inverse for at
toStr : ∀ {a} {A : Set a} → (ℕ → A) → Stream A
hd (toStr f) = f 0
tl (toStr f) = toStr (λ n → f (suc n))

-- | Element repetition
repeat : ∀{a} {A : Set a} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- Streams and lists.

-- Prepending a list to a stream.

_++ˢ_ : ∀ {a} {A : Set a} → List A → Stream A → Stream A
[]       ++ˢ s = s
(a ∷ as) ++ˢ s = a ∷ (as ++ˢ s)

-- Taking an initial segment of a stream.

takeˢ : ∀ {a} {A : Set a} (n : ℕ) (s : Stream A) → List A
takeˢ 0       s = []
takeˢ (suc n) s = hd s ∷ takeˢ n (tl s)

-- Notation for takeˢ.

_↓_ : ∀ {a} {A : Set a} (s : Stream A) (n : ℕ) → List A
s ↓ n = takeˢ n s

-- Implementation of the standard stream bisimilarity.
module Bisimilarity {a ℓ} (S : Setoid a ℓ) where

  infix 4 _~_

  open Setoid S renaming (Carrier to A; isEquivalence to S-equiv)
  module SE = IsEquivalence S-equiv

  -- Stream equality is bisimilarity
  record _~_ {i : Size} (s t : Stream A) : Set ℓ where
    coinductive
    field
      hd≈ : hd s ≈ hd t
      tl~ : ∀ {j : Size< i} → _~_ {j} (tl s) (tl t)
  open _~_ public

  _~[_]_ : Stream A → Size → Stream A → Set _
  s ~[ i ] t = _~_ {i} s t

  s-bisim-refl : ∀ {i} {s : Stream A} → s ~[ i ] s
  hd≈ s-bisim-refl               = SE.refl
  tl~ (s-bisim-refl {_} {s}) {j} = s-bisim-refl {j} {tl s}

  s-bisim-sym : ∀ {i} {s t : Stream A} → s ~[ i ] t → t ~[ i ] s
  hd≈ (s-bisim-sym             p)     = SE.sym (hd≈ p)
  tl~ (s-bisim-sym {_} {s} {t} p) {j} =
    s-bisim-sym {j} {tl s} {tl t} (tl~ p)

  s-bisim-trans : ∀ {i} {r s t : Stream A} →
                  r ~[ i ] s → s ~[ i ] t → r ~[ i ] t
  hd≈ (s-bisim-trans                 p q)     = SE.trans (hd≈ p) (hd≈ q)
  tl~ (s-bisim-trans {_} {r} {s} {t} p q) {j} =
    s-bisim-trans {j} {tl r} {tl s} {tl t} (tl~ p) (tl~ q)

  stream-setoid : Setoid _ _
  stream-setoid = record
    { Carrier = Stream A
    ; _≈_ = _~_
    ; isEquivalence = record
      { refl  = s-bisim-refl
      ; sym   = s-bisim-sym
      ; trans = s-bisim-trans
      }
    }

  import Relation.Binary.EqReasoning as EqR

  module ~-Reasoning where
    module _ where
      open EqR (stream-setoid) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _~⟨_⟩_; begin_ to begin_; _∎ to _∎)

  -- | As usual, bisimilarity implies equality at every index.
  bisim→ext-≡ : ∀ {s t : Stream A} → s ~ t → ∀ {n} → s at n ≈ t at n
  bisim→ext-≡ p {zero}  = hd≈ p
  bisim→ext-≡ p {suc n} = bisim→ext-≡ (tl~ p) {n}

  -- | Relation transformer that characterises bisimulations
  Φ : Rt (Stream A) (Stream A) ℓ
  Φ R s t = (hd s ≈ hd t) × R (tl s) (tl t)

  Φ-mono : Monotone Φ
  Φ-mono R⇒S (h≈ , tR) = (h≈ , R⇒S tR)

  ~-isBisim : IsBisim Φ _~_
  ~-isBisim x~y = (hd≈ x~y , tl~ x~y)

  -- | Bisimulation proof principle
  ∃-bisim→~ : ∀ {R} → IsBisim Φ R → {s t : Stream A} → R s t → s ~ t
  hd≈ (∃-bisim→~ R-isBisim q) = proj₁ (R-isBisim q)
  tl~ (∃-bisim→~ {R} R-isBisim q) =
    ∃-bisim→~ {R} R-isBisim (proj₂ (R-isBisim q))

  isBisim : Bisim _ _
  isBisim = record
              { Carrier = Stream A
              ; _~_ = _~_
              ; CharRt = Φ
              ; isMono = Φ-mono
              ; isBisim = ~-isBisim
              ; final = ∃-bisim→~
              }
