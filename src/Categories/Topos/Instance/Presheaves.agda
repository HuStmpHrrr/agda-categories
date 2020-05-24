{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category

module Categories.Topos.Instance.Presheaves {o} (C : Category o o o) where

open import Data.Product

open import Categories.Topos
open import Categories.Category.CartesianClosed
open import Categories.Category.Complete.Finitely
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Properties.Presheaves
open import Categories.Diagram.SubobjectClassifier
open import Categories.Functor.Sieve
open import Categories.NaturalTransformation

open import Categories.Morphism

private
  module C = Category C

  P : Category (suc o) o o
  P = Presheaves′ o o C

  PC : FinitelyComplete P
  PC = Presheaves-FinitelyComplete C o o o o o

  module PC = FinitelyComplete PC

  PCCC : CartesianClosed P
  PCCC = IsCartesianClosed.Presheaves-CartesianClosed C

  module PCCC = CartesianClosed PCCC

  subobjectClassifier : SubobjectClassifier P
  subobjectClassifier = record
    { Ω         = SieveF C.op
    ; terminal  = PCCC.terminal
    ; true      = ntHelper record
      { η       = λ X → record
        { _⟨$⟩_ = λ _ → X , C.id
        ; cong  = λ _ → ≅.refl C.op , C.identity²
        }
      ; commute = λ f _ → {!!} , {!!}
      }
    ; universal = {!!}
    ; pullback  = PC.pullback _ _
    ; unique    = {!!}
    }

Presheaves-isTopos : IsTopos P
Presheaves-isTopos = record
  { cartesianClosed     = PCCC
  ; subobjectClassifier = subobjectClassifier
  ; equalizer           = PC.equalizer
  }

Presheaves-Topos : Topos (suc o) o o
Presheaves-Topos = record
  { underlying = P
  ; isTopos    = Presheaves-isTopos
  }
