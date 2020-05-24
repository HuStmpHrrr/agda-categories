{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Topos where

open import Level

open import Categories.Category.CartesianClosed
open import Categories.Category.Complete.Finitely
open import Categories.Diagram.Equalizer
open import Categories.Diagram.SubobjectClassifier

import Categories.Category.Complete.Finitely.Properties as Fₚ

record IsTopos {o ℓ e} (C : Category o ℓ e) : Set (levelOfTerm C) where
  open Category C
  field
    cartesianClosed     : CartesianClosed C
    subobjectClassifier : SubobjectClassifier C
    equalizer           : ∀ {A B} (f g : A ⇒ B) → Equalizer C f g

  finitelyComplete : FinitelyComplete C
  finitelyComplete = record
    { cartesian = CartesianClosed.cartesian cartesianClosed
    ; equalizer = equalizer
    }

  open FinitelyComplete finitelyComplete using (module equalizer; pullback) public

  open Fₚ finitelyComplete using (finiteLimit) public

record Topos o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    underlying : Category o ℓ e
    isTopos    : IsTopos underlying

  open Category underlying public
  open IsTopos isTopos public
