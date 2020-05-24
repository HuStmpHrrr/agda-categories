{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Sieve {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product

open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C

open Category C
open HomReasoning

Sieve : Obj → Set (o ⊔ ℓ)
Sieve X = Σ Obj λ Y → Y ⇒ X

SieveF : Functor C (Setoids (o ⊔ ℓ) (ℓ ⊔ e))
SieveF = record
  { F₀           = λ X → record
    { Carrier       = Sieve X
    ; _≈_           = λ { (A , f) (B , g) → Σ (A ≅ B) λ h → g ∘ _≅_.from h ≈ f }
    ; isEquivalence = record
      { refl  = ≅.refl , identityʳ
      ; sym   = λ { (h , eq) → ≅.sym h , ⟺ (switch-fromtoʳ h eq) }
      ; trans = λ { (i , eq) (j , eq′) → ≅.trans i j , (pullˡ eq′ ○ eq) }
      }
    }
  ; F₁           = λ f → record
    { _⟨$⟩_ = λ { (Y , g) → Y , f ∘ g }
    ; cong  = λ { (h , eq) → h , pullʳ eq }
    }
  ; identity     = λ { (h , eq) → h , (eq ○ ⟺ identityˡ) }
  ; homomorphism = λ { (h , eq) → h , (pull-last eq ○ sym-assoc) }
  ; F-resp-≈     = λ { eq (h , eq′) → h , ((pullʳ eq′) ○ ∘-resp-≈ˡ (⟺ eq)) }
  }
