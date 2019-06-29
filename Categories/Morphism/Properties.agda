{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Morphism.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

open import Categories.Morphism 𝒞
open import Categories.Square 𝒞

private
  variable
    A B C : Obj
    f g h i : A ⇒ B

module _ (iso : Iso f g) where

  open Iso iso
  
  Iso-resp-≈ : f ≈ h → g ≈ i → Iso h i
  Iso-resp-≈ {h = h} {i = i} eq₁ eq₂ = record
    { isoˡ = begin
      i ∘ h ≈⟨ sym eq₂ ⟩∘⟨ sym eq₁ ⟩
      g ∘ f ≈⟨ isoˡ ⟩
      id    ∎
    ; isoʳ = begin
      h ∘ i ≈⟨ sym eq₁ ⟩∘⟨ sym eq₂ ⟩
      f ∘ g ≈⟨ isoʳ ⟩
      id    ∎
    }

  Iso-swap : Iso g f
  Iso-swap = record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  
  Iso⇒Mono : Mono f
  Iso⇒Mono h i eq = begin
    h           ≈⟨ introˡ isoˡ ⟩
    (g ∘ f) ∘ h ≈⟨ pullʳ eq ⟩
    g ∘ f ∘ i   ≈⟨ cancelˡ isoˡ ⟩
    i           ∎

  Iso⇒Epi : Epi f
  Iso⇒Epi h i eq = begin
    h           ≈⟨ introʳ isoʳ ⟩
    h ∘ f ∘ g   ≈⟨ pullˡ eq ⟩
    (i ∘ f) ∘ g ≈⟨ cancelʳ isoʳ ⟩
    i           ∎

Iso-∘ : Iso f g → Iso h i → Iso (h ∘ f) (g ∘ i)
Iso-∘ {f = f} {g = g} {h = h} {i = i} iso iso′ = record
  { isoˡ = begin
    (g ∘ i) ∘ h ∘ f ≈⟨ cancelInner (isoˡ iso′) ⟩
    g ∘ f           ≈⟨ isoˡ iso ⟩
    id              ∎
  ; isoʳ = begin
    (h ∘ f) ∘ g ∘ i ≈⟨ cancelInner (isoʳ iso) ⟩
    h ∘ i           ≈⟨ isoʳ iso′ ⟩
    id              ∎
  }
  where open Iso

Iso-≈ : f ≈ h → Iso f g → Iso h i → g ≈ i
Iso-≈ {f = f} {h = h} {g = g} {i = i} eq iso iso′ = begin
  g           ≈⟨ introˡ (isoˡ iso′) ⟩
  (i ∘ h) ∘ g ≈⟨ (refl ⟩∘⟨ sym eq) ⟩∘⟨refl ⟩
  (i ∘ f) ∘ g ≈⟨ pullʳ (isoʳ iso) ⟩
  i ∘ id      ≈⟨ identityʳ ⟩
  i           ∎
  where open Iso
