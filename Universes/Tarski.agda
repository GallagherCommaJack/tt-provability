{-# OPTIONS --rewriting #-}
module Universes.Tarski where
-- This file takes in a family of indexed types to serve as the concrete types for our universes
-- If you only want finitely many, just use Fin n and a Data.Vec
-- If for some reason you need infinitely many families of types (maybe you want all types of n-ary trees?) then you can have them

open import lib

module U₀ (I : Set) (⟦_⟧ᵢ : I → Set) where
  data U₀ : Set
  ⟦_⟧₀ : U₀ → Set

  data U₀ where
    π σ : (A : U₀) → (⟦ A ⟧₀ → U₀) → U₀
    ix : I → U₀
  ⟦ π a b ⟧₀ = (a⇓ : ⟦ a ⟧₀) → ⟦ b a⇓ ⟧₀
  ⟦ σ a b ⟧₀ = Σ ⟦ a ⟧₀ (λ a⇓ → ⟦ b a⇓ ⟧₀)
  ⟦ ix i ⟧₀ = ⟦ i ⟧ᵢ

module NextU (A : Set) (A⇓ : A → Set) where
  data NextU : Set
  ⟦_⟧ₙ : NextU → Set

  data NextU where
    uu : NextU
    up : A → NextU
    πn : (a : NextU) → (⟦ a ⟧ₙ → NextU) → NextU
    σn : (a : NextU) → (⟦ a ⟧ₙ → NextU) → NextU

  ⟦ uu ⟧ₙ = A
  ⟦ up x ⟧ₙ = A⇓ x
  ⟦ πn u x ⟧ₙ = (u⇓ : ⟦ u ⟧ₙ) → ⟦ x u⇓ ⟧ₙ
  ⟦ σn u x ⟧ₙ = Σ[ u⇓ ∈ ⟦ u ⟧ₙ ] ⟦ x u⇓ ⟧ₙ

  NextU⇓ = ⟦_⟧ₙ

module SuperU (I : Set) (⟦_⟧ᵢ : I → Set) where
  open U₀ I ⟦_⟧ᵢ
  open NextU

  data SuperU : Set
  SuperU⇓ : SuperU → Set

  data SuperU where
    u₀ : SuperU
    nextU : (a : SuperU) → (b : SuperU⇓ a → SuperU) → SuperU
    nextT : (a : SuperU) → (b : SuperU⇓ a → SuperU) → SuperU⇓ (nextU a b) → SuperU
    π : (a : SuperU) → (SuperU⇓ a → SuperU) → SuperU
    σ : (a : SuperU) → (SuperU⇓ a → SuperU) → SuperU
    ix : I → SuperU

  SuperU⇓ u₀ = U₀
  SuperU⇓ (nextU u b) = NextU (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓))
  SuperU⇓ (nextT u b x) = NextU⇓ (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓)) x
  SuperU⇓ (π u b) = Π (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓))
  SuperU⇓ (σ u b) = Σ[ u⇓ ∈ SuperU⇓ u ] SuperU⇓ (b u⇓)
  SuperU⇓ (ix i) = ⟦ i ⟧ᵢ

  U₀↑ : U₀ → SuperU
  U₀↑-eq : ∀ u → SuperU⇓ (U₀↑ u) ≡ ⟦ u ⟧₀
  U₀↑ (σ u b) = σ (U₀↑ u) (λ uₛ⇓ → U₀↑ (b (coe (U₀↑-eq u) uₛ⇓)))
  U₀↑ (π u b) = π (U₀↑ u) (λ uₛ⇓ → U₀↑ (b (coe (U₀↑-eq u) uₛ⇓)))
  U₀↑ (ix i) = ix i

  U₀↑-eq (σ u b) rewrite U₀↑-eq u | funext (λ u⇓ → U₀↑-eq (b u⇓)) = refl
  U₀↑-eq (π u b) rewrite U₀↑-eq u = ap (Π $ ⟦ u ⟧₀) $ funext $ λ u⇓ → U₀↑-eq (b u⇓)
  U₀↑-eq (ix i) = refl

  {-# REWRITE U₀↑-eq #-}

  U : ℕ → SuperU
  U zero = u₀
  U (suc n) with U n
  U (suc n) | nextU u b = nextU (nextU u b) (nextT u b)
  U (suc n) | _         = nextU u₀ U₀↑

  uNext : ∀ n → Σ[ u ∈ SuperU ] (Σ[ b ∈ (SuperU⇓ u → SuperU) ] (U (suc n) ≡ nextU u b))
  uNext zero = u₀ , U₀↑ , refl
  uNext (suc n) with uNext n
  uNext (suc n) | u , b , p rewrite p = nextU u b , nextT u b , refl
