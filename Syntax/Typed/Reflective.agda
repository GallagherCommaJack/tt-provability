{-# OPTIONS --no-positivity-check #-}
module Syntax.Typed.Reflective where
open import lib

module Simple where
  data Con : Set
  data Ty : Set
  data _⊢_ (Γ : Con) : Ty → Set
  ⟦_⟧c : Con → Set
  ⟦_⟧t : Ty → Set
  Tm↓ : ∀ {Γ T} → Γ ⊢ T → ⟦ Γ ⟧c → ⟦ T ⟧t

  data Con where
    ε : Con
    _,_ : Con → Ty → Con

  data Ty where
    ⋆ : Ty
    _⟶_ : Ty → Ty → Ty
    con ty : Ty
    tm : ∀ {Γ} → Γ ⊢ con → Γ ⊢ ty → Ty

  ⟦ ε ⟧c = ⊤
  ⟦ Γ , x ⟧c = ⟦ Γ ⟧c × ⟦ x ⟧t
  ⟦ ⋆ ⟧t = ⊤
  ⟦ T₁ ⟶ T₂ ⟧t = ⟦ T₁ ⟧t → ⟦ T₂ ⟧t
  ⟦ con ⟧t = Con
  ⟦ ty ⟧t = Ty
  ⟦ tm {Γ} Δ T ⟧t = (Γ↓ : ⟦ Γ ⟧c) → Tm↓ Δ Γ↓ ⊢ Tm↓ T Γ↓

  data _⊢_ Γ where
    q-con : Con → Γ ⊢ con
    q-ty : Ty → Γ ⊢ ty
    q-tm : ∀ {Δ T} → ⟦ tm {Γ} Δ T ⟧t → Γ ⊢ tm Δ T

  Tm↓ (q-con x) Γ↓ = x
  Tm↓ (q-ty x) Γ↓ = x
  Tm↓ (q-tm x) Γ↓ = x

data Con : Set
data Ty (Γ : Con) : Set
data _⊢_ Γ : Ty Γ → Set
⟦_⟧c : Con → Set
Ty↓ : ∀ {Γ} → Ty Γ → Set
Tm↓ : ∀ {Γ T} → Γ ⊢ T → Ty↓ T

data Con where
  ε : Con
  _,_ : ∀ Γ → Ty Γ → Con

⟦ ε ⟧c = ⊤
⟦ Γ , x ⟧c = Σ ⟦ Γ ⟧c (λ Γ↓ → Ty↓ x)

data Ty Γ where
  con : Ty Γ
  ty : Γ ⊢ con → Ty Γ
  tm : (Δ : Γ ⊢ con) → Γ ⊢ ty Δ → Ty Γ

Ty↓ con = Con
Ty↓ (ty x) = Ty (Tm↓ x)
Ty↓ (tm Δ x) = Tm↓ Δ ⊢ Tm↓ x

data _⊢_ Γ where
  q-con : Con → Γ ⊢ con
  q-ty : ∀ {Δ} → Ty (Tm↓ Δ) → Γ ⊢ ty Δ
  q-tm : ∀ {Δ T} → Tm↓ Δ ⊢ Tm↓ T → Γ ⊢ (tm Δ T)
  
Tm↓ (q-con x) = x
Tm↓ (q-ty x) = x
Tm↓ (q-tm x) = x

