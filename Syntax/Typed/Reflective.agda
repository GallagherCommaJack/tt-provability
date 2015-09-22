module Syntax.Typed.Reflective where
open import lib


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

