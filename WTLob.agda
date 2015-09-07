module WTLob where
open import Syntax.Typed.Def
open import lib renaming (id to idf)

Con⇓ : Con → Set
Ty⇓ : ∀ {Γ} → Ty Γ → Con⇓ Γ → Set
Tm⇓ : ∀ {Γ A} → Tm Γ A → (Γ⇓ : Con⇓ Γ) → Ty⇓ A Γ⇓
Tms⇓ : ∀ {Γ Δ} → Tms Γ Δ → Con⇓ Γ → Con⇓ Δ

Con⇓ ε = ⊤
Con⇓ (Γ ,, x) = Σ (Con⇓ Γ) (λ Γ⇓ → Ty⇓ x Γ⇓)

Ty⇓ (t [ x ]T) Γ⇓ = Ty⇓ t (Tms⇓ x Γ⇓)
Ty⇓ (‘Π’ dom cod) Γ⇓ = (a : Ty⇓ dom Γ⇓) → Ty⇓ cod (Γ⇓ , a)
Ty⇓ (U {Γ}) Γ⇓ = Ty Γ
Ty⇓ ‘top’ Γ⇓ = ⊤
Ty⇓ ‘bot’ Γ⇓ = ⊥
Ty⇓ (‘□’ T) Γ⇓ = Tm _ T
Ty⇓ (El x) Γ⇓ = Tm _ (Tm⇓ x Γ⇓) -- El ⌜ X ⌝ and □ are secretly the same thing?

Tms⇓ ε Γ⇓ = tt
Tms⇓ (δ ,, x) Γ⇓ = Tms⇓ δ Γ⇓ , Tm⇓ x Γ⇓
Tms⇓ (π₁ δ) Γ⇓ = proj₁ (Tms⇓ δ Γ⇓)
Tms⇓ id Γ⇓ = Γ⇓
Tms⇓ (δ₂ ⊚ δ₁) Γ⇓ = Tms⇓ δ₂ (Tms⇓ δ₁ Γ⇓)

Tm⇓ (tm [ δ ]t) Γ⇓ = Tm⇓ tm (Tms⇓ δ Γ⇓)
Tm⇓ (π₂ δ) Γ⇓ = proj₂ (Tms⇓ δ Γ⇓)
Tm⇓ (app tm) (Γ⇓ , A⇓) = Tm⇓ tm Γ⇓ A⇓
Tm⇓ (lam tm) Γ⇓ a = Tm⇓ tm (Γ⇓ , a)
Tm⇓ ‘tt’ Γ⇓ = tt
Tm⇓ ‘⊥-rec’ Γ⇓ = λ ()
Tm⇓ ⌜ x ⌝ Γ⇓ = x
Tm⇓ ⌜ tm ⌝t Γ⇓ = tm
Tm⇓ (Löb l) Γ⇓ = Tm⇓ l Γ⇓ (Löb l)

⌞_⌟ : Ty ε → Set
⌞ T ⌟ = Ty⇓ T _

_‘’_ : ∀ {Γ A} → Ty (Γ ,, A) → Tm Γ A → Ty Γ
f ‘’ x = f [ id ,, x [ id ]t ]T

löb : ∀ {‘X’} → Tm ε (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
löb f = Tm⇓ (Löb f) _
