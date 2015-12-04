module WTLob where
open import Syntax.Typed.Def
open import lib renaming (id to idf)
open import Universes.Tarski

open import Data.Vec using (Vec)
open import Data.Vec as V
open import Data.Fin using (Fin)
open import Data.Fin as F

data Label : Set where
  top bot con ty tm : Label

I : Label → Set
I top = ⊤
I bot = ⊤
I con = ⊤
I ty = Con
I tm = Σ Con Ty

I↓ : ∀ ℓ → I ℓ → Set
I↓ top _ = ⊤
I↓ bot _ = ⊥
I↓ con _ = Con
I↓ ty Γ = Ty Γ
I↓ tm (Γ , T) = Tm Γ T

open U₀ (Σ Label I) (uncurry I↓)

open NextU U₀ ⟦_⟧₀

Con⇓ : Con → Set
Ty⇓ : ∀ {Γ} → Ty Γ → Con⇓ Γ → NextU
Tm⇓ : ∀ {Γ A} → Tm Γ A → (Γ⇓ : Con⇓ Γ) → ⟦ Ty⇓ A Γ⇓ ⟧ₙ
Tms⇓ : ∀ {Γ Δ} → Tms Γ Δ → Con⇓ Γ → Con⇓ Δ

Con⇓ ε = ⊤
Con⇓ (Γ ,, x) = Σ (Con⇓ Γ) (λ Γ⇓ → ⟦ Ty⇓ x Γ⇓ ⟧ₙ)

Ty⇓ (t [ x ]T) Γ⇓ = Ty⇓ t (Tms⇓ x Γ⇓)
Ty⇓ (‘Π’ t₁ t₂) Γ⇓ = πn (Ty⇓ t₁ Γ⇓) (λ t⇓ → Ty⇓ t₂ (Γ⇓ , t⇓))
Ty⇓ U Γ⇓ = uu
Ty⇓ (El A) Γ⇓ = up $ Tm⇓ A Γ⇓
Ty⇓ ‘top’ Γ⇓ = up $ ix (top , _)
Ty⇓ ‘bot’ Γ⇓ = up $ ix (bot , _)
Ty⇓ (‘□’ {Γ} T) Γ⇓ = up $ ix (tm , (Γ , T))

Tms⇓ ε Γ⇓ = tt
Tms⇓ (δ ,, x) Γ⇓ = Tms⇓ δ Γ⇓ , Tm⇓ x Γ⇓
Tms⇓ (π₁ δ) Γ⇓ = proj₁ (Tms⇓ δ Γ⇓)
Tms⇓ id Γ⇓ = Γ⇓
Tms⇓ (δ₂ ⊚ δ₁) Γ⇓ = Tms⇓ δ₂ (Tms⇓ δ₁ Γ⇓)

Tm⇓ (t [ δ ]t) Γ⇓ = Tm⇓ t (Tms⇓ δ Γ⇓)
Tm⇓ (π₂ δ) Γ⇓ = proj₂ (Tms⇓ δ Γ⇓)
Tm⇓ (app t) (Γ⇓ , A⇓) = Tm⇓ t Γ⇓ A⇓
Tm⇓ (lam t) Γ⇓ a = Tm⇓ t (Γ⇓ , a)
Tm⇓ ‘tt’ Γ⇓ = tt
Tm⇓ ‘⊥-rec’ Γ⇓ = λ ()
Tm⇓ ⌜ x ⌝ Γ⇓ = {!!}
Tm⇓ ⌜ t ⌝t Γ⇓ = t
Tm⇓ (Löb l) Γ⇓ = Tm⇓ l Γ⇓ (Löb l)

-- ⌞_⌟ : Ty ε → Set
-- ⌞ T ⌟ = Ty⇓ T _

-- _‘’_ : ∀ {Γ A} → Ty (Γ ,, A) → Tm Γ A → Ty Γ
-- f ‘’ x = f [ id ,, x [ id ]t ]T

-- löb : ∀ {‘X’} → Tm ε (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
-- löb f = Tm⇓ (Löb f) _

-- comp : ∀ {Γ X Y Z} → Tm Γ (Y ‘→’ Z) → Tm Γ (X ‘→’ Y) → Tm Γ (X ‘→’ Z)
-- comp g f = lam (app g [ wk ,, app f ]t)

-- fb-fb-cooperate : ∀ {Γ X Y} → Tm Γ (‘□’ X ‘→’ Y) → Tm Γ (‘□’ Y ‘→’ X) → Tm Γ X × Tm Γ Y
-- fb-fb-cooperate {Γ} {X} {Y} p1 p2 = Löb (comp p2 (lam ⌜ app p1 ⌝t)) , Löb (comp p1 (lam ⌜ app p2 ⌝t))
