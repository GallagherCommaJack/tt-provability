module WTLob where
open import Syntax.Typed.Def
open import lib

-- so missing Lean's calc environment right now...
-- or Coq's rewrite for that matter
-- ah hah! Agda has rewrite pragmas!

module löb-mod {Γ : Con} (X : Ty Γ) (f : Tm Γ (‘□’ Γ [ ‘’ₛ ⌜ X ⌝ ]T ‘→’ X)) where
  Hf : Ty (Γ , U)
  Hf = ‘□’ Γ [ wk1 {Γ} {U} {U} ∘ ‘’ₛ vz ]T ‘→’ X [ wk ]T

  H : Ty Γ
  H = Quine Hf

  H= : (Hf [ ‘’ₛ ⌜ Quine Hf ⌝ ]T)
     ≡ ((‘□’ Γ [ ‘’ₛ ⌜ Quine Hf ⌝ ]T ‘→’ X))
  H= = →SW1SV→W

  toH   : Tm Γ ((‘□’ Γ [ ‘’ₛ ⌜ H ⌝ ]T ‘→’ X) ‘→’ H)
  toH   = coe (TmΓ= (ap (λ t → t ‘→’ H) H=)) (quine← Hf)

  fromH : Tm Γ (H ‘→’ (‘□’ Γ [ ‘’ₛ ⌜ H ⌝ ]T ‘→’ X))
  fromH = coe (TmΓ= (ap (λ t → H ‘→’ t) H=)) (quine→ Hf)

  □H→□X : Tm Γ (‘□’ Γ [ ‘’ₛ ⌜ H ⌝ ]T ‘→’ ‘□’ Γ [ ‘’ₛ ⌜ X ⌝ ]T)
□H→□X = lam {!coe (λ s → Tm _ (‘□’ Γ [ s ]T))!}

  h : Tm Γ H
  h = {!!}

  Löb : Tm Γ X
  Löb = coe (TmΓ= {!!}) -- ack! another really ugly looking goal
        (app (app fromH [ ‘’ₛ h ]t) [ ‘’ₛ (coe (TmΓ= (ap (_[_]T (‘□’ Γ)) ((assoc ◾ ((ap (_∘_ _) (wk‘’ₛ h)) ◾ idr)) ⁻¹))) ⌜ h ⌝t) ]t)

Con⇓ : Con → Set
Ty⇓ : ∀ {Γ} → Ty Γ → Con⇓ Γ → Set
Tm⇓ : ∀ {Γ A} → Tm Γ A → (Γ⇓ : Con⇓ Γ) → Ty⇓ A Γ⇓
Tms⇓ : ∀ {Γ Δ} → Tms Γ Δ → Con⇓ Γ → Con⇓ Δ

Con⇓ ε = ⊤
Con⇓ (Γ , x) = Σ (Con⇓ Γ) (λ Γ⇓ → Ty⇓ x Γ⇓)
Ty⇓ (t [ x ]T) Γ⇓ = Ty⇓ t (Tms⇓ x Γ⇓)
Ty⇓ (Π dom cod) Γ⇓ = (a : Ty⇓ dom Γ⇓) → Ty⇓ cod (Γ⇓ , a)
Ty⇓ (U {Γ}) Γ⇓ = Ty Γ
Ty⇓ ‘top’ Γ⇓ = ⊤
Ty⇓ ‘bot’ Γ⇓ = ⊥
Ty⇓ (‘□’ Γ) Γ⇓ = Tm Γ (proj₂ Γ⇓)
Ty⇓ (Quine φ) Γ⇓ = Ty⇓ φ (Γ⇓ , Quine φ)
Ty⇓ (El x) Γ⇓ = Tm _ (Tm⇓ x Γ⇓)

Tms⇓ ε Γ⇓ = tt
Tms⇓ (δ , x) Γ⇓ = Tms⇓ δ Γ⇓ , Tm⇓ x Γ⇓
Tms⇓ (π₁ δ) Γ⇓ = proj₁ (Tms⇓ δ Γ⇓)
Tms⇓ id Γ⇓ = Γ⇓
Tms⇓ (δ₂ ∘ δ₁) Γ⇓ = Tms⇓ δ₂ (Tms⇓ δ₁ Γ⇓)

Tm⇓ (tm [ δ ]t) Γ⇓ = Tm⇓ tm (Tms⇓ δ Γ⇓)
Tm⇓ (π₂ δ) Γ⇓ = proj₂ (Tms⇓ δ Γ⇓)
Tm⇓ (app tm) (Γ⇓ , A⇓) = Tm⇓ tm Γ⇓ A⇓
Tm⇓ (lam tm) Γ⇓ a = Tm⇓ tm (Γ⇓ , a)
Tm⇓ ‘tt’ Γ⇓ = tt
Tm⇓ ‘⊥-rec’ Γ⇓ = λ ()
Tm⇓ ⌜ x ⌝ Γ⇓ = x
Tm⇓ ⌜ tm ⌝t Γ⇓ = tm
Tm⇓ (quine→ φ) Γ⇓ a = a
Tm⇓ (quine← φ) Γ⇓ a = a

-- ⌞_⌟ : Ty ε → Set
-- ⌞ T ⌟ = Ty⇓ T _

-- _‘’_ : ∀ {Γ A} → Ty (Γ , A) → Tm Γ A → Ty Γ
-- f ‘’ x = f [ id , x [ id ]t ]T

-- löb : ∀ {‘X’} → Tm ε ((‘□’ ε ‘’ ⌜ ‘X’ ⌝) ‘→’ ‘X’) → ⌞ ‘X’ ⌟
-- löb f = Tm⇓ (Löb f) _
