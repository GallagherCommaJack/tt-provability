module Syntax.Untyped.Interpreter where
open import lib
open import Syntax.Untyped.Def
open import Syntax.Untyped.Subst-Lemmas
open import Syntax.Untyped.Typing
open import Universes.Tarski

v-pred : ∀ {Γ n X Y} → var-rel (suc n) (Y ∷ Γ) X → var-rel n Γ (unw X)
v-pred (vs {X = X} p) rewrite unlift-lift 0 X = p

data is-good-con : Con → Set where
  ε : is-good-con []
  _,_ : ∀ {Γ X l} → is-good-con Γ → Γ ⊢ X ∈ typ l → is-good-con (X ∷ Γ)

good-con : Set
good-con = Σ Con is-good-con

con⇓ : good-con → Set
ty⇓ : ∀ {Γ n ty} → proj₁ Γ ⊢ ty ∈ typ n → con⇓ Γ → SuperU
tm⇓ : ∀ {Γ n ty tm} (pty : proj₁ Γ ⊢ ty ∈ typ n) → proj₁ Γ ⊢ tm ∈ ty → (Γ⇓ : con⇓ Γ) → SuperU⇓ (ty⇓ pty Γ⇓)

con⇓ ([] , ε) = ⊤
con⇓ (x ∷ Γ , pΓ , px) = Σ[ Γ⇓ ∈ con⇓ (Γ , pΓ) ] SuperU⇓ (ty⇓ px Γ⇓)

ty⇓ (t-typ {n}) Γ⇓ = U n
ty⇓ t-bot Γ⇓ = n₀
ty⇓ t-top Γ⇓ = n₁
ty⇓ {Γ , pΓ} (t-pi  pA pB) Γ⇓ = π (ty⇓ pA Γ⇓) (λ a⇓ → ty⇓ {_ , pΓ , pA} pB (Γ⇓ , a⇓))
ty⇓ {Γ , pΓ} (t-sig pA pB) Γ⇓ = σ (ty⇓ pA Γ⇓) (λ a⇓ → ty⇓ {_ , pΓ , pA} pB (Γ⇓ , a⇓))
ty⇓ {Γ , pΓ} {n} (t-pi1 {p} .{typ n} {B} pab) Γ⇓ = {!!}
ty⇓ (t-pi2 pab saB) Γ⇓ = {!!}
ty⇓ (t-app pf px sxB) Γ⇓ = {!!}
ty⇓ t-btr Γ⇓ = τ
ty⇓ {[] , ε} (t-var ()) Γ⇓
ty⇓ {x ∷ Γ , pΓ , px} {n} (t-var v) Γ⇓ = ⋆⋆TODO⋆⋆ -- I hate Agda sometimes
--ty⇓ (t-var (vz {X = typ n})) (Γ⇓ , x⇓) = {!!}
--ty⇓ {x ∷ Γ , pΓ , px} (t-var (vs i)) (Γ⇓ , x⇓) = {!!}
tm⇓ pty tm Γ⇓ = {!!}
-- ty⇓ {x ∷ Γ , (pΓ , px)} (t-var {zero} il) (Γ⇓ , x⇓) = ty⇓ px Γ⇓
-- ty⇓ {x ∷ Γ , (pΓ , px)} (t-var {suc i} il) (Γ⇓ , x⇓) = ty⇓ (t-var $ v-pred il) Γ⇓

-- tm⇓ pty tm Γ⇓ = {!!}
