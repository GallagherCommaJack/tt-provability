{-# OPTIONS --without-K #-}
module Syntax.Untyped.EqDec where
open import Syntax.Untyped.Def
open import lib

typ-inj : ∀ {n m} → typ n ≡ typ m → n ≡ m
typ-inj refl = refl

pi-inj : ∀ {A B A' B'} → pi A B ≡ pi A' B' → A ≡ A' × B ≡ B'
pi-inj refl = refl , refl

lam-inj : ∀ {A b A' b'} → lam A b ≡ lam A' b' → A ≡ A' × b ≡ b'
lam-inj refl = refl , refl

sig-inj : ∀ {A B A' B'} → sig A B ≡ sig A' B' → A ≡ A' × B ≡ B'
sig-inj refl = refl , refl


smk-inj : ∀ {a b a' b'} → smk a b ≡ smk a' b' → a ≡ a' × b ≡ b'
smk-inj refl = refl , refl

pi1-inj : ∀ {e e'} → pi1 e ≡ pi1 e' → e ≡ e'
pi1-inj refl = refl

pi2-inj : ∀ {e e'} → pi2 e ≡ pi2 e' → e ≡ e'
pi2-inj refl = refl

app-inj : ∀ {f x f' x'} → f ⊛ x ≡ f' ⊛ x' → f ≡ f' × x ≡ x'
app-inj refl = refl , refl

brc-inj : ∀ {l r l' r'} → l ⊕ r ≡ l' ⊕ r' → l ≡ l' × r ≡ r'
brc-inj refl = refl , refl

ind-inj : ∀ {P lc bc P' lc' bc'} → ind P lc bc ≡ ind P' lc' bc' → P ≡ P' × lc ≡ lc' × bc ≡ bc'
ind-inj refl = refl , refl , refl

exf-inj : ∀ {X X'} → exf X ≡ exf X' → X ≡ X'
exf-inj refl = refl

var-inj : ∀ {i i'} → * i ≡ * i' → i ≡ i'
var-inj refl = refl

ptm-dec : ∀ (p q : Ptm) → Dec (p ≡ q)
ptm-dec (typ l1) (typ l2) with l1 ≟ l2
ptm-dec (typ l1) (typ .l1) | yes refl = yes refl
ptm-dec (typ l1) (typ l2) | no ¬p = no (¬p ∘ typ-inj)
ptm-dec bot bot = yes refl
ptm-dec top top = yes refl
ptm-dec unt unt = yes refl
ptm-dec (pi  A₁ B₁) (pi  A₂ B₂) with ptm-dec A₁ A₂
ptm-dec (pi A₁ B₁) (pi A₂ B₂) | yes p with ptm-dec B₁ B₂
ptm-dec (pi A₁ B₁) (pi .A₁ .B₁) | yes refl | yes refl = yes refl
ptm-dec (pi A₁ B₁) (pi A₂ B₂) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ pi-inj)
ptm-dec (pi A₁ B₁) (pi A₂ B₂) | no ¬p = no (¬p ∘ proj₁ ∘ pi-inj)
ptm-dec (lam A₁ b₁) (lam A₂ b₂) with ptm-dec A₁ A₂
ptm-dec (lam A₁ b₁) (lam A₂ b₂) | yes p with ptm-dec b₁ b₂
ptm-dec (lam A₁ b₁) (lam .A₁ .b₁) | yes refl | yes refl = yes refl
ptm-dec (lam A₁ b₁) (lam A₂ b₂) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ lam-inj)
ptm-dec (lam A₁ b₁) (lam A₂ b₂) | no ¬p = no (¬p ∘ proj₁ ∘ lam-inj)
ptm-dec (sig A₁ B₁) (sig A₂ B₂) with ptm-dec A₁ A₂
ptm-dec (sig A₁ B₁) (sig A₂ B₂) | yes p with ptm-dec B₁ B₂
ptm-dec (sig A₁ B₁) (sig .A₁ .B₁) | yes refl | yes refl = yes refl
ptm-dec (sig A₁ B₁) (sig A₂ B₂) | yes p | no ¬p = no (λ z → ¬p (proj₂ (sig-inj z))) -- this was when I stopped filling it in by hand
ptm-dec (sig A₁ B₁) (sig A₂ B₂) | no ¬p = no (λ z → ¬p (proj₁ (sig-inj z)))
ptm-dec (smk a₁ b₁) (smk a₂ b₂) with ptm-dec a₁ a₂
ptm-dec (smk a₁ b₁) (smk a₂ b₂) | yes p with ptm-dec b₁ b₂
ptm-dec (smk a₁ b₁) (smk .a₁ .b₁) | yes refl | yes refl = yes refl
ptm-dec (smk a₁ b₁) (smk a₂ b₂) | yes p | no ¬p = no (λ z → ¬p (proj₂ (smk-inj z)))
ptm-dec (smk a₁ b₁) (smk a₂ b₂) | no ¬p = no (λ z → ¬p (proj₁ (smk-inj z)))
ptm-dec (pi1 e₁) (pi1 e₂) with ptm-dec e₁ e₂
ptm-dec (pi1 e₁) (pi1 .e₁) | yes refl = yes refl
ptm-dec (pi1 e₁) (pi1 e₂) | no ¬p = no (λ z → ¬p (pi1-inj z))
ptm-dec (pi2 e₁) (pi2 e₂) with ptm-dec e₁ e₂
ptm-dec (pi2 e₁) (pi2 .e₁) | yes refl = yes refl
ptm-dec (pi2 e₁) (pi2 e₂) | no ¬p = no (λ z → ¬p (pi2-inj z))
ptm-dec (f₁ ⊛ x₁) (f₂ ⊛ x₂) with ptm-dec f₁ f₂
ptm-dec (f₁ ⊛ x₁) (f₂ ⊛ x₂) | yes p with ptm-dec x₁ x₂
ptm-dec (f₁ ⊛ x₁) (.f₁ ⊛ .x₁) | yes refl | yes refl = yes refl
ptm-dec (f₁ ⊛ x₁) (f₂ ⊛ x₂) | yes p | no ¬p = no (λ z → ¬p (proj₂ (app-inj z)))
ptm-dec (f₁ ⊛ x₁) (f₂ ⊛ x₂) | no ¬p = no (λ z → ¬p (proj₁ (app-inj z)))
ptm-dec τ τ = yes refl
ptm-dec ℓ ℓ = yes refl
ptm-dec (l₁ ⊕ r₁) (l₂ ⊕ r₂) with ptm-dec l₁ l₂
ptm-dec (l₁ ⊕ r₁) (l₂ ⊕ r₂) | yes p with ptm-dec r₁ r₂
ptm-dec (l₁ ⊕ r₁) (.l₁ ⊕ .r₁) | yes refl | yes refl = yes refl
ptm-dec (l₁ ⊕ r₁) (l₂ ⊕ r₂) | yes p | no ¬p = no (λ z → ¬p (proj₂ (brc-inj z)))
ptm-dec (l₁ ⊕ r₁) (l₂ ⊕ r₂) | no ¬p = no (λ z → ¬p (proj₁ (brc-inj z)))
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) with ptm-dec P₁ P₂
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) | yes p with ptm-dec lc₁ lc₂
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) | yes p | yes q with ptm-dec bc₁ bc₂
ptm-dec (ind P₁ lc₁ bc₁) (ind .P₁ .lc₁ .bc₁) | yes refl | yes refl | yes refl = yes refl
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) | yes p | yes q | no ¬p = no (λ z → ¬p (proj₂ (proj₂ (ind-inj z))))
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) | yes p | no ¬p = no (λ z → ¬p (proj₁ (proj₂ (ind-inj z))))
ptm-dec (ind P₁ lc₁ bc₁) (ind P₂ lc₂ bc₂) | no ¬p = no (λ z → ¬p (proj₁ (ind-inj z)))
ptm-dec (exf X₁) (exf X₂) with ptm-dec X₁ X₂
ptm-dec (exf X₁) (exf .X₁) | yes refl = yes refl
ptm-dec (exf X₁) (exf X₂) | no ¬p = no (λ z → ¬p (exf-inj z))
ptm-dec (* i₁) (* i₂) with i₁ ≟ i₂
ptm-dec (* i₁) (* .i₁) | yes refl = yes refl
ptm-dec (* i₁) (* i₂) | no ¬p = no (λ z → ¬p (var-inj z))
ptm-dec (typ x) bot = no λ ()
ptm-dec (typ x) top = no λ ()
ptm-dec (typ x) unt = no λ ()
ptm-dec (typ x) (pi q q₁) = no λ ()
ptm-dec (typ x) (lam q q₁) = no λ ()
ptm-dec (typ x) (sig q q₁) = no λ ()
ptm-dec (typ x) (smk q q₁) = no λ ()
ptm-dec (typ x) (pi1 q) = no λ ()
ptm-dec (typ x) (pi2 q) = no λ ()
ptm-dec (typ x) (q ⊛ q₁) = no λ ()
ptm-dec (typ x) τ = no λ ()
ptm-dec (typ x) ℓ = no λ ()
ptm-dec (typ x) (q ⊕ q₁) = no λ ()
ptm-dec (typ x) (ind q q₁ q₂) = no λ ()
ptm-dec (typ x) (exf q) = no λ ()
ptm-dec (typ x) (* x₁) = no λ ()
ptm-dec bot (typ x) = no λ ()
ptm-dec bot top = no λ ()
ptm-dec bot unt = no λ ()
ptm-dec bot (pi q q₁) = no λ ()
ptm-dec bot (lam q q₁) = no λ ()
ptm-dec bot (sig q q₁) = no λ ()
ptm-dec bot (smk q q₁) = no λ ()
ptm-dec bot (pi1 q) = no λ ()
ptm-dec bot (pi2 q) = no λ ()
ptm-dec bot (q ⊛ q₁) = no λ ()
ptm-dec bot τ = no λ ()
ptm-dec bot ℓ = no λ ()
ptm-dec bot (q ⊕ q₁) = no λ ()
ptm-dec bot (ind q q₁ q₂) = no λ ()
ptm-dec bot (exf q) = no λ ()
ptm-dec bot (* x) = no λ ()
ptm-dec top (typ x) = no λ ()
ptm-dec top bot = no λ ()
ptm-dec top unt = no λ ()
ptm-dec top (pi q q₁) = no λ ()
ptm-dec top (lam q q₁) = no λ ()
ptm-dec top (sig q q₁) = no λ ()
ptm-dec top (smk q q₁) = no λ ()
ptm-dec top (pi1 q) = no λ ()
ptm-dec top (pi2 q) = no λ ()
ptm-dec top (q ⊛ q₁) = no λ ()
ptm-dec top τ = no λ ()
ptm-dec top ℓ = no λ ()
ptm-dec top (q ⊕ q₁) = no λ ()
ptm-dec top (ind q q₁ q₂) = no λ ()
ptm-dec top (exf q) = no λ ()
ptm-dec top (* x) = no λ ()
ptm-dec unt (typ x) = no λ ()
ptm-dec unt bot = no λ ()
ptm-dec unt top = no λ ()
ptm-dec unt (pi q q₁) = no λ ()
ptm-dec unt (lam q q₁) = no λ ()
ptm-dec unt (sig q q₁) = no λ ()
ptm-dec unt (smk q q₁) = no λ ()
ptm-dec unt (pi1 q) = no λ ()
ptm-dec unt (pi2 q) = no λ ()
ptm-dec unt (q ⊛ q₁) = no λ ()
ptm-dec unt τ = no λ ()
ptm-dec unt ℓ = no λ ()
ptm-dec unt (q ⊕ q₁) = no λ ()
ptm-dec unt (ind q q₁ q₂) = no λ ()
ptm-dec unt (exf q) = no λ ()
ptm-dec unt (* x) = no λ ()
ptm-dec (pi p p₁) (typ x) = no λ ()
ptm-dec (pi p p₁) bot = no λ ()
ptm-dec (pi p p₁) top = no λ ()
ptm-dec (pi p p₁) unt = no λ ()
ptm-dec (pi p p₁) (lam q q₁) = no λ ()
ptm-dec (pi p p₁) (sig q q₁) = no λ ()
ptm-dec (pi p p₁) (smk q q₁) = no λ ()
ptm-dec (pi p p₁) (pi1 q) = no λ ()
ptm-dec (pi p p₁) (pi2 q) = no λ ()
ptm-dec (pi p p₁) (q ⊛ q₁) = no λ ()
ptm-dec (pi p p₁) τ = no λ ()
ptm-dec (pi p p₁) ℓ = no λ ()
ptm-dec (pi p p₁) (q ⊕ q₁) = no λ ()
ptm-dec (pi p p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (pi p p₁) (exf q) = no λ ()
ptm-dec (pi p p₁) (* x) = no λ ()
ptm-dec (lam p p₁) (typ x) = no λ ()
ptm-dec (lam p p₁) bot = no λ ()
ptm-dec (lam p p₁) top = no λ ()
ptm-dec (lam p p₁) unt = no λ ()
ptm-dec (lam p p₁) (pi q q₁) = no λ ()
ptm-dec (lam p p₁) (sig q q₁) = no λ ()
ptm-dec (lam p p₁) (smk q q₁) = no λ ()
ptm-dec (lam p p₁) (pi1 q) = no λ ()
ptm-dec (lam p p₁) (pi2 q) = no λ ()
ptm-dec (lam p p₁) (q ⊛ q₁) = no λ ()
ptm-dec (lam p p₁) τ = no λ ()
ptm-dec (lam p p₁) ℓ = no λ ()
ptm-dec (lam p p₁) (q ⊕ q₁) = no λ ()
ptm-dec (lam p p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (lam p p₁) (exf q) = no λ ()
ptm-dec (lam p p₁) (* x) = no λ ()
ptm-dec (sig p p₁) (typ x) = no λ ()
ptm-dec (sig p p₁) bot = no λ ()
ptm-dec (sig p p₁) top = no λ ()
ptm-dec (sig p p₁) unt = no λ ()
ptm-dec (sig p p₁) (pi q q₁) = no λ ()
ptm-dec (sig p p₁) (lam q q₁) = no λ ()
ptm-dec (sig p p₁) (smk q q₁) = no λ ()
ptm-dec (sig p p₁) (pi1 q) = no λ ()
ptm-dec (sig p p₁) (pi2 q) = no λ ()
ptm-dec (sig p p₁) (q ⊛ q₁) = no λ ()
ptm-dec (sig p p₁) τ = no λ ()
ptm-dec (sig p p₁) ℓ = no λ ()
ptm-dec (sig p p₁) (q ⊕ q₁) = no λ ()
ptm-dec (sig p p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (sig p p₁) (exf q) = no λ ()
ptm-dec (sig p p₁) (* x) = no λ ()
ptm-dec (smk p p₁) (typ x) = no λ ()
ptm-dec (smk p p₁) bot = no λ ()
ptm-dec (smk p p₁) top = no λ ()
ptm-dec (smk p p₁) unt = no λ ()
ptm-dec (smk p p₁) (pi q q₁) = no λ ()
ptm-dec (smk p p₁) (lam q q₁) = no λ ()
ptm-dec (smk p p₁) (sig q q₁) = no λ ()
ptm-dec (smk p p₁) (pi1 q) = no λ ()
ptm-dec (smk p p₁) (pi2 q) = no λ ()
ptm-dec (smk p p₁) (q ⊛ q₁) = no λ ()
ptm-dec (smk p p₁) τ = no λ ()
ptm-dec (smk p p₁) ℓ = no λ ()
ptm-dec (smk p p₁) (q ⊕ q₁) = no λ ()
ptm-dec (smk p p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (smk p p₁) (exf q) = no λ ()
ptm-dec (smk p p₁) (* x) = no λ ()
ptm-dec (pi1 p) (typ x) = no λ ()
ptm-dec (pi1 p) bot = no λ ()
ptm-dec (pi1 p) top = no λ ()
ptm-dec (pi1 p) unt = no λ ()
ptm-dec (pi1 p) (pi q q₁) = no λ ()
ptm-dec (pi1 p) (lam q q₁) = no λ ()
ptm-dec (pi1 p) (sig q q₁) = no λ ()
ptm-dec (pi1 p) (smk q q₁) = no λ ()
ptm-dec (pi1 p) (pi2 q) = no λ ()
ptm-dec (pi1 p) (q ⊛ q₁) = no λ ()
ptm-dec (pi1 p) τ = no λ ()
ptm-dec (pi1 p) ℓ = no λ ()
ptm-dec (pi1 p) (q ⊕ q₁) = no λ ()
ptm-dec (pi1 p) (ind q q₁ q₂) = no λ ()
ptm-dec (pi1 p) (exf q) = no λ ()
ptm-dec (pi1 p) (* x) = no λ ()
ptm-dec (pi2 p) (typ x) = no λ ()
ptm-dec (pi2 p) bot = no λ ()
ptm-dec (pi2 p) top = no λ ()
ptm-dec (pi2 p) unt = no λ ()
ptm-dec (pi2 p) (pi q q₁) = no λ ()
ptm-dec (pi2 p) (lam q q₁) = no λ ()
ptm-dec (pi2 p) (sig q q₁) = no λ ()
ptm-dec (pi2 p) (smk q q₁) = no λ ()
ptm-dec (pi2 p) (pi1 q) = no λ ()
ptm-dec (pi2 p) (q ⊛ q₁) = no λ ()
ptm-dec (pi2 p) τ = no λ ()
ptm-dec (pi2 p) ℓ = no λ ()
ptm-dec (pi2 p) (q ⊕ q₁) = no λ ()
ptm-dec (pi2 p) (ind q q₁ q₂) = no λ ()
ptm-dec (pi2 p) (exf q) = no λ ()
ptm-dec (pi2 p) (* x) = no λ ()
ptm-dec (p ⊛ p₁) (typ x) = no λ ()
ptm-dec (p ⊛ p₁) bot = no λ ()
ptm-dec (p ⊛ p₁) top = no λ ()
ptm-dec (p ⊛ p₁) unt = no λ ()
ptm-dec (p ⊛ p₁) (pi q q₁) = no λ ()
ptm-dec (p ⊛ p₁) (lam q q₁) = no λ ()
ptm-dec (p ⊛ p₁) (sig q q₁) = no λ ()
ptm-dec (p ⊛ p₁) (smk q q₁) = no λ ()
ptm-dec (p ⊛ p₁) (pi1 q) = no λ ()
ptm-dec (p ⊛ p₁) (pi2 q) = no λ ()
ptm-dec (p ⊛ p₁) τ = no λ ()
ptm-dec (p ⊛ p₁) ℓ = no λ ()
ptm-dec (p ⊛ p₁) (q ⊕ q₁) = no λ ()
ptm-dec (p ⊛ p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (p ⊛ p₁) (exf q) = no λ ()
ptm-dec (p ⊛ p₁) (* x) = no λ ()
ptm-dec τ (typ x) = no λ ()
ptm-dec τ bot = no λ ()
ptm-dec τ top = no λ ()
ptm-dec τ unt = no λ ()
ptm-dec τ (pi q q₁) = no λ ()
ptm-dec τ (lam q q₁) = no λ ()
ptm-dec τ (sig q q₁) = no λ ()
ptm-dec τ (smk q q₁) = no λ ()
ptm-dec τ (pi1 q) = no λ ()
ptm-dec τ (pi2 q) = no λ ()
ptm-dec τ (q ⊛ q₁) = no λ ()
ptm-dec τ ℓ = no λ ()
ptm-dec τ (q ⊕ q₁) = no λ ()
ptm-dec τ (ind q q₁ q₂) = no λ ()
ptm-dec τ (exf q) = no λ ()
ptm-dec τ (* x) = no λ ()
ptm-dec ℓ (typ x) = no λ ()
ptm-dec ℓ bot = no λ ()
ptm-dec ℓ top = no λ ()
ptm-dec ℓ unt = no λ ()
ptm-dec ℓ (pi q q₁) = no λ ()
ptm-dec ℓ (lam q q₁) = no λ ()
ptm-dec ℓ (sig q q₁) = no λ ()
ptm-dec ℓ (smk q q₁) = no λ ()
ptm-dec ℓ (pi1 q) = no λ ()
ptm-dec ℓ (pi2 q) = no λ ()
ptm-dec ℓ (q ⊛ q₁) = no λ ()
ptm-dec ℓ τ = no λ ()
ptm-dec ℓ (q ⊕ q₁) = no λ ()
ptm-dec ℓ (ind q q₁ q₂) = no λ ()
ptm-dec ℓ (exf q) = no λ ()
ptm-dec ℓ (* x) = no λ ()
ptm-dec (p ⊕ p₁) (typ x) = no λ ()
ptm-dec (p ⊕ p₁) bot = no λ ()
ptm-dec (p ⊕ p₁) top = no λ ()
ptm-dec (p ⊕ p₁) unt = no λ ()
ptm-dec (p ⊕ p₁) (pi q q₁) = no λ ()
ptm-dec (p ⊕ p₁) (lam q q₁) = no λ ()
ptm-dec (p ⊕ p₁) (sig q q₁) = no λ ()
ptm-dec (p ⊕ p₁) (smk q q₁) = no λ ()
ptm-dec (p ⊕ p₁) (pi1 q) = no λ ()
ptm-dec (p ⊕ p₁) (pi2 q) = no λ ()
ptm-dec (p ⊕ p₁) (q ⊛ q₁) = no λ ()
ptm-dec (p ⊕ p₁) τ = no λ ()
ptm-dec (p ⊕ p₁) ℓ = no λ ()
ptm-dec (p ⊕ p₁) (ind q q₁ q₂) = no λ ()
ptm-dec (p ⊕ p₁) (exf q) = no λ ()
ptm-dec (p ⊕ p₁) (* x) = no λ ()
ptm-dec (ind p p₁ p₂) (typ x) = no λ ()
ptm-dec (ind p p₁ p₂) bot = no λ ()
ptm-dec (ind p p₁ p₂) top = no λ ()
ptm-dec (ind p p₁ p₂) unt = no λ ()
ptm-dec (ind p p₁ p₂) (pi q q₁) = no λ ()
ptm-dec (ind p p₁ p₂) (lam q q₁) = no λ ()
ptm-dec (ind p p₁ p₂) (sig q q₁) = no λ ()
ptm-dec (ind p p₁ p₂) (smk q q₁) = no λ ()
ptm-dec (ind p p₁ p₂) (pi1 q) = no λ ()
ptm-dec (ind p p₁ p₂) (pi2 q) = no λ ()
ptm-dec (ind p p₁ p₂) (q ⊛ q₁) = no λ ()
ptm-dec (ind p p₁ p₂) τ = no λ ()
ptm-dec (ind p p₁ p₂) ℓ = no λ ()
ptm-dec (ind p p₁ p₂) (q ⊕ q₁) = no λ ()
ptm-dec (ind p p₁ p₂) (exf q) = no λ ()
ptm-dec (ind p p₁ p₂) (* x) = no λ ()
ptm-dec (exf p) (typ x) = no λ ()
ptm-dec (exf p) bot = no λ ()
ptm-dec (exf p) top = no λ ()
ptm-dec (exf p) unt = no λ ()
ptm-dec (exf p) (pi q q₁) = no λ ()
ptm-dec (exf p) (lam q q₁) = no λ ()
ptm-dec (exf p) (sig q q₁) = no λ ()
ptm-dec (exf p) (smk q q₁) = no λ ()
ptm-dec (exf p) (pi1 q) = no λ ()
ptm-dec (exf p) (pi2 q) = no λ ()
ptm-dec (exf p) (q ⊛ q₁) = no λ ()
ptm-dec (exf p) τ = no λ ()
ptm-dec (exf p) ℓ = no λ ()
ptm-dec (exf p) (q ⊕ q₁) = no λ ()
ptm-dec (exf p) (ind q q₁ q₂) = no λ ()
ptm-dec (exf p) (* x) = no λ ()
ptm-dec (* x) (typ x₁) = no λ ()
ptm-dec (* x) bot = no λ ()
ptm-dec (* x) top = no λ ()
ptm-dec (* x) unt = no λ ()
ptm-dec (* x) (pi q q₁) = no λ ()
ptm-dec (* x) (lam q q₁) = no λ ()
ptm-dec (* x) (sig q q₁) = no λ ()
ptm-dec (* x) (smk q q₁) = no λ ()
ptm-dec (* x) (pi1 q) = no λ ()
ptm-dec (* x) (pi2 q) = no λ ()
ptm-dec (* x) (q ⊛ q₁) = no λ ()
ptm-dec (* x) τ = no λ ()
ptm-dec (* x) ℓ = no λ ()
ptm-dec (* x) (q ⊕ q₁) = no λ ()
ptm-dec (* x) (ind q q₁ q₂) = no λ ()
ptm-dec (* x) (exf q) = no λ ()
