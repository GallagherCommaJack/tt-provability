module Universes.Tarski where
open import lib

data U₀ : Set
U₀⇓ : U₀ → Set

data U₀ where
  σ : (A : U₀) → (U₀⇓ A → U₀) → U₀
  π : (A : U₀) → (U₀⇓ A → U₀) → U₀
  τ : U₀
  n₀ : U₀
  n₁ : U₀
  n₂ : U₀

U₀⇓ (σ u b) = Σ[ u⇓ ∈ U₀⇓ u ] U₀⇓ (b u⇓)
U₀⇓ (π u b) = Π (U₀⇓ u) (λ u⇓ → U₀⇓ (b u⇓))
U₀⇓ τ = Tree
U₀⇓ n₀ = ⊥
U₀⇓ n₁ = ⊤
U₀⇓ n₂ = Bool

data NextU (A : Set) (A⇓ : A → Set) : Set
NextU⇓ : (A : Set) (A⇓ : A → Set) → NextU A A⇓ → Set

data NextU A A⇓ where
  uu : NextU A A⇓
  up : A → NextU A A⇓
  πn : (a : NextU A A⇓) → (NextU⇓ A A⇓ a → NextU A A⇓) → NextU A A⇓
  σn : (a : NextU A A⇓) → (NextU⇓ A A⇓ a → NextU A A⇓) → NextU A A⇓

NextU⇓ A A⇓ uu = A
NextU⇓ A A⇓ (up x) = A⇓ x
NextU⇓ A A⇓ (πn u x) = (u⇓ : NextU⇓ A A⇓ u) → NextU⇓ A A⇓ (x u⇓)
NextU⇓ A A⇓ (σn u x) = Σ[ u⇓ ∈ NextU⇓ A A⇓ u ] NextU⇓ A A⇓ (x u⇓)

data SuperU : Set
SuperU⇓ : SuperU → Set

data SuperU where
  u₀ : SuperU
  nextU : (a : SuperU) → (b : SuperU⇓ a → SuperU) → SuperU
  nextT : (a : SuperU) → (b : SuperU⇓ a → SuperU) → SuperU⇓ (nextU a b) → SuperU
  π : (a : SuperU) → (SuperU⇓ a → SuperU) → SuperU
  σ : (a : SuperU) → (SuperU⇓ a → SuperU) → SuperU
  τ : SuperU
  n₀ : SuperU
  n₁ : SuperU
  n₂ : SuperU

SuperU⇓ u₀ = U₀
SuperU⇓ (nextU u b) = NextU (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓))
SuperU⇓ (nextT u b x) = NextU⇓ (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓)) x
SuperU⇓ (π u b) = Π (SuperU⇓ u) (λ u⇓ → SuperU⇓ (b u⇓))
SuperU⇓ (σ u b) = Σ[ u⇓ ∈ SuperU⇓ u ] SuperU⇓ (b u⇓)
SuperU⇓ τ = Tree
SuperU⇓ n₀ = ⊥
SuperU⇓ n₁ = ⊤
SuperU⇓ n₂ = Bool

U₀↑ : U₀ → SuperU
U₀↑-eq : ∀ u → SuperU⇓ (U₀↑ u) ≡ U₀⇓ u
U₀↑ (σ u b) = σ (U₀↑ u) (λ uₛ⇓ → U₀↑ (b (coe (U₀↑-eq u) uₛ⇓)))
U₀↑ (π u b) = π (U₀↑ u) (λ uₛ⇓ → U₀↑ (b (coe (U₀↑-eq u) uₛ⇓)))
U₀↑ τ = τ
U₀↑ n₀ = n₀
U₀↑ n₁ = n₁
U₀↑ n₂ = n₂

U₀↑-eq (σ u b) rewrite U₀↑-eq u | funext (λ u⇓ → U₀↑-eq (b u⇓)) = refl
U₀↑-eq (π u b) rewrite U₀↑-eq u = ap (Π $ U₀⇓ u) $ funext $ λ u⇓ → U₀↑-eq (b u⇓)
U₀↑-eq τ = refl
U₀↑-eq n₀ = refl
U₀↑-eq n₁ = refl
U₀↑-eq n₂ = refl

U : ℕ → SuperU
U zero = u₀
U (suc n) with U n
U (suc n) | nextU u b = nextU (nextU u b) (nextT u b)
U (suc n) | _ = nextU u₀ U₀↑

uNext : ∀ n → Σ[ u ∈ SuperU ] (Σ[ b ∈ (SuperU⇓ u → SuperU) ] (U (suc n) ≡ nextU u b))
uNext zero = u₀ , U₀↑ , refl
uNext (suc n) with uNext n
uNext (suc n) | u , b , p rewrite p = nextU u b , nextT u b , refl
