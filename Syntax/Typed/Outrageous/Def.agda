{-# OPTIONS --without-K #-}
module Syntax.Typed.Outrageous.Def where
open import Universes.Tarski
open import lib hiding (_∋_)

infixr 4 _‘→’_
_‘→’_ : U₀ → U₀ → U₀
lhs ‘→’ rhs = π lhs λ _ → rhs

El = U₀⇓
fst = proj₁
snd = proj₂
if = if_then_else_

data Con : Set
[_]ᶜ : Con → Set

Ty : Con → Set
Ty Γ = [ Γ ]ᶜ → U₀

data Con where
  ε : Con
  _,_ : ∀ Γ → Ty Γ → Con

[ ε ]ᶜ = ⊤
[ Γ , x ]ᶜ = Σ [ Γ ]ᶜ λ Γ⇓ → El (x Γ⇓)

dropC : ℕ → Con → Con
dropC zero Γ = Γ
dropC (suc n) ε = ε
dropC (suc n) (Γ , x) = dropC n Γ

insertC : ∀ n Γ → Ty (dropC n Γ) → Con
liftT : ∀ n Γ t → Ty Γ → Ty (insertC n Γ t)

insertC zero Γ t = Γ , t
insertC (suc n) ε t = ε , t
insertC (suc n) (Γ , x) t = insertC n Γ t , liftT n Γ t x

liftT zero Γ t x = x ∘ proj₁
liftT (suc n) ε t x = x ∘ proj₁
liftT (suc n) (Γ , X) t x (Γ⇓ , X⇓) = {!!}

infix 3 _∋_
data _∋_ : ∀ Γ → Ty Γ → Set where
  top : ∀ {Γ T}           → Γ , T ∋ T ∘ fst
  pop : ∀ {Γ S T} → Γ ∋ T → Γ , S ∋ T ∘ fst

[_]ᵛ : ∀{Γ T} → Γ ∋ T → (Γ⇓ : [ Γ ]ᶜ) → El (T Γ⇓)
[ top   ]ᵛ (γ , x) = x
[ pop p ]ᵛ (γ , x) = [ p ]ᵛ γ

ᵏ : ∀{a b}{A : Set a}{B : Set b} → A → B → A
ᵏ a b = a

-- _ˢ_ : ∀ {α β γ}
--         {A : Set α}
--         {B : A → Set β}
--         {C : (a : A) → B a → Set γ}
--       → ((a : A) (b : B a) → C a b)
--       → (s : (a : A) → B a)
--       → (a : A) → C a (s a)
-- f ˢ g = λ a → f a (g a)

ᵛ : ∀ {α β γ}{S : Set α}{T : S → Set β}{P : Σ S T → Set γ}
  → ((s : S) (t : T s) → P (s , t))
  → (σ : Σ S T) → P σ
ᵛ f (s , t) = f s t

^ : ∀ {α β γ}{S : Set α}{T : S → Set β}{P : Σ S T → Set γ}
    → ((σ : Σ S T) → P σ)
    → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)

infix 3 _⋆_  _⊢_

infixr 4 _‘⟶’_
‘Σ’ : ∀ {Γ}(S : Ty Γ) → Ty (Γ , S) → Ty Γ
‘Σ’ S T Γ⇓ = σ (S Γ⇓) (^ T Γ⇓)
‘Π’ : ∀ {Γ}(S : Ty Γ) → Ty (Γ , S) → Ty Γ
‘Π’ S T Γ⇓ = π (S Γ⇓) (^ T Γ⇓)
_‘⟶’_ : ∀{Γ} → Ty Γ → Ty Γ → Ty Γ
lhs ‘⟶’ rhs = ‘Π’ lhs (rhs ∘ proj₁)

data _⋆_ (Γ : Con) : Ty Γ → Set
data _⊢_ (Γ : Con) : Ty Γ → Set
[_]ᵗ : ∀ {Γ T} → Γ ⊢ T → (γ : [ Γ ]ᶜ) → El (T γ)

data _⋆_ (Γ : Con) where
  ZE : Γ ⋆ ᵏ n₀
  ON : Γ ⋆ ᵏ n₁
  TW : Γ ⋆ ᵏ n₂
  TR : Γ ⋆ ᵏ τ
  SG : ∀ {S T}
       → Γ ⋆ S → Γ , S ⋆ T
       → Γ ⋆ ‘Σ’ S T
  PI : ∀ {S T}
       → Γ ⋆ S → Γ , S ⋆ T
       → Γ ⋆ ‘Π’ S T
  IF : ∀ {T F} (b : Γ ⊢ ᵏ n₂) → Γ ⋆ T → Γ ⋆ F
       → Γ ⋆ ᵏ if ˢ [ b ]ᵗ ˢ T ˢ F

infixl 5 _⊛_
infixr 3 _&_
data _⊢_ (Γ : Con) where
  VAR : ∀ {T} → Γ ∋ T → Γ ⊢ T
  LAM : ∀ {S T} → Γ ⋆ S → Γ , S ⊢ T → Γ ⊢ ‘Π’ S T
  _⊛_ : ∀ {S T} → Γ ⊢ ‘Π’ S (ᵛ T) → (p : Γ ⊢ S) → Γ ⊢ T ˢ [ p ]ᵗ
  UNT : Γ ⊢ ᵏ n₁
  TT FF : Γ ⊢ ᵏ n₂
  LEAF : Γ ⊢ ᵏ τ
  _⊕_ : Γ ⊢ ᵏ τ → Γ ⊢ ᵏ τ → Γ ⊢ ᵏ τ
  EXF : (T : Ty Γ) → Γ ⊢ ᵏ n₀ ‘⟶’ T
  IF : ∀{P} → (b : Γ ⊢ ᵏ n₂)
            → Γ , ᵏ n₂ ⋆ P
            → Γ ⊢ ^ P ˢ ᵏ tt
            → Γ ⊢ ^ P ˢ ᵏ ff
            → Γ ⊢ ^ P ˢ [ b ]ᵗ
  IND : ∀{P}
        → Γ , ᵏ τ ⋆ P
        → Γ ⊢ ^ P ˢ ᵏ ℓ
        → Γ ⊢ (λ Γ⇓ → π τ λ l → π τ λ r → (P (Γ⇓ , l) ‘→’ P (Γ⇓ , r) ‘→’ P (Γ⇓ , l ⊕ r)))
        → Γ ⊢ ‘Π’ (ᵏ τ) P
  _&_ : ∀{S T} (p : Γ ⊢ S) → Γ ⊢ T ˢ [ p ]ᵗ → Γ ⊢ ‘Σ’ S (ᵛ T)
  FST : ∀{S T} → Γ ⊢ ‘Σ’ S T
               → Γ ⊢ S
  SND : ∀{S T} → (p : Γ ⊢ ‘Σ’ S T)
               → Γ ⊢ ^ T ˢ fst ∘ [ p ]ᵗ

-- [ UU 0 ]ᵗ γ = uu
-- [ UU (suc n) ]ᵗ γ with uNext n
-- [ UU (suc n) ]ᵗ γ | u , b , p rewrite p = uu
[ VAR x ]ᵗ γ = [ x ]ᵛ γ
[ LAM X b ]ᵗ γ = λ x → [ b ]ᵗ (γ , x)
[ f ⊛ x ]ᵗ = [ f ]ᵗ ˢ [ x ]ᵗ
[ UNT ]ᵗ γ = tt
[ TT ]ᵗ γ = tt
[ FF ]ᵗ γ = ff
[ LEAF ]ᵗ γ = ℓ
[ l ⊕ r ]ᵗ γ = [ l ]ᵗ γ ⊕ [ r ]ᵗ γ
[ EXF T ]ᵗ γ = λ ()
[ IF {P} b pP t f ]ᵗ γ = if {B = El ∘ ^ P γ} ([ b ]ᵗ γ) ([ t ]ᵗ γ) ([ f ]ᵗ γ)
[ IND {P} pP lc bc ]ᵗ γ = tree-ind (El ∘ ^ P γ) ([ lc ]ᵗ γ) ([ bc ]ᵗ γ)
[ x & p ]ᵗ γ = [ x ]ᵗ γ , [ p ]ᵗ γ
[ FST p ]ᵗ γ = proj₁ ([ p ]ᵗ γ)
[ SND p ]ᵗ γ = proj₂ ([ p ]ᵗ γ)

⟦_⟧ : {T : ∀ {Γ} → Ty Γ} → (∀ {Γ} → Γ ⋆ T) → Set
⟦_⟧ {T} _ = ∀ {Γ} → Γ ⊢ T

True_ : ∀{Γ}(b : Γ ⊢ ᵏ n₂) → Γ ⋆ _
True b = IF b ON ZE
infix 1 True_

AND : ⟦ PI TW (PI TW TW) ⟧
AND = LAM TW $ LAM TW $ IF (VAR (pop top)) TW (VAR top) FF
OR : ⟦ PI TW (PI TW TW) ⟧
OR = LAM TW $ LAM TW $ IF (VAR (pop top)) TW TT (VAR top)

nat : ℕ → ⟦ TR ⟧
nat zero = LEAF
nat (suc n) = LEAF ⊕ nat n

is-leaf : ⟦ PI TR TW ⟧
is-leaf = IND TW TT $ LAM TR $ LAM TR $ LAM TW $ LAM TW $ FF

REC2 : ⟦ PI TW $ PI (PI TW $ PI TW TW) $ PI TR TW ⟧
REC2 = LAM TW (LAM (PI TW $ PI TW TW) (IND TW (VAR (pop top)) (LAM TR (LAM TR (VAR (pop (pop top)))))))

is-nat : ⟦ PI TR TW ⟧
is-nat = IND TW TT $ LAM TR $ LAM TR $ LAM TW $ LAM TW $ AND ⊛ (is-leaf ⊛ VAR (pop (pop (pop top)))) ⊛ VAR top

0-is-nat : ⟦ True_ (is-nat ⊛ LEAF) ⟧
0-is-nat = UNT

SUC : ⟦ PI TR TR ⟧
SUC = LAM TR (LEAF ⊕ VAR top)

-- private S-is-nat-ty : ∀{Γ} → Γ , ᵏ τ ⋆ _
--         S-is-nat-ty = PI (True_ $ is-nat ⊛ VAR top) (True_ $ is-nat ⊛ (SUC ⊛ VAR (pop top)))

-- S-is-nat : ⟦ PI TR $ S-is-nat-ty ⟧
-- S-is-nat = IND S-is-nat-ty (LAM ON 0-is-nat)
--                           $ LAM TR
--                           $ LAM TR
--                           $ LAM (PI (True_ $ is-nat ⊛ VAR (pop top)) (True_ $ is-nat ⊛ (SUC ⊛ VAR (pop (pop top)))))
--                           $ LAM (PI (True_ $ is-nat ⊛ VAR (pop top)) (True_ $ is-nat ⊛ (SUC ⊛ VAR (pop (pop top)))))
--                           $ ?
