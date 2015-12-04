{-# OPTIONS --rewriting #-}
-- Uses the syntax representation from http://www.cs.nott.ac.uk/~txa/publ/tt-in-tt.pdf with added Löbian constructors as suggested by Jason Gross
module Syntax.Typed.Defn where
open import lib renaming (id to idf)

infix 5 _⋆_ _⊢_ _⊃_

-- Types of the syntax
data Con : Set
data _⋆_ : Con → ℕ → Set
data _⊢_ : ∀ Γ {n} → Γ ⋆ n → Set
-- ty : ∀ {Γ} n → Γ ⋆ (suc n)
data _⊃_ : Con → Con → Set
-- _[_]T : ∀{Γ Δ n} → Δ ⋆ n → Tms Γ Δ → Γ ⋆ n

TmΓ= : ∀ {Γ n}{A₀ A₁ : Γ ⋆ n}(A₂ : A₀ ≡ A₁)
       → Γ ⊢ A₀ ≡ Γ ⊢ A₁
TmΓ= {Γ} p = ap (_⊢_ Γ) p

data Con where
  ε : Con
  _,_ : ∀ Γ {n} → Γ ⋆ n → Con

data _⋆_ where
  -- ty's
  _[_]T : ∀{Γ Δ n} → Δ ⋆ n → Γ ⊃ Δ → Γ ⋆ n
  uu : ∀{Γ} n → Γ ⋆ suc n
  ∈_ : ∀{Γ n} → Γ ⊢ uu n → Γ ⋆ n
  π σ : ∀{Γ n m} → (T : Γ ⋆ n) → Γ , T ⋆ m → Γ ⋆ n ⊔ m
  top bot : ∀{Γ} → Γ ⋆ 0
  lift : ∀{Γ n m} → Γ ⋆ n → n ≤ m → Γ ⋆ m
  -- One idea: develop it as a datatype in the theory
  -- Feels likely to have some of the same issues as semi-simplicials
  -- Commented out until I figure out what it should be
--  con : ∀{Γ} → Γ ⋆ 0
--  _‘⋆’_ : ∀{Γ} → Γ ⊢ con → ℕ → Γ ⋆ 0
--  _‘⊢’_ : ∀{Γ n}(Δ : Γ ⊢ con) → Γ ⊢ Δ ‘⋆’ n → Γ ⋆ 0
  box : ∀{Γ Δ n} → Δ ⋆ n → Γ ⋆ 0

-- Γ ⋆ n = Γ ⊢ ty n

infixl 8 _[_]T

TmΓA[]= : ∀{Γ Δ n}{A : Δ ⋆ n}{ρ₀ ρ₁ : Γ ⊃ Δ}(ρ₂ : ρ₀ ≡ ρ₁)
          → Γ ⊢ A [ ρ₀ ]T ≡ Γ ⊢ A [ ρ₁ ]T
TmΓA[]= refl = refl

data _⊃_ where
  ε : ∀{Γ} → Γ ⊃ ε
  _,_ : ∀{Γ Δ n}(δ : Γ ⊃ Δ){A : Δ ⋆ n} → Γ ⊢ A [ δ ]T → Γ ⊃ Δ , A
  π₁ : ∀{Γ Δ n}{A : Δ ⋆ n} → Γ ⊃ Δ , A → Γ ⊃ Δ
  id : ∀{Γ} → Γ ⊃ Γ
  _∙_ : ∀{Γ Δ Σ} → Δ ⊃ Σ → Γ ⊃ Δ → Γ ⊃ Σ

wk : ∀{Γ n}{A : Γ ⋆ n} → Γ , A ⊃ Γ
wk = π₁ id

infixr 6 _‘→’_

_‘→’_ : ∀ {Γ n m} → Γ ⋆ n → Γ ⋆ m → Γ ⋆ (n ⊔ m)
dom ‘→’ cod = π dom (cod [ wk ]T)

data _⊢_ where
  -- tm's
  _[_]t : ∀{Γ Δ n}{T : Δ ⋆ n} → Δ ⊢ T → (δ : Γ ⊃ Δ) → Γ ⊢ T [ δ ]T
  π₂ : ∀{Γ Δ n}{A : Δ ⋆ n}(δ : Γ ⊃ Δ , A) → Γ ⊢ A [ π₁ δ ]T
  app : ∀{Γ n m}{A : Γ ⋆ n}{B : Γ , A ⋆ m} → Γ ⊢ π A B → Γ , A ⊢ B
  lam : ∀{Γ n m}{A : Γ ⋆ n}{B : Γ , A ⋆ m} → Γ , A ⊢ B → Γ ⊢ π A B
  tt : ∀{Γ} → Γ ⊢ top
  bot-rec : ∀{Γ n}(A : Γ , bot ⋆ n) → Γ ⊢ π bot A
  up : ∀{Γ n m}{A : Γ ⋆ n} → Γ ⊢ A → (p : n ≤ m) → Γ ⊢ lift A p
  ⌜_⌝T : ∀{Γ n} → Γ ⋆ n → Γ ⊢ uu (suc n)
  ⌜_⌝t : ∀{Γ Δ n}{T : Δ ⋆ n} → Δ ⊢ T → Γ ⊢ box T
  -- Ah hah! Right! This is how box should behave!
  Löb : ∀{Γ Δ n}{T : Δ ⋆ n} → Γ ⊢ box (box T ‘→’ T) → Γ ⊢ box T
  bapp : ∀{Γ Δ n m}{A : Δ ⋆ n}{B : Δ , A ⋆ m} → Γ ⊢ box {Δ = Δ} (π A B) → Γ ⊢ box  {Δ = Δ , A} B
  _[_]b : ∀{Γ Δ Σ n}{A : Σ ⋆ n} → Γ ⊢ box A → (δ : Δ ⊃ Σ) → Γ ⊢ box (A [ δ ]T)
  unsub : ∀{Γ Δ Σ n}(δ : Δ ⊃ Σ){A : Σ ⋆ n} → Γ ⊢ box (A [ δ ]T) → Γ ⊢ box A

infixl 8 _[_]t

vz : ∀ {Γ n}{A : Γ ⋆ n} → Γ , A ⊢ A [ wk ]T
vz = π₂ id

vs : ∀ {Γ n m}{A : Γ ⋆ n}{B : Γ ⋆ m} → Γ ⊢ A → Γ , B ⊢ A [ wk ]T
vs x = x [ wk ]t

-- ty = uu
-- T [ δ ]T = T [ δ ]t

postulate
  -- higher constructors for ⋆'s
  uu[]  : ∀{Γ Δ n}(δ : Γ ⊃ Δ)
          → uu n [ δ ]T ≡ uu n

  top[] : ∀{Γ Δ} (δ : Γ ⊃ Δ)
          → top [ δ ]T ≡ top

  bot[] : ∀{Γ Δ} (δ : Γ ⊃ Δ)
          → bot [ δ ]T ≡ bot

  box[] : ∀{Γ Δ Σ n} (δ : Γ ⊃ Δ) (A : Σ ⋆ n)
          → box A [ δ ]T ≡ box A

  ∈⌜l⌝T : ∀{Γ n}(A : Γ ⋆ n)
        → ∈ ⌜ A ⌝T ≡ lift A (≤-step ≤-refl)

  -- ⌜∈l⌝T : ∀{Γ n}(A : Γ ⊢ uu n)
  --       → ⌜ ∈ A ⌝T ≡ {!lift A!}

  lift-0 : ∀{Γ n}(A : Γ ⋆ n)
           → lift A ≤-refl ≡ A

  -- lift-t0 : ∀{Γ n}(A : Γ ⊢ uu n)
  --         → {!!} ≡ {!!}

  lift-lift-T : ∀{Γ x y z}(p : x ≤ y)(q : y ≤ z)(A : Γ ⋆ x)
                → lift (lift A p) q ≡ (lift A (p ≤-trans q))

  [id]T : ∀{Γ n}(A : Γ ⋆ n)
          → A [ id ]T ≡ A

  [][]T : ∀{Γ Δ Σ n}{A : Σ ⋆ n}{σ : Γ ⊃ Δ}{δ : Δ ⊃ Σ}
          → A [ δ ]T [ σ ]T ≡ A [ δ ∙ σ ]T

{-# REWRITE uu[]  #-}
{-# REWRITE top[] #-}
{-# REWRITE bot[] #-}
{-# REWRITE box[] #-}
{-# REWRITE ∈⌜l⌝T #-}
-- {-# REWRITE ⌜∈l⌝T #-}
-- {-# REWRITE lift-T0 #-}
-- {-# REWRITE lift-t0 #-}
{-# REWRITE lift-0 #-}
{-# REWRITE lift-lift-T #-}
{-# REWRITE [id]T #-}
{-# REWRITE [][]T #-}

_^_ : ∀{Γ Δ n}(δ : Γ ⊃ Δ)(A : Δ ⋆ n) → (Γ , (A [ δ ]T)) ⊃ (Δ , A)
δ ^ A = (δ ∙ wk) , vz

<_> : ∀ {Γ n}{A : Γ ⋆ n} → Γ ⊢ A → Γ ⊃ Γ , A
< t > = id , t

postulate
  -- more higher constructors for ty's
  ∈[]   : ∀{Γ Δ n}(δ : Γ ⊃ Δ)(A : Δ ⊢ uu n)
          → ∈ A [ δ ]T ≡ ∈ (A [ δ ]t)
  π[] : ∀{Γ Δ n m}(δ : Γ ⊃ Δ)(A : Δ ⋆ n)(B : (Δ , A) ⋆ m)
        → π A B [ δ ]T ≡ π (A [ δ ]T) (B [ δ ^ A ]T)

{-# REWRITE ∈[] #-}
{-# REWRITE π[] #-}

postulate
  -- higher constructors for ⊃'s
  idl : ∀{Γ Δ}(δ : Γ ⊃ Δ)
        → id ∙ δ ≡ δ
  idr : ∀{Γ Δ}(δ : Γ ⊃ Δ)
        → δ ∙ id ≡ δ
  assoc : ∀{Γ Δ Σ Ω}(ω : Σ ⊃ Ω)(σ : Δ ⊃ Σ)(δ : Γ ⊃ Δ)
          → ω ∙ (σ ∙ δ) ≡ (ω ∙ σ) ∙ δ
  ,∙ : ∀{Γ Δ Σ n}(δ : Γ ⊃ Δ){σ : Δ ⊃ Σ}{A : Σ ⋆ n}(a : Δ ⊢ A [ σ ]T)
       → ((_,_ σ {A} a) ∙ δ) ≡ ((σ ∙ δ) , (a [ δ ]t))
  π₁β : ∀{Γ Δ n}{A : Δ ⋆ n}(δ : Γ ⊃ Δ)(a : Γ ⊢ A [ δ ]T)
        → π₁ (_,_ δ {A} a) ≡ δ
  π₁η : ∀{Γ Δ n}{A : Δ ⋆ n}{δ : Γ ⊃ Δ , A}
        → (π₁ δ , π₂ δ) ≡ δ
  εη : ∀{Γ}{σ : Γ ⊃ ε}
       → σ ≡ ε

{-# REWRITE idl #-}
{-# REWRITE idr #-}
{-# REWRITE ,∙ #-}
{-# REWRITE π₁β #-}
{-# REWRITE π₁η  #-}

π₁∙ : ∀{Γ Δ Θ n}{A : Δ ⋆ n}{δ : Γ ⊃ Δ , A}{ρ : Θ ⊃ Γ}
      → π₁ δ ∙ ρ ≡ π₁ (δ ∙ ρ)
π₁∙ {Γ}{Δ}{Θ}{n}{A}{δ}{ρ}
  = π₁ {A = A} δ ∙ ρ ≡⟨ π₁β {A = A} (π₁ δ ∙ ρ) (π₂ δ [ ρ ]t) ⟩
    π₁ {A = A} ((π₁ δ ∙ ρ) , (π₂ δ [ ρ ]t)) ≡⟨ ap π₁ (,∙ ρ {π₁ δ} {A} (π₂ δ) ⁻¹) ⟩
    π₁ {A = A} (δ ∙ ρ) ∎

{-# REWRITE π₁∙ #-}
--  π₁β {A = A} (π₁ δ ∙ ρ) (π₂ δ [ ρ ]t) ⁻¹ ◾ {!!} ◾ {!!}
  --π₁β {δ = π₁ δ ∙ ρ} {π₂ δ [ ρ ]t} ⁻¹ ◾ ap π₁ (,∙ {δ = π₁ δ} {ρ} {a = π₂ δ} ⁻¹) ◾ ap (λ σ → π₁ (σ ∙ ρ)) ?

→[] : ∀{Γ Δ}(δ : Γ ⊃ Δ){n m}(A : Δ ⋆ n)(B : Δ ⋆ m)
      → (A ‘→’ B) [ δ ]T ≡ A [ δ ]T ‘→’ B [ δ ]T
→[] δ A B = π[] δ A (B [ wk ]T)

postulate
  -- higher constructors for ⊢'s
  [id]t : ∀{Γ n}{A : Γ ⋆ n}(a : Γ ⊢ A)
          → a [ id ]t ≡ a
  [][]t : ∀{Γ Δ Σ n}(δ : Γ ⊃ Δ)(σ : Δ ⊃ Σ){A : Σ ⋆ n}(a : Σ ⊢ A)
          → a [ σ ]t [ δ ]t ≡ a [ σ ∙ δ ]t
  ⌜⌝T[] : ∀{Γ Δ n}(δ : Γ ⊃ Δ)(A : Δ ⋆ n)
          → ⌜ A ⌝T [ δ ]t ≡ ⌜ A [ δ ]T ⌝T
  ⌜⌝t[] : ∀{Γ Δ Σ n}(δ : Γ ⊃ Δ){A : Σ ⋆ n}(a : Σ ⊢ A)
          → ⌜ a ⌝t [ δ ]t ≡ ⌜ a ⌝t
  lift-lift-t : ∀{Γ x y z}(p : x ≤ y)(q : y ≤ z){A : Γ ⋆ x}(a : Γ ⊢ A)
                → up (up a p) q ≡ up a (p ≤-trans q)
  π₂β : ∀{Γ Δ n}{A : Δ ⋆ n}(δ : Γ ⊃ Δ)(a : Γ ⊢ A [ δ ]T)
        → π₂ (_,_ δ {A} a) ≡ a
  lam[] : ∀{Γ Δ n m}{A : Δ ⋆ n}{B : Δ , A ⋆ m}(δ : Γ ⊃ Δ)(t : Δ , A ⊢ B)
          → (lam t) [ δ ]t ≡ lam (t [ δ ^ A ]t)
  πβ : ∀{Γ n m}{A : Γ ⋆ n}{B : Γ , A ⋆ m}(t : Γ , A ⊢ B)
       → app (lam t) ≡ t
  πη : ∀{Γ n m}{A : Γ ⋆ n}{B : Γ , A ⋆ m}(t : Γ ⊢ πA B)
       → lam (app t) ≡ t
  tt[] : ∀{Γ Δ}(δ : Γ ⊃ Δ)
         → tt [ δ ]t ≡ tt
  brec[] : ∀{Γ Δ n}(A : Δ , bot ⋆ n)(δ : Γ ⊃ Δ)
           → (bot-rec A) [ δ ]t ≡ (coe (TmΓ= (π[] δ bot A ⁻¹)) $ bot-rec (A [ δ ^ bot ]T))
  ⌜⌝t[]b : ∀{Γ Δ Σ n}(δ : Δ ⊃ Σ){A : Σ ⋆ n}(a : Σ ⊢ A)
           → ⌜_⌝t {Γ} a [ δ ]b ≡ ⌜ a [ δ ]t ⌝t -- ⌜ a ⌝ [ δ ]b ≡ ⌜ a [ δ ]t ⌝t
  Löb[] : ∀{Γ Δ Σ n}(δ : Γ ⊃ Δ){A : Σ ⋆ n}(l : Δ ⊢ box (box A ‘→’ A))
        → Löb l [ δ ]t ≡ Löb (l [ δ ]t)
  bapp[] : ∀{Γ Δ Σ n m}(δ : Γ ⊃ Δ){A : Σ ⋆ n}{B : Σ , A ⋆ m}(p : Δ ⊢ box (π A B))
           → bapp p [ δ ]t ≡ bapp (p [ δ ]t)
  unsub[] : ∀{Γ Δ Σ Ξ n}(δ : Γ ⊃ Δ){A : Ξ ⋆ n}(σ : Σ ⊃ Ξ)(a : Δ ⊢ box (A [ σ ]T))
            → unsub σ {A} a [ δ ]t ≡ unsub σ {A} (a [ δ ]t)
  unsub[]b : ∀{Γ Δ Σ n}(δ : Δ ⊃ Σ){A : Σ ⋆ n}(a : Γ ⊢ box A)
            → unsub δ (a [ δ ]b) ≡ a
  [unsub]b : ∀{Γ Δ Σ n}(δ : Δ ⊃ Σ){A : Σ ⋆ n}(a : Γ ⊢ box (A [ δ ]T))
             → unsub δ {A = A} a [ δ ]b ≡ a

{-# REWRITE [id]t #-}
{-# REWRITE [][]t #-}
{-# REWRITE ⌜⌝T[] #-}
{-# REWRITE ⌜⌝t[] #-}
{-# REWRITE lift-lift-t #-}
{-# REWRITE π₂β #-}
{-# REWRITE lam[] #-}
{-# REWRITE πβ #-}
{-# REWRITE πη #-}
{-# REWRITE tt[] #-}
{-# REWRITE brec[] #-}
{-# REWRITE ⌜⌝t[]b #-}
{-# REWRITE Löb[] #-}
{-# REWRITE bapp[] #-}
{-# REWRITE unsub[] #-}
{-# REWRITE unsub[]b #-}
{-# REWRITE [unsub]b #-}

löb : ∀{Γ n}{T : Γ ⋆ n} → Γ ⊢ box T ‘→’ T → Γ ⊢ T
löb {Γ} {T = T} l = app l [ < Löb ⌜ l ⌝t > ]t
