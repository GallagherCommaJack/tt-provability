{-# OPTIONS --rewriting #-}
-- Uses the syntax representation from http://www.cs.nott.ac.uk/~txa/publ/tt-in-tt.pdf with added Löbian constructors as suggested by Jason Gross
module Syntax.Typed.Def where
open import lib renaming (id to idf)

-- types of the syntax

data Con : Set
data Ty : Con → Set
data Tms : Con → Con → Set
data Tm : ∀ Γ → Ty Γ → Set

-- a congruence rule (corresponds to refl(TmΓ) in the cubical syntax:
-- Γ is in the context,, we degenerate it)
TmΓ= : {Γ : Con}{A₀ : Ty Γ}{A₁ : Ty Γ}(A₂ : A₀ ≡ A₁)
     → Tm Γ A₀ ≡ Tm Γ A₁
TmΓ= {Γ} p = ap (Tm Γ) p

-- constructors
-- note: we are using the categorical application rule and π₁,, π₂

data Con where
  ε     : Con
  _,,_   : (Γ : Con) → Ty Γ → Con

infixl 5 _,,_

data Ty where
  _[_]T   : ∀{Γ Δ} → Ty Δ → Tms Γ Δ → Ty Γ
  ‘Π’     : ∀{Γ}(A : Ty Γ)(B : Ty (Γ ,, A)) → Ty Γ
  U       : ∀{Γ} → Ty Γ
  El      : ∀{Γ}(A : Tm Γ U) → Ty Γ
  ‘top’   : ∀{Γ} → Ty Γ
  ‘bot’   : ∀{Γ} → Ty Γ
  ‘□’     : ∀{Γ} → Ty Γ → Ty Γ

infixl 7 _[_]T

TmΓA[]= : ∀{Γ Δ}{A : Ty Δ}{ρ₀ ρ₁ : Tms Γ Δ}(ρ₂ : ρ₀ ≡ ρ₁)
        → Tm Γ (A [ ρ₀ ]T) ≡ Tm Γ (A [ ρ₁ ]T)
TmΓA[]= refl = refl

data Tms where
  ε     : ∀{Γ} → Tms Γ ε
  _,,_   : ∀{Γ Δ}(δ : Tms Γ Δ){A : Ty Δ} → Tm Γ (A [ δ ]T) → Tms Γ (Δ ,, A)
  π₁    : ∀{Γ Δ}{A : Ty Δ} → Tms Γ (Δ ,, A) →  Tms Γ Δ
  id    : ∀{Γ} → Tms Γ Γ
  _⊚_   : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ

infixl 6 _⊚_

wk : ∀{Γ A} → Tms (Γ ,, A) Γ
wk = π₁ id

infixr 1 _‘→’_

_‘→’_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
dom ‘→’ cod = ‘Π’ dom (cod [ wk ]T)

data Tm where
  _[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T)
  π₂    : ∀{Γ Δ}{A : Ty Δ}(δ : Tms Γ (Δ ,, A)) → Tm Γ (A [ π₁ δ ]T)
  app   : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,, A)} → Tm Γ (‘Π’ A B) → Tm (Γ ,, A) B
  lam   : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,, A)} → Tm (Γ ,, A) B → Tm Γ (‘Π’ A B)
  ‘tt’  : ∀{Γ} → Tm Γ ‘top’
  ‘⊥-rec’ : ∀ {Γ A} → Tm Γ (‘Π’ ‘bot’ A)
  ⌜_⌝ : ∀ {Γ} → Ty Γ → Tm Γ U
  ⌜_⌝t : ∀ {Γ T} → Tm Γ T → Tm Γ (‘□’ T)
  Löb : ∀ {Γ T} → Tm Γ (‘□’ T ‘→’ T) → Tm Γ T

infixl 8 _[_]t

vz : ∀ {Γ}{A : Ty Γ} → Tm (Γ ,, A) (A [ wk ]T)
vz = π₂ id

vs : ∀ {Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ,, B) (A [ wk ]T)
vs x = x [ wk ]t

-- higher constructors are postulated
postulate
  -- higher constructors for Ty
  [id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
  [][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Tms Γ Δ}{δ : Tms Δ Σ} → (A [ δ ]T) [ σ ]T ≡ A [ δ ⊚ σ ]T
  U[]   : ∀{Γ Δ}{δ : Tms Γ Δ} → U [ δ ]T ≡ U
  ⊤[]   : ∀{Γ Δ}{δ : Tms Γ Δ} → ‘top’ [ δ ]T ≡ ‘top’
  ⊥[]   : ∀{Γ Δ}{δ : Tms Γ Δ} → ‘bot’ [ δ ]T ≡ ‘bot’
--  El[]  : ∀{Γ Δ}{δ : Tms Γ Δ}{Â : Tm Δ U} → El Â [ δ ]T ≡ El (coe (TmΓ= U[]) (Â [ δ ]t'))

{-# REWRITE [id]T #-}
--
{-# REWRITE U[] #-}
{-# REWRITE ⊤[] #-}
{-# REWRITE ⊥[] #-}

{-# REWRITE [][]T #-}

_^_ : ∀{Γ Δ}(δ : Tms Γ Δ)(A : Ty Δ) → Tms (Γ ,, A [ δ ]T) (Δ ,, A)
_^_ {Γ} {Δ} δ A = (δ ⊚ wk) ,, vz {Γ} {A [ δ ]T}

infix 5 _^_

postulate
   Elβ   : ∀{Γ}(A : Tm Γ U) → ⌜ El A ⌝ ≡ A
   Elη   : ∀{Γ}(A : Ty Γ) → El (⌜ A ⌝) ≡ A

   El[]  : ∀{Γ Δ}{δ : Tms Γ Δ}(A : Tm Δ U) → El A [ δ ]T ≡ El (A [ δ ]t)
   □[]   : ∀{Γ Δ}{δ : Tms Γ Δ}(A : Ty Δ) → ‘□’ A [ δ ]T ≡ ‘□’ (A [ δ ]T)
   -- □[]   : ∀{Γ Δ}{δ : Tms Γ (Δ ,, U)} → ‘□’ Δ [ δ ]T ≡ El (π₂ δ) -- don't think this one is right
   -- □[]   : ∀{Γ Δ}{δ : Tms Γ Δ} → ‘□’ Δ [ δ ⊚ wk ,, coe (TmΓ= U[] ⁻¹) tvz ]T ≡ ‘□’ Γ -- this doesn't look right
   -- Q[]   : ∀{Γ Δ}{δ : Tms Γ Δ} (f : Ty (Δ ,, U)) → Quine f [ δ ]T ≡ Quine (f [ δ ⊚ wk ,, coe (TmΓ= U[] ⁻¹) tvz ]T)
   ‘Π’[]   : ∀{Γ Δ}{δ : Tms Γ Δ}(A : Ty Δ)(B : Ty (Δ ,, A))
         → (‘Π’ A B) [ δ ]T ≡ ‘Π’ (A [ δ ]T) (B [ δ ^ A ]T)
   setT  : ∀{Γ}{A B : Ty Γ}{e0 e1 : A ≡ B} → e0 ≡ e1

   -- Qwk   : ∀{Γ}(f : Ty Γ) → Quine (f [ π₁ id ]T) ≡ f
   -- Q_[_]   : ∀{Γ Δ}(δ : Tms Γ Δ)(f : Ty (Δ ,, U)) → Quine f [ δ ]T ≡ Quine (f [ δ ^ U ]T)

   -- Qapp  : ∀{Γ}{T : Ty (Γ ,, U)} → T [ ‘’ₛ ⌜ Quine T ⌝ ]T ≡ Quine T

{-# REWRITE Elβ #-}
{-# REWRITE Elη #-}
{-# REWRITE El[] #-}
{-# REWRITE □[] #-}
{-# REWRITE ‘Π’[] #-}
-- {-# REWRITE Q_[_] #-}
-- {-# REWRITE Qwk #-}
-- {-# REWRITE Qapp #-}

postulate
   -- higher constructors for Tms
   idl   : ∀{Γ Δ}{δ : Tms Γ Δ} → id ⊚ δ ≡ δ
   idr   : ∀{Γ Δ}{δ : Tms Γ Δ} → δ ⊚ id ≡ δ
   assoc : ∀{Δ Γ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Γ Σ}{ν : Tms Δ Γ}
         → (σ ⊚ δ) ⊚ ν ≡ σ ⊚ (δ ⊚ ν)
   ,,⊚    : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty Δ}{a : Tm Γ (A [ δ ]T)}
         → (_,,_ δ {A} a) ⊚ σ ≡ (δ ⊚ σ) ,, a [ σ ]t -- coe (TmΓ= [][]T) (a [ σ ]t)
   π₁β   : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T)} → π₁ (_,,_ δ {A} a) ≡ δ
   πη    : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ (Δ ,, A)} → (π₁ δ ,, π₂ δ) ≡ δ
   εη    : ∀{Γ}{σ : Tms Γ ε} → σ ≡ ε
   sets  : ∀{Γ Δ}{δ σ : Tms Γ Δ}{e0 e1 : δ ≡ σ} → e0 ≡ e1

{-# REWRITE idl #-}
{-# REWRITE idr #-}
{-# REWRITE ,,⊚ #-}
{-# REWRITE π₁β #-}
{-# REWRITE πη #-}

postulate
   -- higher constructors for Tm
   [id]t : ∀{Γ}{A : Ty Γ}{t : Tm Γ A} → t [ id ]t ≡ t
   [][]t : ∀{Γ Δ Σ}{A : Ty Σ}{t : Tm Σ A}{σ : Tms Γ Δ}{δ : Tms Δ Σ}
         → (t [ δ ]t) [ σ ]t ≡ t [ δ ⊚ σ ]t
   π₂β   : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T)}
         → π₂ (_,,_ δ {A} a) ≡ a
   lam[] : ∀{Γ Δ}{δ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ ,, A)}{t : Tm (Δ ,, A) B}
         → (lam t) [ δ ]t ≡ lam (t [ δ ^ A ]t)
   ‘Π’β    : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,, A)}{t : Tm (Γ ,, A) B}
         →  app (lam t) ≡ t
   ‘Π’η    : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,, A)}{t : Tm Γ (‘Π’ A B)}
         → lam (app t) ≡ t
   sett  : ∀{Γ}{A : Ty Γ}{u v : Tm Γ A}{e0 e1 : u ≡ v} → e0 ≡ e1
   tt[]  : ∀{Γ Δ}{δ : Tms Γ Δ} → ‘tt’ [ δ ]t ≡ ‘tt’ -- ∀{Γ Δ}{δ : Tms Γ Δ} → ‘tt’ [ δ ]t ≡[ TmΓ= ⊤[] ]≡ ‘tt’
   ⌜⌝[]  : ∀{Γ Δ A}{δ : Tms Γ Δ} → ⌜ A ⌝ [ δ ]t ≡ ⌜ A [ δ ]T ⌝

<_> : ∀ {Γ}{A : Ty Γ} → Tm Γ A → Tms Γ (Γ ,, A)
< t > = id ,, t

--    -- What's the analagous law for Löb? An idea below:
--    -- Löb[] : ∀{Γ Δ X}{δ : Tms Γ Δ}{s : Tm Δ (‘□’ Δ [ id ,, ⌜ X ⌝ [ id ]t ]T ‘→’ X)} →
--    --         Löb s [ δ ]t
--    --       ≡ Löb (coe {!!} (s [ δ ]t))

{-# REWRITE [id]t #-}
{-# REWRITE [][]t #-}
-- {-# REWRITE lam[] #-}
{-# REWRITE tt[] #-}
{-# REWRITE ⌜⌝[] #-}
{-# REWRITE ‘Π’η #-}
-- {-# REWRITE ‘Π’β #-}

app= : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ,, A)}{t₀ t₁ : Tm Γ (‘Π’ A B)} → t₀ ≡ t₁ → app t₀ ≡ app t₁
app= refl = refl

app[] : ∀{Γ Δ}{δ : Tms Γ Δ}{A : Ty Δ}{B : Ty (Δ ,, A)}{t : Tm Δ (‘Π’ A B)}
      → app (t [ δ ]t) ≡ (app t) [ δ ^ A ]t
app[] {Γ}{Δ}{δ}{A}{B}{t}
      = app (t [ δ ]t)               ≡⟨ refl ⟩
        app (lam (app t) [ δ ]t)     ≡⟨ ap app {lam (app t) [ δ ]t} {lam (app t [ δ ^ A ]t)} (lam[] {t = app t}) ⟩
        app (lam (app t [ δ ^ A ]t)) ≡⟨ ‘Π’β ⟩ -- ‘Π’β ⟩
        app t [ δ ^ A ]t             ∎

π₁⊚ : ∀{Γ Δ Θ}{A : Ty Δ}{δ : Tms Γ (Δ ,, A)}{ρ : Tms Θ Γ}
     → π₁ δ ⊚ ρ ≡ π₁ (δ ⊚ ρ)
π₁⊚ {Γ}{Δ}{Θ}{A}{δ}{ρ}
  = π₁ {A = A} δ ⊚ ρ ≡⟨ π₁β {A = A} {π₁ δ ⊚ ρ} {π₂ δ [ ρ ]t} ⟩
    π₁ {A = A} (π₁ δ ⊚ ρ ,, π₂ δ [ ρ ]t) ≡⟨ ap π₁ (,,⊚ {δ = π₁ δ} {ρ} {A} {π₂ δ} ⁻¹) ⟩
    π₁ {A = A} (δ ⊚ ρ) ∎

{-# REWRITE π₁⊚ #-}
postulate
  Löb[] : ∀ {Γ Δ}{δ : Tms Γ Δ}{A : Ty Δ}(l : Tm Δ (‘□’ A ‘→’ A)) → Löb l [ δ ]t ≡ Löb (l [ δ ]t)

wk×2 : ∀ {Γ A B} → Tms (Γ ,, A ,, B) Γ
wk×2 = π₁ (π₁ id)

wk⊚wk=wk×2 : ∀ {Γ A B} → wk ⊚ wk ≡ wk×2 {Γ} {A} {B}
wk⊚wk=wk×2 {Γ} {A} {B} = refl

wk1 : ∀{Γ A B} → Tms (Γ ,, B ,, A [ wk ]T) (Γ ,, A)
wk1 {Γ} {A} {B} = (wk ⊚ wk) ,, vz {A = A [ wk ]T}
-- some defined conversion rules

‘Π’= : ∀{Γ}{A₀ A₁ : Ty Γ}(A₂ : A₀ ≡ A₁){B₀ : Ty (Γ ,, A₀)}{B₁ : Ty (Γ ,, A₁)}
     (B₂ : B₀ ≡[ ap Ty (ap (_,,_ Γ) A₂) ]≡ B₁)
   → ‘Π’ A₀ B₀ ≡ ‘Π’ A₁ B₁
‘Π’= refl refl = refl

s,,= : ∀ {Γ Δ : Con}{δ₁ δ₂ : Tms Γ Δ}(δₚ : δ₁ ≡ δ₂){A : Ty Δ}
      → {a₁ : Tm Γ (A [ δ₁ ]T)}{a₂ : Tm Γ (A [ δ₂ ]T)}
      → a₁ ≡[ ap (λ δ → Tm Γ (A [ δ ]T)) δₚ ]≡ a₂
      → _≡_ {A = Tms Γ (Δ ,, A)} (δ₁ ,, a₁) (δ₂ ,, a₂)
s,,= refl refl = refl

_$$_ : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ,, A)} → (t : Tm Γ (‘Π’ A B)) → (u : Tm Γ A) → Tm Γ (B [ < u > ]T)
t $$ u = (app t) [ < u > ]t

wk<> : ∀{Γ}{A : Ty Γ}(a : Tm Γ A) → wk ⊚ < a > ≡ id
wk<> {Γ} {A} a
  = wk ⊚ < a > ≡⟨ refl ⟩
    π₁ id ⊚ (id ,, a ) ≡⟨ refl ⟩
    π₁ (id ⊚ (id ,, a )) ≡⟨ refl ⟩
    π₁ (id ,, a) ≡⟨ refl ⟩
    id ∎

δ=coe : ∀{Γ Δ}{δ₁ δ₂ : Tms Γ Δ}(δₚ : δ₁ ≡ δ₂){A : Ty Δ}{a : Tm Δ A} → a [ δ₁ ]t ≡[ ap (λ δ → Tm Γ (A [ δ ]T)) δₚ ]≡ a [ δ₂ ]t
δ=coe refl = refl

-- ‘’ₛv : ∀{Γ}{A : Ty Γ} → < vz {Γ} {A} > ⊚ wk ≡ id
-- ‘’ₛv {Γ} {A}
--   = < vz > ⊚ wk ≡⟨ refl ⟩
--     (id ,, coe (TmΓ= [id]T ⁻¹) vz) ⊚ wk ≡⟨ ,,⊚ ◾ {!!} ⟩
--     id ⊚ wk ,, {!!} [ {!id ⊚ wk!} ]t ≡⟨ {!!} ⟩
--     id ∎

--   where H1 : wk {Γ} {A} ⊚ id ⊚ wk {Γ ,, A} {A [ wk ]T} ≡ wk ⊚ wk
--         H1 = ap (λ s → s ⊚ wk) idr

-- we can prove that Con is a set,, no need to postulate a higher constructor
setC : {Γ Δ : Con}{e0 e1 : Γ ≡ Δ} → e0 ≡ e1
setC {ε}     {ε}    {refl}{refl} = refl
setC {ε}     {Δ ,, A}{()}
setC {Γ ,, A} {ε}    {()}
setC {Γ ,, A} {Δ ,, B}{e0}  {e1}   = ,,=η e0 ◾ ,,== α β ◾ ,,=η e1 ⁻¹
  where
    ,,= : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}(p : Γ ≡ Δ)(q : A ≡[ ap Ty p ]≡ B)
       → _≡_ {A = Con} (Γ ,, A) (Δ ,, B)
    ,,= refl refl = refl

    ,,=0 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ} → _≡_ {A = Con} (Γ ,, A) (Δ ,, B) → Γ ≡ Δ
    ,,=0 refl = refl

    ,,=1 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ} → (p : _≡_ {A = Con} (Γ ,, A) (Δ ,, B)) → A ≡[ ap Ty (,,=0 p) ]≡ B
    ,,=1 refl = refl

    ,,=η : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ} → (p : _≡_ {A = Con} (Γ ,, A) (Δ ,, B)) → p ≡ ,,= (,,=0 p) (,,=1 p)
    ,,=η refl = refl

    ,,=β0 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}(p : Γ ≡ Δ)(q : A ≡[ ap Ty p ]≡ B) → p ≡ ,,=0 (,,= p q)
    ,,=β0 refl refl = refl

    ,,=β1 : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}(p : Γ ≡ Δ)(q : A ≡[ ap Ty p ]≡ B)
         → q ≡[ ap (λ z → A ≡[ ap Ty z ]≡ B) (,,=β0 p q) ]≡ ,,=1 (,,= p q)
    ,,=β1 refl refl = refl

    α : ,,=0 e0 ≡ ,,=0 e1
    α = setC {Γ}{Δ}{,,=0 e0}{,,=0 e1}

    β : ,,=1 e0 ≡[ ap (λ z → A ≡[ ap Ty z ]≡ B) α ]≡ ,,=1 e1
    β = setT {Δ}{coe (ap Ty (,,=0 e1)) A}{B}{coe (ap (λ z → A ≡[ ap Ty z ]≡ B) α) (,,=1 e0)}{,,=1 e1}

    ,,== : {Γ Δ : Con}{A : Ty Γ}{B : Ty Δ}{p p' : Γ ≡ Δ}{q : A ≡[ ap Ty p ]≡ B}{q' : A ≡[ ap Ty p' ]≡ B}
        (α : p ≡ p')(β : q ≡[ ap (λ z → A ≡[ ap Ty z ]≡ B) α ]≡ q') → ,,= p q ≡ ,,= p' q'
    ,,== refl refl = refl
