{-# OPTIONS --without-K #-}

module lib where

open import Level renaming (zero to lzero)

--------------------------------------------------------------
-- unsafe
--------------------------------------------------------------
{-# NON_TERMINATING #-}
undefined : ∀ {i}{A : Set i} → A
undefined = undefined

--------------------------------------------------------------
-- equality
--------------------------------------------------------------

data _≡_ {i}{A : Set i} (x : A) : A → Set i where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

infix 4 _≡_

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

{-# BUILTIN REWRITE _≡_ #-}

infixl 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z

infixr 2 _≡⟨_⟩_

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
x ∎ = refl

infix  3 _∎

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

coeref : ∀{i}{A : Set i} (a : A) → coe refl a ≡ a
coeref a = refl

transport : ∀ {i}{A : Set i}{j}(B : A → Set j) {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
transport B refl b = b

_≡[_]≡_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ α ]≡ y = coe α x ≡ y

infix 4 _≡[_]≡_

ap : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡ f a₁
ap f refl = refl

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ ap B a₂ ]≡ f a₁
apd f refl = refl

apid : ∀{i}{A : Set i}{x y : A}(p : x ≡ y) → ap (λ x → x) p ≡ p
apid refl = refl

apap : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}{f : A → B}{g : B → C}
       {a₀ a₁ : A}(a₂ : a₀ ≡ a₁) → ap (λ x → g (f x)) a₂ ≡ ap g (ap f a₂)
apap refl = refl

J : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

J' : {A : Set} (P : {x y : A} → x ≡ y → Set) → (∀ {x} → P {x} {x} refl) → {x y : A} (w : x ≡ y) → P w
J' P pr w = J P pr w

≡inv : {A : Set} {x y : A} (p : x ≡ y) → (p ◾ p ⁻¹) ≡ refl
≡inv refl = refl

coeap2 : {A : Set}{B : A → Set}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁){t : B a₁}
       → coe (ap B a₂) (coe (ap B (a₂ ⁻¹)) t) ≡ t
coeap2 refl = refl

ap2 : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C)
    → {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ b₁ : B}(b₂ : b₀ ≡ b₁)
    → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl = refl

coe2r : ∀{i j}{A : Set i}{B : A → Set j}{a₀ a₁ : A}
        (a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}
      → b₀ ≡[ ap B a₂ ]≡ b₁ → b₀ ≡ coe (ap B (a₂ ⁻¹)) b₁
coe2r refl p = p

--------------------------------------------------------------
-- sigma
--------------------------------------------------------------

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infixl 5 _,_

open Σ public

aptot : ∀{i}{A : Set i}{B : A → Set}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → _≡_ {A = Σ Set λ X → X} (B a₀ , f a₀) (B a₁ , f a₁)
aptot f refl = refl

Σ= : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
     (p : a ≡ a') → b ≡[ ap B p ]≡ b' → _≡_ {A = Σ A B} (a , b) (a' , b')
Σ= refl refl = refl

Σ=0 : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
    → _≡_ {A = Σ A B} (a , b) (a' , b') → a ≡ a'
Σ=0 refl = refl

Σ=1 : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
      (p : (a , b) ≡ (a' , b')) → b ≡[ ap B (Σ=0 p) ]≡ b'
Σ=1 refl = refl

Σ=η : ∀{i j}{A : Set i}{B : A → Set j}{w w' : Σ A B}
      (p : w ≡ w') → Σ= (Σ=0 p) (Σ=1 p) ≡ p
Σ=η refl = refl

Σ=β0 : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b') → Σ=0 (Σ= p q) ≡ p
Σ=β0 refl refl = refl

Σ=β1 : ∀{i j}{A : Set i}{B : A → Set j}{a a' : A}{b : B a}{b' : B a'}
       (p : a ≡ a')(q : b ≡[ ap B p ]≡ b')
     → Σ=1 (Σ= p q) ≡[ ap (λ r → b ≡[ ap B r ]≡ b') (Σ=β0 p q) ]≡ q
Σ=β1 refl refl = refl

Σ=' : {A₀ A₁ : Set}(A₂ : A₀ ≡ A₁){a₀ : A₀}{a₁ : A₁}(a₂ : a₀ ≡[ A₂ ]≡ a₁)
    → _≡_ {A = Σ Set λ X → X} (A₀ , a₀) (A₁ , a₁)
Σ=' A₂ {b₀}{b₁} b₂ = Σ= A₂ (coe (ap (λ z → b₀ ≡[ z ]≡ b₁) (apid A₂ ⁻¹)) b₂)

Σ=1' : {A₀ A₁ : Set}{a₀ : A₀}{a₁ : A₁}
     → (p : (A₀ , a₀) ≡ (A₁ , a₁)) → a₀ ≡[ Σ=0 p ]≡ a₁
Σ=1' refl = refl

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

--------------------------------------------------------------
-- top
--------------------------------------------------------------

record ⊤ : Set where
  constructor tt

--------------------------------------------------------------
-- bottom
--------------------------------------------------------------

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

--------------------------------------------------------------
-- disjoint union
--------------------------------------------------------------

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

--------------------------------------------------------------
-- function extensionality
--------------------------------------------------------------

postulate
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B

w-rec : ∀ {A B} (C : W A B → Set) → (∀ (a : A) (f : B a → W A B) → ((b : B a) → C (f b)) → C (sup a f)) → (w : W A B) → C w
w-rec C p (sup a f) = p a f (λ b → w-rec C p (f b))

data Bool : Set where
  tt ff : Bool

if_then_else_ : ∀ {i} {B : Bool → Set i} (b : Bool) → B tt → B ff → B b
if tt then pt else pf = pt
if ff then pt else pf = pf

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : A → ∀ {n} → Vec A n → Vec A (succ n)

data _≤_ (n : ℕ) : ℕ → Set where
  le-refl : n ≤ n
  le-step : ∀ {m} → n ≤ m → n ≤ (succ m)

fin : ℕ → Set
fin n = Σ ℕ (λ m → m ≤ n)
