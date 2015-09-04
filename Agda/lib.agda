{-# OPTIONS --without-K #-}

module lib where
open import Level public renaming (_⊔_ to lmax; suc to lsuc; zero to lzero; lift to ulift)
open import Data.Nat public
open import Relation.Binary public
open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality public renaming ([_] to ⟨_⟩)
open import Relation.Nullary public
open import Data.Product public hiding (map; zip)
open import Data.List public
open import Function public
open import Data.Empty public
open import Data.Maybe.Base public hiding (map)

--------------------------------------------------------------
-- unsafe
--------------------------------------------------------------
postulate ⋆⋆TODO⋆⋆ : ∀ {i}{A : Set i} → A

--------------------------------------------------------------
-- unit
--------------------------------------------------------------
record ⊤ : Set where
  constructor tt

--------------------------------------------------------------
-- level
--------------------------------------------------------------
levelℕ : ℕ → Level
levelℕ zero = lzero
levelℕ (suc n) = lsuc (levelℕ n)

--------------------------------------------------------------
-- pi
--------------------------------------------------------------
Π : ∀{i j}(A : Set i) → (A → Set j) → Set (lmax i j)
Π A B = (x : A) → B x

--------------------------------------------------------------
-- equality
--------------------------------------------------------------
{-# BUILTIN REWRITE _≡_ #-}

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

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

≡inv-r : ∀{i}{A : Set i} {x y : A} (p : x ≡ y) → (p ◾ p ⁻¹) ≡ refl
≡inv-r refl = refl

≡inv-l : ∀{i}{A : Set i} {x y : A} (p : x ≡ y) → (p ⁻¹ ◾ p) ≡ refl
≡inv-l refl = refl

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

match_withl_withr_ : ∀ {i j}{X : Set i}{Y : Set j} → (Dec X) → (X → Y) → (¬ X → Y) → Y
match yes p withl p1 withr p2 = p1  p
match no ¬p withl p1 withr p2 = p2 ¬p

hedberg : ∀ {i}{A : Set i} → ((x y : A) → Dec (x ≡ y)) → {x y : A} → (p q : x ≡ y) → p ≡ q
hedberg {i} {A} d {x} {.x} refl q with d x x | lemma q
                                  where T : {x y : A} → x ≡ y → Set i
                                        T {x} {y} p = match d x y withl (λ b → match d x x withl (λ b' → p ≡ (b' ⁻¹ ◾ b))
                                                                                           withr (λ ¬p → ⊥-elim (¬p refl)))
                                                                  withr (λ ¬b → ⊥-elim (¬b p))
                                        lemma : {x y : A} → (p : x ≡ y) → T p
                                        lemma {x} refl with (d x x)
                                        lemma refl | yes p = ≡inv-l p ⁻¹
                                        lemma refl | no ¬p = ⊥-elim (¬p refl)
hedberg d refl .(p ⁻¹ ◾ p) | yes p | refl = ≡inv-l p ⁻¹
hedberg d refl q | no ¬p | _ = ⊥-elim (¬p q)

ℕ≡irrel : ∀ {x y : ℕ} → (p q : x ≡ y) → p ≡ q
ℕ≡irrel = hedberg _≟_

ℕK : ∀ {x : ℕ}(p : x ≡ x) → p ≡ refl
ℕK p = ℕ≡irrel p refl

--------------------------------------------------------------
-- sigma
--------------------------------------------------------------

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

¬-prop : ∀ {i}{X : Set i}(f g : ¬ X) → f ≡ g
¬-prop f g = funext (λ x → ⊥-elim (f x))

--------------------------------------------------------------
-- nats
--------------------------------------------------------------

-- some basic identities
+0r : ∀ n → n + zero ≡ n
+0r zero = refl
+0r (suc n) = cong suc (+0r n)

_+S_ : ∀ n m → n + suc m ≡ suc (n + m)
zero +S m = refl
suc n +S m = cong suc (n +S m)

-- injectivity
suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

-- ordering
≤-step : ∀ {n m} → n ≤ m → n ≤ suc m
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

infixl 5 _≤-trans_

_≤-trans_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
z≤n ≤-trans p2 = z≤n
s≤s p1 ≤-trans s≤s p2 = s≤s (p1 ≤-trans p2)

le-of-lt : ∀ {x y} → x < y → x ≤ y
le-of-lt (s≤s p) = ≤-step p

le'-le : _≤′_ ⇒ _≤_
le'-le ≤′-refl = ≤-refl
le'-le (≤′-step p) = ≤-step (le'-le p)

le''-le' : _≤″_ ⇒ _≤′_
le''-le' {i} (less-than-or-equal {0} refl) rewrite +0r i = ≤′-refl
le''-le' {i} (less-than-or-equal {suc k} refl) rewrite i +S k = ≤′-step (le''-le' (less-than-or-equal refl))

le-le'' : _≤_ ⇒ _≤″_
le-le'' z≤n = less-than-or-equal refl
le-le'' (s≤s p) with le-le'' p
le-le'' (s≤s p) | less-than-or-equal proof = less-than-or-equal (cong suc proof)

le''-le : _≤″_ ⇒ _≤_
le''-le p = le'-le (le''-le' p)

le'-le'' : _≤′_ ⇒ _≤″_
le'-le'' p = le-le'' (le'-le p)

le-le' : _≤_ ⇒ _≤′_
le-le' p = le''-le' (le-le'' p)

≤-+r : ∀ {n k} → n ≤ n + k
≤-+r = le''-le (less-than-or-equal refl)

≤-+l : ∀ {n k} → n ≤ k + n
≤-+l {k = 0} = ≤-refl
≤-+l {k = suc k} = ≤-step (≤-+l {k = k})

_≠Sn+_ : ∀ n k → n ≢ suc n + k
_≠Sn+_ 0 k ()
_≠Sn+_ (suc n) k p = (n ≠Sn+ k) (suc-inj p)

_≤-antisym_ : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
z≤n ≤-antisym z≤n = refl
s≤s p1 ≤-antisym s≤s p2 = cong suc (p1 ≤-antisym p2)

<-nosym : ∀ {n m} → n < m → n ≯ m
<-nosym (s≤s p1) (s≤s p2) = <-nosym p1 p2

≤<-nosym : ∀ {n m} → n ≥ m → n ≮ m
≤<-nosym z≤n ()
≤<-nosym (s≤s p1) (s≤s p2) = ≤<-nosym p1 p2

<-noref : ∀ {n} → n ≮ n
<-noref p = <-nosym p p

≤-trich : Trichotomous _≡_ _<_
≤-trich n m with compare n m
≤-trich n .(suc (n + k)) | less .n k = tri< ≤-+r (n ≠Sn+ k) (<-nosym ≤-+r)
≤-trich n .n | equal .n = tri≈ <-noref refl <-noref
≤-trich .(suc (m + k)) m | greater .m k = tri> (<-nosym ≤-+r) ((m ≠Sn+ k) ∘ sym) ≤-+r

≤-irrel : ∀ {n m} (p1 p2 : n ≤ m) → p1 ≡ p2
≤-irrel z≤n z≤n = refl
≤-irrel (s≤s p1) (s≤s p2) = cong s≤s (≤-irrel p1 p2)

<-noref-j : {x y : ℕ} → x < y → x ≢ y
<-noref-j p refl = <-noref p

≤-trich-c1 : ∀ {n m} (p : n < m) → ≤-trich n m ≡ tri< p (<-noref-j p) (<-nosym p)
≤-trich-c1 {n} {m} p with ≤-trich n m
≤-trich-c1 p | tri< a ¬b ¬c rewrite ≤-irrel p a | ¬-prop (<-noref-j a) ¬b | ¬-prop (<-nosym a) ¬c = refl
≤-trich-c1 p | tri≈ ¬a b ¬c = ⊥-elim (¬a p)
≤-trich-c1 p | tri> ¬a ¬b c = ⊥-elim (¬a p)

≤-trich-c2 : ∀ {n} → ≤-trich n n ≡ tri≈ <-noref refl <-noref
≤-trich-c2 {n} with ≤-trich n n
≤-trich-c2 | tri< a ¬b ¬c = ⊥-elim (¬b refl)
≤-trich-c2 | tri≈ ¬a b ¬c rewrite ¬-prop ¬a <-noref | ℕ≡irrel b refl | ¬-prop ¬c <-noref = refl
≤-trich-c2 | tri> ¬a ¬b c = ⊥-elim (¬b refl)

≤-trich-c3 : ∀ {n m} (p : n > m) → ≤-trich n m ≡ tri> (<-nosym p) (<-noref-j p ∘ _⁻¹) p
≤-trich-c3 {n} {m} p with ≤-trich n m
≤-trich-c3 p | tri< a ¬b ¬c = ⊥-elim (¬c p)
≤-trich-c3 p | tri≈ ¬a b ¬c = ⊥-elim (¬c p)
≤-trich-c3 p | tri> ¬a ¬b c rewrite ¬-prop ¬a (<-nosym p) | ¬-prop ¬b (<-noref-j p ∘ _⁻¹) | ≤-irrel p c = refl

≤?-c1 : ∀ {n m} (p : n ≤ m) → (n ≤? m) ≡ yes p
≤?-c1 {n} {m} p with n ≤? m
... | yes q = ap yes (≤-irrel q p)
... | no ¬q = ⊥-elim (¬q p)

≤?-c2 : ∀ {n m} (p : n ≰ m) → (n ≤? m) ≡ no p
≤?-c2 {n} {m} ¬p with n ≤? m
... | yes q = ⊥-elim (¬p q)
... | no ¬q = ap no (¬-prop ¬q ¬p)

--------------------------------------------------------------
-- Trees
--------------------------------------------------------------
infix 25 _⊕_
data Tree : Set where
  _⊕_ : Tree → Tree → Tree
  ℓ : Tree

tree-ind : ∀{i}(P : Tree → Set i)
           → P ℓ
           → ((l r : Tree) → P l → P r → P (l ⊕ r))
           → (t : Tree) → P t
tree-ind P pl pb (l ⊕ r) = pb l r (tree-ind P pl pb l) (tree-ind P pl pb r)
tree-ind P pl pb ℓ = pl
--------------------------------------------------------------
-- Lists
--------------------------------------------------------------
lookup : ∀ {i} {X : Set i} → ℕ → List X → Maybe X
lookup n [] = nothing
lookup zero (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n xs

lookup-le : ∀ {l}{X : Set l} i (xs : List X) → i < length xs → X
lookup-le i [] ()
lookup-le zero (x ∷ xs) (s≤s p) = x
lookup-le (suc i) (x ∷ xs) (s≤s p) = lookup-le i xs p
