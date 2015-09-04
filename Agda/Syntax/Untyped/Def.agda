{-# OPTIONS --without-K #-}
module Syntax.Untyped.Def where
open import lib

infixl 100 _⊛_
infix 50 _⊕_
infix 1000 *_

data Ptm : Set where
  typ : ℕ → Ptm
  bot : Ptm
  exf : Ptm → Ptm
  top : Ptm
  unt : Ptm
  pi  : Ptm → Ptm → Ptm
  lam : Ptm → Ptm → Ptm
  _⊛_ : Ptm → Ptm → Ptm
  sig : Ptm → Ptm → Ptm
  smk : Ptm → Ptm → Ptm
  pi1 : Ptm → Ptm
  pi2 : Ptm → Ptm
  τ : Ptm -- tree
  ℓ : Ptm -- leaf
  _⊕_ : Ptm → Ptm → Ptm -- branch
  ind : (P lc bc : Ptm) → Ptm
  *_  : ℕ → Ptm -- var

infixl 1 _|>_
_|>_ : ∀ {i j}{X : Set i}{P : X → Set j}
       → (x : X)(f : ∀ x → P x) → P x
x |> f = f x

lift : ℕ → Ptm → Ptm
lift d (typ l) = typ l
lift d bot = bot
lift d top = top
lift d unt = unt
lift d (pi X P) = pi (lift d X) (lift (suc d) P)
lift d (lam X b) = lam (lift d X) (lift (suc d) b)
lift d (sig X P) = sig (lift d X) (lift (suc d) P)
lift d (smk x p) = smk (lift d x) (lift d p)
lift d (pi1 p) = pi1 (lift d p)
lift d (pi2 p) = pi2 (lift d p)
lift d (f ⊛ x) = lift d f ⊛ lift d x
lift d τ = τ
lift d ℓ = ℓ
lift d (l ⊕ r) = lift d l ⊕ lift d r
lift d (ind P l b) = ind (lift (suc d) P) (lift d l) (lift d b)
lift d (exf X) = exf (lift d X)
lift d (* x) with d ≤? x
... | yes p = * suc x
... | no ¬p = * x

infixr 500 lift^_at_of_
lift^_at_of_ : ℕ → ℕ → Ptm → Ptm
lift^ zero  at d of e = e
lift^ suc n at d of e = lift d (lift^ n at d of e)

w = lift 0

w^ : ℕ → Ptm → Ptm
w^ n e = lift^ n at 0 of e

data subst-rel (d : ℕ) (v : Ptm) : Ptm → Ptm → Set where
  s-typ : ∀ {l} → subst-rel d v (typ l) (typ l)
  s-bot : subst-rel d v bot bot
  s-top : subst-rel d v top top
  s-unt : subst-rel d v unt unt
  s-pip : ∀ {X X' P P'} → subst-rel d v X X' → subst-rel (suc d) (w v) P P' → subst-rel d v (pi X P) (pi X' P')
  s-lam : ∀ {X X' b b'} → subst-rel d v X X' → subst-rel (suc d) (w v) b b' → subst-rel d v (lam X b) (lam X' b')
  s-sig : ∀ {X X' P P'} → subst-rel d v X X' → subst-rel (suc d) (w v) P P' → subst-rel d v (sig X P) (sig X' P')
  s-smk : ∀ {x x' p p'} → subst-rel d v x x' → subst-rel d v p p' → subst-rel d v (smk x p) (smk x' p')
  s-pi1 : ∀ {p p'} → subst-rel d v p p' → subst-rel d v (pi1 p) (pi1 p')
  s-pi2 : ∀ {p p'} → subst-rel d v p p' → subst-rel d v (pi2 p) (pi2 p')
  s-app : ∀ {f f' x x'} → subst-rel d v f f' → subst-rel d v x x' → subst-rel d v (f ⊛ x) (f' ⊛ x')
  s-btr : subst-rel d v τ τ
  s-ell : subst-rel d v ℓ ℓ
  s-brc : ∀ {l l' r r'} → subst-rel d v l l' → subst-rel d v r r' → subst-rel d v (l ⊕ r) (l' ⊕ r')
  s-ind : ∀ {P P' l l' b b'} → subst-rel (suc d) (w v) P P' → subst-rel d v l l' → subst-rel d v b b' → subst-rel d v (ind P l b) (ind P' l' b')
  s-exf : ∀ {X X'} → subst-rel d v X X' → subst-rel d v (exf X) (exf X')
  s-var-eq : subst-rel d v (* d) v
  s-var-lt : ∀ {i} → d < i → subst-rel d v (* i) (* pred i)
  s-var-gt : ∀ {i} → d > i → subst-rel d v (* i) (* i)

subst-fun : (d : ℕ) (v : Ptm) (e : Ptm) → Σ[ e' ∈ Ptm ] subst-rel d v e e'
subst-fun d v (typ x) = (typ x) , s-typ
subst-fun d v bot = bot , s-bot
subst-fun d v top = top , s-top
subst-fun d v unt = unt , s-unt
subst-fun d v (pi X P) with subst-fun d v X | subst-fun (suc d) (w v) P
... | X' , pX' | P' , pP' = pi X' P' , s-pip pX' pP'
subst-fun d v (lam X b) with subst-fun d v X | subst-fun (suc d) (w v) b
... | X' , pX' | b' , pb' = lam X' b' , s-lam pX' pb'
subst-fun d v (sig X P) with subst-fun d v X | subst-fun (suc d) (w v) P
... | X' , pX' | P' , pP' = sig X' P' , s-sig pX' pP'
subst-fun d v (smk x p) with subst-fun d v x | subst-fun d v p
... | x' , px' | p' , pp' = smk x' p' , s-smk px' pp'
subst-fun d v (pi1 p) with subst-fun d v p
... | p' , pp' = pi1 p' , s-pi1 pp'
subst-fun d v (pi2 p) with subst-fun d v p
... | p' , pp' = pi2 p' , s-pi2 pp'
subst-fun d v (f ⊛ x) with subst-fun d v f | subst-fun d v x
... | f' , pf' | x' , px' = (f' ⊛ x') , s-app pf' px'
subst-fun d v τ = τ , s-btr
subst-fun d v ℓ = ℓ , s-ell
subst-fun d v (l ⊕ r) with subst-fun d v l | subst-fun d v r
... | l' , pl' | r' , pr' = (l' ⊕ r') , (s-brc pl' pr')
subst-fun d v (ind P l b) with subst-fun (suc d) (w v) P | subst-fun d v l | subst-fun d v b
... | P' , pP' | l' , pl' | r' , pr' = (ind P' l' r') , (s-ind pP' pl' pr')
subst-fun d v (exf P) with subst-fun d v P
... | P' , pP' = exf P' , s-exf pP'
subst-fun d v (* i) with ≤-trich d i
subst-fun d v (* i) | tri< a ¬b ¬c = (* pred i) , s-var-lt a
subst-fun d v (* .d) | tri≈ ¬a refl ¬c = v , s-var-eq
subst-fun d v (* i) | tri> ¬a ¬b c = * i , s-var-gt c

subst-v : ℕ → Ptm → Ptm → Ptm
subst-v d v e = proj₁ (subst-fun d v e)

subst₀ : Ptm → Ptm → Ptm
subst₀ = subst-v 0

-- small step evaluation relation

-- now comes the question - quotient over this (Ptm / step) or just add these equalities as postulates?
-- let's try postulates for now, and see how it goes

-- infix 1 _⟹_
-- data _⟹_ : Ptm → Ptm → Set where
postulate
  e-pi1 : ∀ {p1 p2} → pi1 (smk p1 p2) ≡ p1
  e-pi2 : ∀ {p1 p2} → pi2 (smk p1 p2) ≡ p2
  e-app-lam : ∀ {X b x} → lam X b ⊛ x ≡ subst-v 0 x b
  e-app-ind-l : ∀ {P lc bc} → ind P lc bc ⊛ ℓ ≡ lc
  e-app-ind-r : ∀ {P lc bc l r} → ind P lc bc ⊛ (l ⊕ r) ≡ bc ⊛ (ind P lc bc ⊛ l) ⊛ (ind P lc bc ⊛ r)
  trunc : ∀ {x y : Ptm} (p q : x ≡ y) → p ≡ q -- set truncation, because we don't care about the equality proof
  --   e-app-l : ∀ {f f' x} → f ⟹ f' → f ⊛ x ⟹ f' ⊛ x
  --   e-app-r : ∀ {f x x'} → x ⟹ x' → f ⊛ x ⟹ f ⊛ x'
  --   e-btr-l : ∀ {l l' r} → l ⟹ l' → l ⊕ r ⟹ l' ⊕ r
  --   e-btr-r : ∀ {l r r'} → r ⟹ r' → l ⊕ r ⟹ l ⊕ r'

-- {-# BUILTIN REWRITE _⟹_ #-}
{-# REWRITE e-pi1 #-}
{-# REWRITE e-pi2 #-}
{-# REWRITE e-app-lam #-}
{-# REWRITE e-app-ind-l #-}
{-# REWRITE e-app-ind-r #-}

-- because of rewrites, it's actually even more convenient than the average HIT
resp-pi1 : ∀ {P : Ptm → Set}{p1 p2} (f : ∀ p → P p) → f (pi1 (smk p1 p2)) ≡ f p1 -- look Ma, no transports
resp-pi1 f = refl

data value : Ptm → Set where
  v-typ : ∀ {n} → value (typ n)
  v-bot : value bot
  v-top : value top
  v-unt : value unt
  v-pi  : ∀ {X P} → value X → value (pi X P)
  v-lam : ∀ {X b} → value X → value (lam X b)
  v-sig : ∀ {X P} → value X → value (sig X P)
  v-btr : value τ
  v-ell : value ℓ
  v-br  : ∀ {l r} → value l → value r → value (l ⊕ r)
  v-ind : ∀ {P l b} → value P → value l → value b → value (ind P l b)
  v-exf : ∀ {X} → value X → value (exf X)

infixl 100 _⍟_
_⍟_ : Ptm → Ptm → Ptm
e ⍟ v = subst₀ v e

infixr 25 _⇨_
_⇨_ = pi

Con : Set
Con = List Ptm

lookup-w : ∀ i (Γ : Con) → i < length Γ → Ptm
lookup-w i [] ()
lookup-w zero (x ∷ Γ) (s≤s p) = w x
lookup-w (suc i) (x ∷ Γ) (s≤s p) = w (lookup-w i Γ p)
