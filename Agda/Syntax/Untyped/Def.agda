{-# OPTIONS --without-K #-}
module Syntax.Untyped.Def where
open import lib

-- data Tree (X : Set) : Set where
--   br : Tree X → Tree X → Tree X
--   leaf : X → Tree X

-- indtree : {X : Set} → (P : Tree X → Set)
--         → ((s t : Tree X) → P s → P t → P (br s t))
--         → ((x : X) → P (leaf x))
--         → (t : Tree X) → P t
-- indtree P b l (br s t) = b s t (indtree P b l s) (indtree P b l t)
-- indtree P b l (leaf x) = l x

infixl 5 _⊛_
infix 10 _⊕_
infix 100 *_
data Ptm : Set where
  typ : ℕ → Ptm
  bot : Ptm
  top : Ptm
  unt : Ptm
  pi : (X P : Ptm) → Ptm
  lam : (X b : Ptm) → Ptm
  sig : (X P : Ptm) → Ptm
  smk : Ptm → Ptm → Ptm
  pi1 : Ptm → Ptm
  pi2 : Ptm → Ptm
  _⊛_ : (f x : Ptm) → Ptm -- app
  τ : Ptm -- tree
  ℓ : Ptm -- leaf
  _⊕_ : (l r : Ptm) → Ptm -- branch
  ind : (P l b : Ptm) → Ptm
  exf : Ptm → Ptm
  *_  : ℕ → Ptm -- var

‘λ→’ = lam

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
lift d (ind P l b) = ind (lift d P) (lift d l) (lift d b)
lift d (exf X) = exf (lift d X)
lift d (* x) = d ≤? x |> (λ { (yes p) → * suc x ; (no ¬p) → * x })

w = lift 0

data subst-rel (d : ℕ) (v : Ptm) : Ptm → Ptm → Set where
  s-typ : ∀ {l} → subst-rel d v (typ l) (typ l)
  s-bot : subst-rel d v bot bot
  s-top : subst-rel d v top top
  s-unt : subst-rel d v unt unt
  s-pip : ∀ {X X' P P'} → subst-rel d v X X' → subst-rel (suc d) (lift 0 v) P P' → subst-rel d v (pi X P) (pi X' P')
  s-lam : ∀ {X X' b b'} → subst-rel d v X X' → subst-rel (suc d) (lift 0 v) b b' → subst-rel d v (lam X b) (lam X' b')
  s-sig : ∀ {X X' P P'} → subst-rel d v X X' → subst-rel (suc d) (lift 0 v) P P' → subst-rel d v (sig X P) (sig X' P')
  s-smk : ∀ {x x' p p'} → subst-rel d v x x' → subst-rel d v p p' → subst-rel d v (smk x p) (smk x' p')
  s-pi1 : ∀ {p p'} → subst-rel d v p p' → subst-rel d v (pi1 p) (pi1 p')
  s-pi2 : ∀ {p p'} → subst-rel d v p p' → subst-rel d v (pi2 p) (pi2 p')
  s-app : ∀ {f f' x x'} → subst-rel d v f f' → subst-rel d v x x' → subst-rel d v (f ⊛ x) (f' ⊛ x')
  s-btr : subst-rel d v τ τ
  s-ell : subst-rel d v ℓ ℓ
  s-brc : ∀ {l l' r r'} → subst-rel d v l l' → subst-rel d v r r' → subst-rel d v (l ⊕ r) (l' ⊕ r')
  s-ind : ∀ {P P' l l' b b'} → subst-rel d v P P' → subst-rel d v l l' → subst-rel d v b b' → subst-rel d v (ind P l b) (ind P' l' b')
  s-exf : ∀ {X X'} → subst-rel d v X X' → subst-rel d v (exf X) (exf X')
  s-var-eq : subst-rel d v (* d) v
  s-var-le : ∀ {i} → d < i → subst-rel d v (* i) (* pred i)
  s-var-ge : ∀ {i} → d > i → subst-rel d v (* i) (* i)

subst-fun : (d : ℕ) (v : Ptm) (e : Ptm) → Σ[ e' ∈ Ptm ] subst-rel d v e e'
subst-fun d v (typ x) = (typ x) , s-typ
subst-fun d v bot = bot , s-bot
subst-fun d v top = top , s-top
subst-fun d v unt = unt , s-unt
subst-fun d v (pi X P) with subst-fun d v X | subst-fun (suc d) (lift 0 v) P
... | X' , pX' | P' , pP' = pi X' P' , s-pip pX' pP'
subst-fun d v (lam X b) with subst-fun d v X | subst-fun (suc d) (lift 0 v) b
... | X' , pX' | b' , pb' = lam X' b' , s-lam pX' pb'
subst-fun d v (sig X P) with subst-fun d v X | subst-fun (suc d) (lift 0 v) P
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
subst-fun d v (ind P l b) with subst-fun d v P | subst-fun d v l | subst-fun d v b
... | P' , pP' | l' , pl' | r' , pr' = (ind P' l' r') , (s-ind pP' pl' pr')
subst-fun d v (exf P) with subst-fun d v P
... | P' , pP' = exf P' , s-exf pP'
subst-fun d v (* i) with compare d i
subst-fun d v (* .(suc (d + k))) | less .d k = (* (d + k)) , s-var-le ≤-+r
subst-fun d v (* .d) | equal .d = v , s-var-eq
subst-fun .(suc (i + k)) v (* i) | greater .i k = (* i) , s-var-ge ≤-+r

subst-v : ℕ → Ptm → Ptm → Ptm
subst-v d v e = proj₁ (subst-fun d v e)

-- proof only proceeds the easy way with K, not sure if it even remains true otherwise
-- might scrap the substitution relation if it's relevant
-- subst-irrel : ∀ {d v e e'} (p1 p2 : subst-rel d v e e') → p1 ≡ p2
-- subst-irrel s-typ s-typ = refl
-- subst-irrel s-bot s-bot = refl
-- subst-irrel s-top s-top = refl
-- subst-irrel s-unt s-unt = refl
-- subst-irrel (s-pip p1 p2) (s-pip p3 p4) rewrite subst-irrel p1 p3 | subst-irrel p2 p4 = refl
-- subst-irrel (s-lam p1 p2) (s-lam p3 p4) = {!!} -- proceed similarly later
-- subst-irrel (s-sig p1 p2) (s-sig p3 p4) = {!!}
-- subst-irrel (s-smk p1 p2) (s-smk p3 p4) = {!!}
-- subst-irrel (s-pi1 p1) (s-pi1 p2) = {!!}
-- subst-irrel (s-pi2 p1) (s-pi2 p2) = {!!}
-- subst-irrel (s-app p1 p2) (s-app p3 p4) = {!!}
-- subst-irrel s-btr s-btr = refl
-- subst-irrel s-ell s-ell = refl
-- subst-irrel (s-brc p1 p2) (s-brc p3 p4) = {!!}
-- subst-irrel (s-ind p1 p2 p3) (s-ind p4 p5 p6) = {!!}
-- subst-irrel (s-exf p1) (s-exf p2) = {!!}
-- subst-irrel s-var-eq s-var-eq = refl
-- subst-irrel s-var-eq (s-var-le x) = ⊥-elim (<-noref x)
-- subst-irrel s-var-eq (s-var-ge x) = ⊥-elim (<-noref x)
-- subst-irrel (s-var-le (s≤s x)) s-var-eq = ⊥-elim (<-noref x)
-- subst-irrel {d} {e = * suc n} (s-var-le (s≤s x)) (s-var-le (s≤s y)) = cong s-var-le (cong s≤s (≤-irrel x y))
-- subst-irrel (s-var-ge (s≤s z≤n)) (s-var-le ())
-- subst-irrel (s-var-ge (s≤s z≤n)) (s-var-ge (s≤s z≤n)) = refl
-- subst-irrel (s-var-ge (s≤s (s≤s x))) s-var-eq = ⊥-elim (<-noref x)
-- subst-irrel (s-var-ge (s≤s (s≤s x))) (s-var-ge (s≤s (s≤s y))) = cong s-var-ge (cong (s≤s ∘ s≤s) (≤-irrel x y))


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


lift-comm : ∀ {d1 d2} → d1 ≤ d2 → ∀ e → lift d1 (lift d2 e) ≡ lift (suc d2) (lift d1 e)
lift-comm p (typ x) = refl
lift-comm p bot = refl
lift-comm p top = refl
lift-comm p unt = refl
lift-comm p (pi X P) rewrite lift-comm p X | lift-comm (s≤s p) P = refl
lift-comm p (lam X b) rewrite lift-comm p X | lift-comm (s≤s p) b = refl
lift-comm p (sig X P) rewrite lift-comm p X | lift-comm (s≤s p) P = refl
lift-comm p (smk x e) rewrite lift-comm p x | lift-comm p e = refl
lift-comm p (pi1 e) rewrite lift-comm p e = refl
lift-comm p (pi2 e) rewrite lift-comm p e = refl
lift-comm p (f ⊛ x) rewrite lift-comm p f | lift-comm p x = refl
lift-comm p τ = refl
lift-comm p ℓ = refl
lift-comm p (l ⊕ r) rewrite lift-comm p l | lift-comm p r = refl
lift-comm p (ind P lc bc) rewrite lift-comm p P | lift-comm p lc | lift-comm p bc = refl
lift-comm p (exf X) rewrite lift-comm p X = refl
-- This... gets ugly. I feel like there is a more elegant way to do this, but I don't know it
lift-comm {d1} {d2} p (* x) with d1 ≤? x
lift-comm {d1} {d2} p (* x) | yes p₁ with d2 ≤? x
lift-comm {d1} {d2} p (* x) | yes p₁ | yes p₂ with d1 ≤? x
lift-comm {d1} {d2} p (* x) | yes p₁ | yes p₂ | yes p₃ with d1 ≤? suc x
lift-comm {d1} {d2} p (* x) | yes p₁ | yes p₂ | yes p₃ | yes p₄ = refl
lift-comm {d1} {d2} p (* x) | yes p₁ | yes p₂ | yes p₃ | no ¬p₄ = ⊥-elim (¬p₄ $ ≤-step p₁)
lift-comm {d1} {d2} p (* x) | yes p₁ | yes p₂ | no ¬p₃ = ⊥-elim (¬p₃ p₁)
lift-comm {d1} {d2} p (* x) | yes p₁ | no ¬p₂ with d1 ≤? x
lift-comm {d1} {d2} p (* x) | yes p₁ | no ¬p₂ | yes p₃ = refl
lift-comm {d1} {d2} p (* x) | yes p₁ | no ¬p₂ | no ¬p₃ = ⊥-elim (¬p₃ p₁)
lift-comm {d1} {d2} p (* x) | no ¬p₁ with d2 ≤? x
lift-comm {d1} {d2} p (* x) | no ¬p₁ | yes p₂ = ⊥-elim (¬p₁ $ p ≤-trans p₂)
lift-comm {d1} {d2} p (* x) | no ¬p₁ | no ¬p₂ with d1 ≤? x
lift-comm {d1} {d2} p (* x) | no ¬p₁ | no ¬p₂ | yes p₃ = ⊥-elim (¬p₁ p₃)
lift-comm {d1} {d2} p (* x) | no ¬p₁ | no ¬p₂ | no ¬p₃ with suc d2 ≤? x
lift-comm {d1} {d2} p (* x) | no ¬p₁ | no ¬p₂ | no ¬p₃ | yes p₄ = ⊥-elim (¬p₁ $ p ≤-trans ≤-step ≤-refl ≤-trans p₄)
lift-comm {d1} {d2} p (* x) | no ¬p₁ | no ¬p₂ | no ¬p₃ | no ¬p₄ = refl

lift-lift : ∀ n m e → lift n (lift (n + m) e) ≡ lift (suc (n + m)) (lift n e)
lift-lift n m = lift-comm ≤-+r

lift-w-comm : ∀ d e → w (lift d e) ≡ lift (suc d) (w e)
lift-w-comm d e = lift-comm z≤n e
