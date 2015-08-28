{-# OPTIONS --without-K #-}
module Syntax.Untyped.Subst-Lemmas where
open import lib
open import Syntax.Untyped.Def

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
lift-comm p (ind P lc bc) rewrite lift-comm (s≤s p) P | lift-comm p lc | lift-comm p bc = refl
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

subst-lift : ∀ d v e → subst-v d v (lift d e) ≡ e
subst-lift d v (typ x) = refl
subst-lift d v bot = refl
subst-lift d v top = refl
subst-lift d v unt = refl
subst-lift d v (pi  A B) rewrite subst-lift d v A | subst-lift (suc d) (w v) B = refl
subst-lift d v (lam A b) rewrite subst-lift d v A | subst-lift (suc d) (w v) b = refl
subst-lift d v (sig A B) rewrite subst-lift d v A | subst-lift (suc d) (w v) B = refl
subst-lift d v (smk a b) rewrite subst-lift d v a | subst-lift d v b = refl
subst-lift d v (pi1 p) = ap pi1 (subst-lift d v p)
subst-lift d v (pi2 p) = ap pi2 (subst-lift d v p)
subst-lift d v (f ⊛ x) rewrite subst-lift d v f | subst-lift d v x = refl
subst-lift d v τ = refl
subst-lift d v ℓ = refl
subst-lift d v (l ⊕ r) rewrite subst-lift d v l | subst-lift d v r = refl
subst-lift d v (ind P lc bc) rewrite subst-lift (suc d) (w v) P | subst-lift d v lc | subst-lift d v bc = refl
subst-lift d v (exf X) = ap exf (subst-lift d v X)
-- oh no... not this again...
subst-lift d v (* i) with d ≤? i
subst-lift d v (* i) | yes p₁ with compare d (suc i)
subst-lift d v (* .(d + k)) | yes p | less .d k = refl
subst-lift .(suc i) v (* i) | yes p | equal .(suc i) = ⊥-elim (<-noref p)
subst-lift .(suc (suc (i + k))) v (* i) | yes p | greater .(suc i) k = ⊥-elim (<-nosym p ≤-+r)
subst-lift d v (* i) | no ¬p with compare d i
subst-lift d v (* .(suc (d + k))) | no ¬p | less .d k = ⊥-elim (¬p (≤-step ≤-+r))
subst-lift d v (* .d) | no ¬p | equal .d = ⊥-elim (¬p ≤-refl)
subst-lift .(suc (i + k)) v (* i) | no ¬p | greater .i k = refl
-- actually, that was fairly painless

lift-subst : ∀ {d1 d2} (p : d2 ≤ d1) v e → lift d1 (subst-v d2 v e) ≡ subst-v d2 (lift d1 v) (lift (suc d1) e)
lift-subst {d1} p v (typ x) = refl
lift-subst {d1} p v bot = refl
lift-subst {d1} p v top = refl
lift-subst {d1} p v unt = refl
lift-subst {d1} p v (pi  A B) rewrite lift-subst p v A | lift-subst (s≤s p) (w v) B | lift-w-comm d1 v = refl
lift-subst {d1} p v (lam A b) rewrite lift-subst p v A | lift-subst (s≤s p) (w v) b | lift-w-comm d1 v = refl
lift-subst {d1} p v (sig A B) rewrite lift-subst p v A | lift-subst (s≤s p) (w v) B | lift-w-comm d1 v = refl
lift-subst {d1} p v (smk a b) rewrite lift-subst p v a | lift-subst p v b = refl
lift-subst {d1} p v (pi1 e) = ap pi1 (lift-subst p v e)
lift-subst {d1} p v (pi2 e) = ap pi2 (lift-subst p v e)
lift-subst {d1} p v (f ⊛ x) rewrite lift-subst p v f | lift-subst p v x = refl
lift-subst {d1} p v τ = refl
lift-subst {d1} p v ℓ = refl
lift-subst {d1} p v (l ⊕ r) rewrite lift-subst p v l | lift-subst p v r = refl
lift-subst {d1} p v (ind P lc bc) rewrite lift-subst (s≤s p) (w v) P | lift-lift 0 d1 v | lift-subst p v lc | lift-subst p v bc = refl
lift-subst {d1} p v (exf X) = ap exf (lift-subst p v X)
lift-subst {d1} {d2} p v (* i) with ≤-trich d2 i
lift-subst {d1} p v (* ._) | tri< (s≤s {d2} {i} a) ¬b ¬c with d1 ≤? i
lift-subst p v (* ._) | tri< (s≤s {d2} {i} a) ¬b ¬c | yes q rewrite ≤-trich-c1 (s≤s $ ≤-step a) = refl
lift-subst p v (* ._) | tri< (s≤s {d2} {i} a) ¬b ¬c | no ¬q rewrite ≤-trich-c1 (s≤s a) = refl
lift-subst {d1} p v (* i) | tri≈ ¬a refl ¬c rewrite ≤?-c2 {suc d1} {i} (λ q → <-noref-j q (suc-inj (≤-step q ≤-antisym s≤s p))) | ≤-trich-c2 {i} = refl
lift-subst {d1} p v (* .i) | tri> ¬a ¬b (s≤s {i} {d2} c) rewrite ≤?-c2 {d1} {i} (λ q → ≤<-nosym c (p ≤-trans q))
                                                               | ≤?-c2 {suc d1} {i} (λ q → ≤<-nosym c (≤-step p ≤-trans q))
                                                               | ≤-trich-c3 {suc d2} {i} (s≤s c) = refl


lift^_++_ : ∀ n m {d} {e} → lift^ (n + m) at d of e ≡ lift^ n at d of lift^ m at d of e
lift^ zero  ++ m = refl
lift^ suc n ++ m = cong (lift _) (lift^ n ++ m)

lift^-subst : ∀ n {d1 d2} (p : d2 ≤ d1) v e → lift^ n at d1 of subst-v d2 v e ≡ subst-v d2 (lift^ n at d1 of v) (lift^ n at (suc d1) of e)
lift^-subst zero p v e = refl
lift^-subst (suc n) {d1} {d2} p v e rewrite lift-subst p (lift^ n at d1 of v) (lift^ n at suc d1 of e) ⁻¹ = cong (lift d1) (lift^-subst n p v e)

depth : Ptm → ℕ
depth (pi  A B) = depth A ⊔ depth B
depth (lam A b) = depth A ⊔ pred (depth b)
depth (sig A B) = depth A ⊔ pred (depth B)
depth (smk a b) = depth a ⊔ depth b
depth (pi1 a) = depth a
depth (pi2 b) = depth b
depth (f ⊛ x) = depth f ⊔ depth x
depth (l ⊕ r) = depth l ⊔ depth r
depth (ind P lc bc) = pred (depth P) ⊔ depth lc ⊔ depth bc
depth (exf f) = depth f
depth (* i) = suc i
depth _ = 0

subst-subst : ∀ {d1 d2} (p : d2 ≤ d1) v1 v2 e → subst-v d2 v2 (subst-v (suc d1) v1 e) ≡ subst-v d1 (subst-v d2 v2 v1) (subst-v d2 v2 e)
subst-subst p v1 v2 (typ x) = {!!}
subst-subst p v1 v2 bot = {!!}
subst-subst p v1 v2 top = {!!}
subst-subst p v1 v2 unt = {!!}
subst-subst p v1 v2 (pi e e₁) = {!!}
subst-subst p v1 v2 (lam e e₁) = {!!}
subst-subst p v1 v2 (sig e e₁) = {!!}
subst-subst p v1 v2 (smk e e₁) = {!!}
subst-subst p v1 v2 (pi1 e) = {!!}
subst-subst p v1 v2 (pi2 e) = {!!}
subst-subst p v1 v2 (e ⊛ e₁) = {!!}
subst-subst p v1 v2 τ = {!!}
subst-subst p v1 v2 ℓ = {!!}
subst-subst p v1 v2 (e ⊕ e₁) = {!!}
subst-subst p v1 v2 (ind e e₁ e₂) = {!!}
subst-subst p v1 v2 (exf e) = {!!}
subst-subst {d1} {d2} p v1 v2 (* x) with ≤-trich d2 x
subst-subst p v1 v2 (* x) | tri< a ¬b ¬c = {!!}
subst-subst p v1 v2 (* i) | tri≈ ¬a refl ¬c rewrite ≤-trich-c3 (s≤s p) | ≤-trich-c2 {i} = {!!}
subst-subst p v1 v2 (* x) | tri> ¬a ¬b c rewrite ≤-trich-c3 (c ≤-trans ≤-step p) | ≤-trich-c3 c | ≤-trich-c3 (c ≤-trans p) = refl
