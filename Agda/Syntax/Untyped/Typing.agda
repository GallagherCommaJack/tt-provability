{-# OPTIONS --without-K #-}
module Syntax.Untyped.Typing where
open import lib
open import Syntax.Untyped.Def
open import Syntax.Untyped.Subst-Lemmas

infix 1 _⊢_∈_
data _⊢_∈_ (Γ : Con) : Ptm → Ptm → Set where
  t-typ : ∀ {n} → Γ ⊢ typ n ∈ typ (suc n)
  t-bot : ∀ {n} → Γ ⊢ bot ∈ typ n
  t-top : ∀ {n} → Γ ⊢ top ∈ typ n
  t-unt : Γ ⊢ unt ∈ top
  t-pi  : ∀ {n m A B} → Γ ⊢ A ∈ typ n → (A ∷ Γ) ⊢ B ∈ typ m → Γ ⊢ pi  A B ∈ typ (n ⊔ m)
  t-lam : ∀ {m X B b} → Γ ⊢ pi X B ∈ typ m → (X ∷ Γ) ⊢ b ∈ B → Γ ⊢ lam X b ∈ pi X B
  t-sig : ∀ {n m A B} → Γ ⊢ A ∈ typ n → (A ∷ Γ) ⊢ B ∈ typ m → Γ ⊢ sig A B ∈ typ (n ⊔ m)
  t-smk : ∀ {a b A B m} → Γ ⊢ sig A B ∈ typ m → Γ ⊢ a ∈ A → Γ ⊢ b ∈ B ⍟ a → Γ ⊢ smk a b ∈ sig A B
  t-pi1 : ∀ {p A B} → Γ ⊢ p ∈ sig A B → Γ ⊢ pi1 p ∈ A
  t-pi2 : ∀ {p A B} → Γ ⊢ p ∈ sig A B → Γ ⊢ pi2 p ∈ B ⍟ pi1 p
  t-app : ∀ {A B f a} → Γ ⊢ f ∈ pi A B → Γ ⊢ a ∈ A → Γ ⊢ f ⊛ a ∈ (B ⍟ a)
  t-btr : ∀ {n} → Γ ⊢ τ ∈ typ n
  t-ell : Γ ⊢ ℓ ∈ τ
  t-brc : ∀ {l r} → Γ ⊢ l ∈ τ → Γ ⊢ r ∈ τ → Γ ⊢ l ⊕ r ∈ τ
  t-ind : ∀ {P l b n} → τ ∷ Γ ⊢ P ∈ typ n
                      → Γ ⊢ l ∈ P ⍟ ℓ
                      → Γ ⊢ b ∈ τ   ⇨ τ
                              ⇨ (lift^ 2 at 1 of P) ⍟ * 1
                              ⇨ (lift^ 3 at 1 of P) ⍟ * 1
                              ⇨ (lift^ 4 at 1 of P) ⍟ (* 2 ⊕ * 3)
                      → Γ ⊢ ind P l b ∈ pi τ P
  t-exf : ∀ {X n} → Γ ⊢ X ∈ typ n → Γ ⊢ exf X ∈ pi bot (w X)
  t-var : ∀ {i n} (p : i < length Γ) → drop (suc i) Γ ⊢ lookup i Γ p ∈ typ n → Γ ⊢ * i ∈ lookup-w i Γ p
  -- these rules are unnecessary because the typechecker has already internalized the evaluation equations
  -- t-eval-to : ∀ {x X X'} → X ⟹ X' → Γ ⊢ x ∈ X → Γ ⊢ x ∈ X'
  -- t-eval-from : ∀ {x X X'} → X ⟹ X' → Γ ⊢ x ∈ X' → Γ ⊢ x ∈ X
  -- Hooray for ETT!

t-vz : ∀ {Γ X n} → Γ ⊢ X ∈ typ n → (X ∷ Γ) ⊢ * 0 ∈ w X
t-vz p = t-var (s≤s z≤n) p

t-vs : ∀ {Γ X Y i} → Γ ⊢ * i ∈ X → (Y ∷ Γ) ⊢ * suc i ∈ w X
t-vs (t-var p₁ p₂) = t-var (s≤s p₁) p₂

infix 50 insert_at_of_

insert_at_of_ : Ptm → ℕ → Con → Con
insert v at zero of Γ = v ∷ Γ
insert v at suc i of [] = [ v ]
insert v at suc i of (x ∷ Γ) = lift i x ∷ insert v at i of Γ

typ-Γ≡ : ∀ {Γ x X X'} → X ≡ X' → Γ ⊢ x ∈ X → Γ ⊢ x ∈ X'
typ-Γ≡ refl = id

tm-Γ≡ : ∀ {Γ x x' X} → x ≡ x' → Γ ⊢ x ∈ X → Γ ⊢ x' ∈ X
tm-Γ≡ refl = id

t-lift-v : ∀ {Γ X Y i} d → Γ ⊢ * i ∈ X → insert Y at d of Γ ⊢ lift d (* i) ∈ lift d X
t-lift-v {[]} d (t-var () pX)
t-lift-v {x ∷ Γ} d (t-var {i} (s≤s ple) pX) with d ≤? i
t-lift-v {x ∷ Γ} d (t-var (s≤s ple) pX) | yes p = ⋆⋆TODO⋆⋆
t-lift-v {x ∷ Γ} d (t-var (s≤s ple) pX) | no ¬p = undefined

lift-wt : ∀ {Γ X Y x} d → Γ ⊢ x ∈ X → insert Y at d of Γ ⊢ lift d x ∈ lift d X
lift-wt d t-typ = t-typ
lift-wt d t-bot = t-bot
lift-wt d t-top = t-top
lift-wt d t-unt = t-unt
lift-wt d (t-pi  pA pB) = t-pi  (lift-wt d pA) (lift-wt (suc d) pB)
lift-wt d (t-lam pA pb) = t-lam (lift-wt d pA) (lift-wt (suc d) pb)
lift-wt d (t-sig pA pB) = t-sig (lift-wt d pA) (lift-wt (suc d) pB)
lift-wt d (t-smk {a} {b} {A} {B} pAB pa pb) = t-smk (lift-wt d pAB) (lift-wt d pa) (typ-Γ≡ (lift-subst z≤n a B) (lift-wt d pb))
lift-wt d (t-pi1 pab) = t-pi1 (lift-wt d pab)
lift-wt d (t-pi2 {ab} {A} {B} pab) rewrite lift-subst {d} z≤n (pi1 ab) B = t-pi2 (lift-wt d pab)
lift-wt d (t-app {A} {B} {f} {x} pf px) rewrite lift-subst {d} z≤n x B = t-app (lift-wt d pf) (lift-wt d px)
lift-wt d t-btr = t-btr
lift-wt d t-ell = t-ell
lift-wt d (t-brc pl pr) = t-brc (lift-wt d pl) (lift-wt d pr)
lift-wt {Γ} {Y = Y} d (t-ind {P} {lc} {bc} pP plc pbc) = t-ind (lift-wt (suc d) pP) (typ-Γ≡ (lift-subst z≤n ℓ P) (lift-wt d plc))
                                                               $ flip typ-Γ≡ (lift-wt d pbc)
                                                               $ ap (λ T → τ ⇨ τ ⇨ T)
                                                               $ lift (2 + d) (lift^ 2 at 1 of P ⍟ * 1) ⇨ -- Really missing Lean's elaborator right now
                                                                 lift (3 + d) (lift^ 3 at 1 of P ⍟ * 1) ⇨
                                                                 lift (4 + d) (lift^ 4 at 1 of P ⍟ (* 2 ⊕ * 3))
                                                                   ≡⟨ ⋆⋆TODO⋆⋆ ⟩
                                                                 lift (3 + d) (lift^ 2 at 1 of P) ⍟ lift (2 + d) (* 1) ⇨
                                                                 lift (4 + d) (lift^ 3 at 1 of P) ⍟ lift (3 + d) (* 1) ⇨
                                                                 lift (5 + d) (lift^ 4 at 1 of P) ⍟ lift (4 + d) (* 2 ⊕ * 3)
                                                                   ≡⟨ refl ⟩
                                                                 lift (3 + d) (lift^ 2 at 1 of P) ⍟ * 1 ⇨
                                                                 lift (4 + d) (lift^ 3 at 1 of P) ⍟ * 1 ⇨
                                                                 lift (5 + d) (lift^ 4 at 1 of P) ⍟ (* 2 ⊕ * 3)
                                                                   ≡⟨ ⋆⋆TODO⋆⋆ ⟩
                                                                ((lift^ 2 at 1 of lift (suc d) P) ⍟ * 1 ⇨
                                                                 (lift^ 3 at 1 of lift (suc d) P) ⍟ * 1 ⇨
                                                                 (lift^ 4 at 1 of lift (suc d) P) ⍟ (* 2 ⊕ * 3)) ∎
lift-wt d (t-exf {X} pX) rewrite lift-w-comm d X ⁻¹ = t-exf (lift-wt d pX)
lift-wt d (t-var ple pX) = t-lift-v d (t-var ple pX)

w^_-wt : ∀ Γ' {Γ X e} → Γ ⊢ e ∈ X → Γ' ++ Γ ⊢ w^ (length Γ') e ∈ w^ (length Γ') X
w^ [] -wt p = p
w^ (X ∷ Γ') -wt p = lift-wt 0 (w^ Γ' -wt p)

subst-con : ℕ → Ptm → Con → Con
subst-con d v [] = []
subst-con zero v (x ∷ Γ) = Γ
subst-con (suc d) v (x ∷ Γ) = subst-v d (w^ d v) x ∷ subst-con d v Γ

subst-all : Ptm → Con → Con
subst-all v Γ = subst-con (pred $ length Γ) v Γ

subst-wt : ∀ {Γ X E e x} Γ' → Γ ⊢ x ∈ X → Γ' ++ X ∷ Γ ⊢ e ∈ E → let d = length Γ' in subst-con d x Γ' ++ Γ ⊢ subst-v d (w^ d x) e ∈ subst-v d (w^ d x) E
subst-wt Γ' px t-typ = t-typ
subst-wt Γ' px t-bot = t-bot
subst-wt Γ' px t-top = t-top
subst-wt Γ' px t-unt = t-unt
subst-wt Γ' px (t-pi  pA pB) = t-pi  (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pB)
subst-wt Γ' px (t-lam pA pb) = t-lam (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pb)
subst-wt Γ' px (t-sig pA pB) = t-sig (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pB)
subst-wt Γ' px (t-smk pAB pa pb) = t-smk (subst-wt Γ' px pAB) (subst-wt Γ' px pa) {!subst-wt Γ' px pb!}
subst-wt Γ' px (t-pi1 APB) = {!!}
subst-wt Γ' px (t-pi2 pab) = {!!}
subst-wt Γ' px (t-app pf pa) = {!!}
subst-wt Γ' px t-btr = t-btr
subst-wt Γ' px t-ell = t-ell
subst-wt Γ' px (t-brc pl pr) = {!!}
subst-wt Γ' px (t-ind pP plc pbc) = {!!}
subst-wt Γ' px (t-exf pA) = {!!}
subst-wt Γ' px (t-var ple pA) = {!!}
