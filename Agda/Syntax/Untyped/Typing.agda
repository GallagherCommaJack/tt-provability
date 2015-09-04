{-# OPTIONS --without-K --no-termination-check #-}
module Syntax.Untyped.Typing where
open import lib
open import Syntax.Untyped.Def
open import Syntax.Untyped.Subst-Lemmas

data var-rel : ℕ → Con → Ptm → Set where
  vz : ∀ {Γ X} → var-rel 0 (X ∷ Γ) (w X)
  vs : ∀ {i Γ X Y} → var-rel i Γ X → var-rel (suc i) (Y ∷ Γ) (w X)

infix 1 _⊢_∈_
data _⊢_∈_ (Γ : Con) : Ptm → Ptm → Set where
  t-typ : ∀ {n} → Γ ⊢ typ n ∈ typ (suc n)
  t-bot : ∀ {n} → Γ ⊢ bot ∈ typ n
  t-top : ∀ {n} → Γ ⊢ top ∈ typ n
  t-unt : Γ ⊢ unt ∈ top
  t-pi  : ∀ {n m A B} → Γ ⊢ A ∈ typ n → (A ∷ Γ) ⊢ B ∈ typ m → Γ ⊢ pi  A B ∈ typ (n ⊔ m)
  t-lam : ∀ {m X B b} → Γ ⊢ pi X B ∈ typ m → (X ∷ Γ) ⊢ b ∈ B → Γ ⊢ lam X b ∈ pi X B
  t-sig : ∀ {n m A B} → Γ ⊢ A ∈ typ n → (A ∷ Γ) ⊢ B ∈ typ m → Γ ⊢ sig A B ∈ typ (n ⊔ m)
  t-smk : ∀ {a b A B B' m} → Γ ⊢ sig A B ∈ typ m → Γ ⊢ a ∈ A → subst-rel 0 a B B' → Γ ⊢ b ∈ B' → Γ ⊢ smk a b ∈ sig A B
  t-pi1 : ∀ {p A B} → Γ ⊢ p ∈ sig A B → Γ ⊢ pi1 p ∈ A
  t-pi2 : ∀ {p A B B'} → Γ ⊢ p ∈ sig A B → subst-rel 0 (pi1 p) B B' → Γ ⊢ pi2 p ∈ B'
  t-app : ∀ {A B B' f a} → Γ ⊢ f ∈ pi A B → Γ ⊢ a ∈ A → subst-rel 0 a B B' → Γ ⊢ f ⊛ a ∈ B'
  t-btr : ∀ {n} → Γ ⊢ τ ∈ typ n
  t-ell : Γ ⊢ ℓ ∈ τ
  t-brc : ∀ {l r} → Γ ⊢ l ∈ τ → Γ ⊢ r ∈ τ → Γ ⊢ l ⊕ r ∈ τ
  t-ind : ∀ {P l b n} → τ ∷ Γ ⊢ P ∈ typ n →
                      ∀ {Pℓ} → subst-rel 0 ℓ P Pℓ
                      → Γ ⊢ l ∈ Pℓ
                      → Γ ⊢ b ∈ τ   ⇨ τ
                              ⇨ (lift^ 2 at 1 of P) ⍟ * 1
                              ⇨ (lift^ 3 at 1 of P) ⍟ * 1
                              ⇨ (lift^ 4 at 1 of P) ⍟ (* 2 ⊕ * 3)
                      → Γ ⊢ ind P l b ∈ pi τ P
  t-exf : ∀ {X n} → Γ ⊢ X ∈ typ n → Γ ⊢ exf X ∈ pi bot (w X)
  t-var : ∀ {i X} → var-rel i Γ X → Γ ⊢ * i ∈ X

  -- these rules are unnecessary because the typechecker has already internalized the evaluation equations
  -- t-eval-to : ∀ {x X X'} → X ⟹ X' → Γ ⊢ x ∈ X → Γ ⊢ x ∈ X'
  -- t-eval-from : ∀ {x X X'} → X ⟹ X' → Γ ⊢ x ∈ X' → Γ ⊢ x ∈ X
  -- Hooray for ETT!

t-vz : ∀ {Γ X} → (X ∷ Γ) ⊢ * 0 ∈ w X
t-vz = t-var vz
t-vs : ∀ {Γ X Y i} → Γ ⊢ * i ∈ X → (Y ∷ Γ) ⊢ * suc i ∈ w X
t-vs (t-var i) = t-var (vs i)

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
t-lift-v zero (t-var vz) = t-var (vs vz)
t-lift-v (suc d) (t-var (vz {Γ} {X})) rewrite lift-comm {0} {d} z≤n X ⁻¹ = t-vz
t-lift-v zero (t-var (vs x)) = t-var (vs (vs x))
t-lift-v {Y = Y₁} (suc d) (t-var (vs {i} {X = X} {Y₂} x)) with t-lift-v {Y = Y₁} d (t-var x)
t-lift-v (suc d) (t-var (vs {i} x)) | p₁ with d ≤? i
t-lift-v (suc d) (t-var (vs {X = X} x)) | p₁ | yes p₂ rewrite lift-comm {0} {d} z≤n X ⁻¹ = t-vs p₁
t-lift-v (suc d) (t-var (vs {X = X} x)) | p₁ | no ¬p₂ rewrite lift-comm {0} {d} z≤n X ⁻¹ = t-vs p₁

lift-wt : ∀ {Γ X Y x} d → Γ ⊢ x ∈ X → insert Y at d of Γ ⊢ lift d x ∈ lift d X
lift-wt d t-typ = t-typ
lift-wt d t-bot = t-bot
lift-wt d t-top = t-top
lift-wt d t-unt = t-unt
lift-wt d (t-pi  pA pB) = t-pi  (lift-wt d pA) (lift-wt (suc d) pB)
lift-wt d (t-lam pA pb) = t-lam (lift-wt d pA) (lift-wt (suc d) pb)
lift-wt d (t-sig pA pB) = t-sig (lift-wt d pA) (lift-wt (suc d) pB)
lift-wt d (t-smk pAB pa sB pb) = t-smk (lift-wt d pAB) (lift-wt d pa) (lift-subst-rel z≤n _ sB) (lift-wt d pb)
lift-wt d (t-pi1 pab) = t-pi1 (lift-wt d pab)
lift-wt d (t-pi2 {ab} {A} {B} pab pB') rewrite lift-subst {d} z≤n (pi1 ab) B = t-pi2 (lift-wt d pab) ⋆⋆TODO⋆⋆
lift-wt d (t-app {A} {B} {f} {x} pf px pfx) rewrite lift-subst {d} z≤n x B = t-app (lift-wt d pf) (lift-wt d px) ⋆⋆TODO⋆⋆
lift-wt d t-btr = t-btr
lift-wt d t-ell = t-ell
lift-wt d (t-brc pl pr) = t-brc (lift-wt d pl) (lift-wt d pr)
lift-wt {Γ} {Y = Y} d (t-ind {P} {lc} {bc} pP pl' plc pbc) = t-ind (lift-wt (suc d) pP) (lift-subst-rel z≤n ℓ pl') (lift-wt d plc)
                                                               $ flip typ-Γ≡ (lift-wt d pbc)
                                                               $ ap (λ T → τ ⇨ τ ⇨ T)
                                                               $ lift (2 + d) (lift^ 2 at 1 of P ⍟ * 1) ⇨
                                                                 lift (3 + d) (lift^ 3 at 1 of P ⍟ * 1) ⇨
                                                                 lift (4 + d) (lift^ 4 at 1 of P ⍟ (* 2 ⊕ * 3))
                                                                   ≡⟨ ⋆⋆TODO⋆⋆ ⟩ -- Really missing Lean's elaborator right now
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
lift-wt d (t-var p) = t-lift-v d (t-var p)

w^_-wt : ∀ Γ' {Γ X e} → Γ ⊢ e ∈ X → Γ' ++ Γ ⊢ w^ (length Γ') e ∈ w^ (length Γ') X
w^ [] -wt p = p
w^ (X ∷ Γ') -wt p = lift-wt 0 (w^ Γ' -wt p)

subst-con : ℕ → Ptm → Con → Con
subst-con d v [] = []
subst-con zero v (x ∷ Γ) = Γ
subst-con (suc d) v (x ∷ Γ) = subst-v d (w^ d v) x ∷ subst-con d v Γ

subst-all : Ptm → Con → Con
subst-all v Γ = subst-con (pred $ length Γ) v Γ

subst-wt : ∀ {Γ X E e x} Γ' → Γ ⊢ x ∈ X → Γ' ++ X ∷ Γ ⊢ e ∈ E
           → let d = length Γ'
             in subst-con d x Γ' ++ Γ ⊢ subst-v d (w^ d x) e ∈ subst-v d (w^ d x) E
subst-wt Γ' px t-typ = t-typ
subst-wt Γ' px t-bot = t-bot
subst-wt Γ' px t-top = t-top
subst-wt Γ' px t-unt = t-unt
subst-wt Γ' px (t-pi  pA pB) = t-pi  (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pB)
subst-wt Γ' px (t-lam pA pb) = t-lam (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pb)
subst-wt Γ' px (t-sig pA pB) = t-sig (subst-wt Γ' px pA) (subst-wt (_ ∷ Γ') px pB)
subst-wt Γ' px (t-smk pAB pa pB' pb) = t-smk (subst-wt Γ' px pAB) (subst-wt Γ' px pa) ⋆⋆TODO⋆⋆ (subst-wt Γ' px pb)
subst-wt Γ' px (t-pi1 pab) = t-pi1 (subst-wt Γ' px pab)
subst-wt Γ' px (t-pi2 pab paB) = ⋆⋆TODO⋆⋆
subst-wt Γ' px (t-app pf pa pfx) = ⋆⋆TODO⋆⋆
subst-wt Γ' px t-btr = t-btr
subst-wt Γ' px t-ell = t-ell
subst-wt Γ' px (t-brc pl pr) = t-brc (subst-wt Γ' px pl) (subst-wt Γ' px pr)
subst-wt Γ' px (t-ind pP pl' plc pbc) = t-ind (subst-wt (_ ∷ Γ') px pP) ⋆⋆TODO⋆⋆ (subst-wt Γ' px plc) ⋆⋆TODO⋆⋆
subst-wt Γ' px (t-exf pA) = ⋆⋆TODO⋆⋆
subst-wt Γ' px (t-var p) = ⋆⋆TODO⋆⋆

nil-no-vars : ∀ {n T} → ¬ ([] ⊢ * n ∈ T)
nil-no-vars (t-var ())

var-lookup-w : ∀ {Γ n T} → Γ ⊢ * n ∈ T → Σ[ T' ∈ Ptm ] (T ≡ w^ (suc n) T')
var-lookup-w (t-var (vz {Γ} {X})) = X , refl
var-lookup-w (t-var (vs x)) with var-lookup-w (t-var x)
var-lookup-w (t-var (vs x)) | X , p = X , cong w p

t-pred : ∀ {Γ n X Y} → Y ∷ Γ ⊢ * (suc n) ∈ X → Γ ⊢ * n ∈ unw X
t-pred (t-var (vs {X = X} p)) rewrite unlift-lift 0 X = t-var p
