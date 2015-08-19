import data.list data.nat
import logic
import ptm

open decidable subtype
open function nat list
open ptm

definition con := list ptm

inductive reval : ptm → ptm → Prop :=
infix `⟹`:5 := reval
| typ : μ ⟹ μ
| var : ∀ {i}, var i ⟹ var i
| bot : ⊥ ⟹ ⊥
| top : ⊤ ⟹ ⊤
| unit : unit ⟹ unit
| pi  : ∀ {d c d' c'}, (d ⟹ d') → (c ⟹ c') → (d ⇒ c ⟹ d' ⇒ c')
| lam : ∀ {X X' b b'}, (X ⟹ X') → (b ⟹ b') → (X ↦ b ⟹ X' ↦ b')
| app_lam : ∀ {f f' X x fx'}, (f ⟹ X ↦ f') → (subst.val 0 f' x ⟹ fx') → (f ⊛ x ⟹ fx') -- lazy because it's easier
| app_ind_leaf : ∀ {X P lc bc t lt'}, (lc ⊛ leaf t ⟹ lt') → (ind X P lc bc ⊛ leaf t ⟹ lt')
| app_ind_br : ∀ {X P lc bc l r l' r' bc'}, (ind X P lc bc ⊛ l ⟹ l')
                                          → (ind X P lc bc ⊛ r ⟹ r')
                                          → (bc ⊛ l ⊛ r ⊛ l' ⊛ r' ⟹ bc')
                                          → (ind X P lc bc ⊛ br l r ⟹ bc')

| tree : ∀ {X X'}, (X ⟹ X') → (tree X ⟹ tree X')
| leaf : ∀ {t t'}, (t ⟹ t') → (leaf t ⟹ leaf t')
| br : ∀ {l l' r r'}, (l ⟹ l') → (r ⟹ r') → (br l r ⟹ br l' r')

infix `⟹`:5 := reval

inductive has_type : con → ptm → ptm → Prop :=
notation Γ `⊢`:1 t `∈`:1 T := has_type Γ t T
| typ : ∀ {Γ}, Γ ⊢ μ ∈ μ -- type : type
| var : ∀ {Γ i} (p : i < length Γ), (Γ ⊢ ith Γ i p ∈ μ)
                                  → (Γ ⊢ var i ∈ ith Γ i p)
| pi  : ∀ {Γ d c}, (Γ ⊢ d ∈ μ)
                 → (d :: Γ ⊢ c ∈ μ)
                 → (Γ ⊢ (d ⇒ c) ∈ μ)
| lam : ∀ {Γ T1 b T2}, (Γ ⊢ T1 ⇒ T2 ∈ μ)
                     → (T1 :: Γ ⊢ b ∈ T2)
                     → (Γ ⊢ T1 ↦ b ∈ T1 ⇒ T2)
| app : ∀ {Γ d c f x}, (Γ ⊢ f ∈ d ⇒ c)
                     → (Γ ⊢ x ∈ d)
                     → (Γ ⊢ f ⊛ x ∈ subst.val 0 x c)
| bot : ∀ {Γ}, Γ ⊢ ⊥ ∈ μ
| top : ∀ {Γ}, Γ ⊢ ⊤ ∈ μ
| unit : ∀ {Γ}, Γ ⊢ unit ∈ ⊤
| tree : ∀ {Γ X}, (Γ ⊢ X ∈ μ) → (Γ ⊢ tree X ∈ μ)
| leaf : ∀ {Γ l X}, (Γ ⊢ l ∈ X) → (Γ ⊢ leaf l ∈ tree X)
| br   : ∀ {Γ l r X}, (Γ ⊢ l ∈ tree X) → (Γ ⊢ r ∈ tree X) → (Γ ⊢ br l r ∈ tree X)
| ind  : ∀ {Γ X P l b}, (Γ ⊢ P ∈ tree X ⇒ μ)
                      → (Γ ⊢ l ∈ X ⇒ P ⊛ leaf (var 0))
                      → (Γ ⊢ b ∈ tree X ⇒ tree X ⇒ P ⊛ var 1 ⇒ P ⊛ var 1 ⇒ P ⊛ br (var 2) (var 3))
                      → (Γ ⊢ ind X P l b ∈ tree X ⇒ P ⊛ var 0)
| eval_to : ∀ {Γ t T T'}, (T ⟹ T') → (Γ ⊢ t ∈ T) → (Γ ⊢ t ∈ T')
| eval_from : ∀ {Γ t T T'}, (T ⟹ T') → (Γ ⊢ t ∈ T') → (Γ ⊢ t ∈ T)

notation Γ `⊢`:1 t `∈`:1 T := has_type Γ t T

definition tm (Γ : con) := { t | ∃ T, (Γ ⊢ t ∈ T) }
