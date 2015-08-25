import data.list data.nat
import logic
import ptm
open decidable subtype
open function nat list
open ptm
open eq eq.ops

definition con := list ptm

inductive reval : ptm → ptm → Prop :=
infix `⟹`:5 := reval
| typ : μ ⟹ μ
| btr : τ ⟹ τ
| bot : ⊥ ⟹ ⊥
| top : ⊤ ⟹ ⊤
| pi  : ∀ {d c d' c'}, (d ⟹ d') → (c ⟹ c') → (d ⇒ c ⟹ d' ⇒ c')
| sig : ∀ {X X' P P'}, (X ⟹ X') → (P ⟹ P') → (X ⊗ P ⟹ X' ⊗ P')
| app : ∀ {f f' x fx'}, (f ⟹ f') → (f' ⊛ x ⟹ fx') → (f ⊛ x ⟹ fx')
| app_lam : ∀ {f X x fx'}, (subst.val 0 x f ⟹ fx') → (X ↦ f ⊛ x ⟹ fx') -- lazy because it's easier
| app_ind_br : ∀ {P lc bc l r l' r' bc'}, (ind P lc bc ⊛ l ⟹ l')
                                        → (ind P lc bc ⊛ r ⟹ r')
                                        → (bc ⊛ l ⊛ r ⊛ l' ⊛ r' ⟹ bc')
                                        → (ind P lc bc ⊛ br l r ⟹ bc')
| app_unit_rec : ∀ {P u u'}, (u ⟹ u') → (top_rec P u ⊛ unit ⟹ u')
| var  : ∀ {i}, var i ⟹ var i
| unit : unit ⟹ unit
| lam  : ∀ {X X' b b'}, (X ⟹ X') → (b ⟹ b') → (X ↦ b ⟹ X' ↦ b')
| mkp  : ∀ {x x' p p'}, (x ⟹ x') → (p ⟹ p') → (mkp x p ⟹ mkp x' p')
| leaf : ℓ ⟹ ℓ
| br   : ∀ {l l' r r'}, (l ⟹ l') → (r ⟹ r') → (l ⊕ r ⟹ l' ⊕ r')
| bot_rec : ∀ {P}, bot_rec P ⟹ bot_rec P
| unit_rec : ∀ {P u}, top_rec P u ⟹ top_rec P u

infix `⟹`:5 := reval

definition lift_n (n : ℕ) (d : ℕ) : ptm → ptm :=
  nat.rec_on n (lift d) (λ n' f, lift d ∘ f)

notation `lift^` n `at` d := lift_n n d

inductive has_type : con → ptm → ptm → Prop :=
notation Γ `⟫`:1 t `∈`:1 T := has_type Γ t T
| typ : ∀ {Γ}, Γ ⟫ μ ∈ μ -- type : type
| btr : ∀ {Γ}, Γ ⟫ τ ∈ μ
| bot : ∀ {Γ}, Γ ⟫ ⊥ ∈ μ
| top : ∀ {Γ}, Γ ⟫ ⊤ ∈ μ
| pi  : ∀ {Γ d c}, (Γ ⟫ d ∈ μ)
                 → (d :: Γ ⟫ c ∈ μ)
                 → (Γ ⟫ (d ⇒ c) ∈ μ)
| sig : ∀ {Γ X P}, (Γ ⟫ X ∈ μ)
                 → (Γ ⟫ P ∈ X ⇒ μ)
                 → (Γ ⟫ X ⊗ P ∈ μ)
| app : ∀ {Γ d c f x}, (Γ ⟫ f ∈ d ⇒ c)
                     → (Γ ⟫ x ∈ d)
                     → (Γ ⟫ f ⊛ x ∈ subst.val 0 x c)
| var : ∀ {Γ i} (p : i < length Γ), (Γ ⟫ ith Γ i p ∈ μ)
                                  → (Γ ⟫ var i ∈ ith Γ i p)
| lam : ∀ {Γ T1 b T2}, (Γ ⟫ T1 ⇒ T2 ∈ μ)
                     → (T1 :: Γ ⟫ b ∈ T2)
                     → (Γ ⟫ T1 ↦ b ∈ T1 ⇒ T2)
| unit : ∀ {Γ}, Γ ⟫ unit ∈ ⊤
| leaf : ∀ {Γ}, Γ ⟫ ℓ ∈ τ
| br   : ∀ {Γ l r}, (Γ ⟫ l ∈ τ) → (Γ ⟫ r ∈ τ) → (Γ ⟫ l ⊕ r ∈ τ)
| bot_rec : ∀  {Γ P}, (Γ ⟫ P ∈ μ) → (Γ ⟫ bot_rec P ∈ ⊥ ⇒ w P)
| ind  : ∀ {Γ P l b}, (Γ ⟫ P ∈ τ ⇒ μ)
                    → (Γ ⟫ l ∈ P ⊛ ℓ)
                    → (Γ ⟫ b ∈ τ ⇒ τ ⇒ (lift^ 2 at 1) P ⊛ var 1 ⇒ (lift^ 3 at 1) P ⊛ var 1 ⇒ (lift^ 4 at 1) P ⊛ (var 3 ⊕ var 2))
                    → (Γ ⟫ ind P l b ∈ τ ⇒ lift 1 P ⊛ var 0)
| eval_to : ∀ {Γ t T T'}, (T ⟹ T') → (Γ ⟫ t ∈ T) → (Γ ⟫ t ∈ T')
| eval_from : ∀ {Γ t T T'}, (T ⟹ T') → (Γ ⟫ t ∈ T') → (Γ ⟫ t ∈ T)

notation Γ `⟫`:1 t `∈`:1 T := has_type Γ t T

definition lift_con : ℕ → ptm → list ptm → list ptm
| 0 x xs := x :: xs
| (succ n) x (y :: ys) := lift n y :: lift_con n x ys
| (succ n) x [] := [x]

theorem w_lift_comm : ∀ d t, w (lift d t) = lift (succ d) (w t) := sorry

theorem lift_wt : ∀ {Γ x X T}, (Γ ⟫ x ∈ X) → ∀ d, (lift_con d T Γ ⟫ lift d x ∈ lift d X)
| Γ μ μ T has_type.typ d := has_type.typ
| Γ τ μ T has_type.btr d := has_type.btr
| Γ ⊥ μ T has_type.bot d := has_type.bot
| Γ ⊤ μ T has_type.top d := has_type.top
| Γ (D ⇒ C) μ T (has_type.pi pD pC) d := have IH_1 : lift_con d T Γ ⟫ lift d D ∈ μ, from lift_wt pD _,
                                          have IH_2 : lift_con (succ d) T (D :: Γ) ⟫ lift (succ d) C ∈ lift (succ d) μ, from lift_wt pC _,
                                          show lift_con d T Γ ⟫ lift d (D ⇒ C) ∈ μ, from has_type.pi IH_1 IH_2
| Γ (X ⊗ P) μ T (has_type.sig pX pP) d := have IH_1 : lift_con d T Γ ⟫ lift d X ∈ μ, from lift_wt pX d,
                                           have IH_2 : lift_con d T Γ ⟫ lift d P ∈ lift d X ⇒ μ, from lift_wt pP d,
                                           show lift_con d T Γ ⟫ lift d (X ⊗ P) ∈ μ, from has_type.sig IH_1 IH_2
| Γ (var i) ⌞ith Γ i p⌟ T (has_type.var p ti) d := sorry
| Γ (T1 ↦ b) (T1 ⇒ T2) T (has_type.lam pArr pb) d :=
                                                     have IH_Arr : lift_con d T Γ ⟫ lift d (T1 ⇒ T2) ∈ lift d μ, from lift_wt pArr d,
                                                     have IH_b : lift_con (succ d) T (T1 :: Γ) ⟫ lift (succ d) b ∈ lift (succ d) T2, from lift_wt pb (succ d),
                                                     show lift_con d T Γ ⟫ lift d (T1 ↦ b) ∈ lift d (T1 ⇒ T2), from has_type.lam IH_Arr IH_b
| Γ unit ⊤ T has_type.unit d := has_type.unit
| Γ ℓ τ T has_type.leaf d := has_type.leaf
| Γ (l ⊕ r) τ T (has_type.br pl pr) d := have IH_l : lift_con d T Γ ⟫ lift d l ∈ τ, from lift_wt pl d,
                                          have IH_r : lift_con d T Γ ⟫ lift d r ∈ τ, from lift_wt pr d,
                                          show lift_con d T Γ ⟫ lift d (l ⊕ r) ∈ τ, from has_type.br IH_l IH_r
| Γ (bot_rec P) ⌞⊥ ⇒ w P⌟ T (has_type.bot_rec p) d := have IH : lift_con d T Γ ⟫ lift d P ∈ μ, from lift_wt p d,
                                                        show lift_con d T Γ ⟫ bot_rec (lift d P) ∈ ⊥ ⇒ lift (succ d) (w P),
                                                        from w_lift_comm d P ▸ has_type.bot_rec IH
| Γ (ind P l b) ⌞τ ⇒ lift 1 P ⊛ var 0⌟ T (has_type.ind pP pl pb) d := sorry
| Γ x X T (has_type.eval_to pX' pX) d := sorry
| Γ x X T (has_type.eval_from pX pX') d := sorry

inductive is_good_con : con → Prop :=
| nil : is_good_con []
| cons : ∀ {Γ T}, (Γ ⟫ T ∈ μ) → is_good_con (T :: Γ)

definition is_well_typed (Γ : con) (t : ptm) (T : ptm) : Prop :=
  (is_good_con Γ) ∧ (Γ ⟫ T ∈ μ) ∧ (Γ ⟫ t ∈ T)

notation Γ `⊢`:1 t `∈`:1 T := is_well_typed Γ t T

definition ty (Γ : con) := {t | (Γ ⊢ t ∈ μ)}
definition tm (Γ : con) (T : ty Γ) := {t | (Γ ⟫ t ∈ elt_of T)}
