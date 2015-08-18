import data.list data.nat
import logic

open eq eq.ops decidable subtype
open function nat list

inductive ptm : Type :=
| typ : ptm
| var : ℕ → ptm
| pi  : ptm → ptm → ptm
| lam : ptm → ptm → ptm
| app : ptm → ptm → ptm

namespace ptm

notation `μ` := typ
infix `⇒`:50 := pi
infix `↦`:50 := lam
infix `⊛`:50 := app
prefix `*`:500 := var

definition lift (d : ℕ) (t : ptm) : ptm :=
  (ptm.rec_on t
    (λ d, μ)
    (λ i d, if d ≤ i then * succ i else * i)
    (λ a b IH_a IH_b d, IH_a d ⇒ IH_b (succ d))
    (λ a b IH_a IH_b d, IH_a d ↦ IH_b (succ d))
    (λ f x IH_f IH_x d, IH_f d ⊛ IH_x d)) d

definition w : ptm → ptm := lift 0
namespace subst
  inductive rel : ℕ → ptm → ptm → ptm → Prop :=
  | typ : ∀ {i v}, rel i v μ μ
  | var_eq : ∀ {i v}, rel i v (var i) v
  | var_lt : ∀ {i j v}, i < j → rel i v (var j) (var (pred j))
  | var_gt : ∀ {i j v}, i > j → rel i v (var j) (var j)
  | pi  : ∀ {i v d d' c c'}, rel i v d d' → rel (succ i) (w v) c c' → rel i v (d ⇒ c) (d' ⇒ c')
  | lam : ∀ {i v t t' b b'}, rel i v t t' → rel (succ i) (w v) b b' → rel i v (t ↦ b) (t' ↦ b')
  | app : ∀ {i v f f' x x'}, rel i v f f' → rel i v x x' → rel i v (f ⊛ x) (f' ⊛ x')

  definition func : Π (i : ℕ) (v : ptm) (e : ptm), { r | rel i v e r }
  | i v μ := tag μ rel.typ
  | i v (var j) := lt.by_cases
                   (take H : i < j, tag (var $ pred j) (rel.var_lt H))
                   (take H : i = j, tag v (H ▸ rel.var_eq))
                   (take H : i > j, tag (var j) (rel.var_gt H))
  | i v (d ⇒ c) :=
                let IH_d : { d' | rel i v d d' } := func i v d in
                let IH_c : { c' | rel (succ i) (w v) c c' } := func (succ i) (w v) c in
                tag (elt_of IH_d ⇒ elt_of IH_c) (rel.pi (has_property IH_d) (has_property IH_c))
  | i v (t ↦ b) :=
                let IH_t : { t' | rel i v t t' } := func i v t in
                let IH_b : { b' | rel (succ i) (w v) b b' } := func (succ i) (w v) b in
                tag (elt_of IH_t ↦ elt_of IH_b) (rel.lam (has_property IH_t) (has_property IH_b))
  | i v (f ⊛ x) :=
                let IH_f := func i v f in
                let IH_x := func i v x in
                tag (elt_of IH_f ⊛ elt_of IH_x) (rel.app (has_property IH_f) (has_property IH_x))

  definition val (i : ℕ) (v : ptm) (e : ptm) := elt_of (func i v e)
end subst

definition con := list ptm

inductive has_type : con → ptm → ptm → Prop :=
| typ : ∀ {Γ}, has_type Γ μ μ
| var : ∀ {Γ i} (p : i < length Γ), has_type Γ (ith Γ i p) μ -- this seems too permissive
                                  → has_type Γ (var i) (ith Γ i p)
| pi  : ∀ {Γ d c}, has_type Γ d μ → has_type (d :: Γ) c μ → has_type Γ (d ⇒ c) μ
| lam : ∀ {Γ T1 b T2}, has_type Γ (T1 ⇒ T2) μ
                     → has_type (T1 :: Γ) b T2
                     → has_type Γ (T1 ↦ b) (T1 ⇒ T2)

notation Γ `⊢` t `∈` T := has_type Γ t T

end ptm

open ptm

definition tm (Γ : con) := { p : ptm | ∃ T : ptm, has_type Γ p T }
