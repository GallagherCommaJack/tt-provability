import data.list data.nat
import logic

open eq eq.ops decidable subtype
open function nat list

inductive tree (X : Type) : Type :=
| br : tree X → tree X → tree X
| leaf : X → tree X

inductive ptm : Type :=
| typ  : ptm
| bot  : ptm
| top  : ptm
| unit : ptm
| var  : ℕ → ptm
| pi   : ptm → ptm → ptm
| lam  : ptm → ptm → ptm
| app  : ptm → ptm → ptm
| tree : ptm → ptm
| leaf : ptm → ptm
| br   : ptm → ptm → ptm
| ind  : ptm → ptm → ptm → ptm → ptm

namespace ptm

notation `μ`:500 := typ
infixr `⇒`:10 := pi
infixr `↦`:10 := lam
infixl `⊛`:50 := app
prefix `*`:500 := var
notation `⊥`:500 := bot
notation `⊤`:500 := top
notation `⊕`:50 := br

definition lift (d : ℕ) (t : ptm) : ptm :=
  (ptm.rec_on t
    (λ d, μ)
    (λ d, bot)
    (λ d, top)
    (λ d, unit)
    (λ i d, if d ≤ i then * succ i else * i)
    (λ a b IH_a IH_b d, IH_a d ⇒ IH_b (succ d))
    (λ a b IH_a IH_b d, IH_a d ↦ IH_b (succ d))
    (λ f x IH_f IH_x d, IH_f d ⊛ IH_x d)
    (λ t IH_t d, tree $ IH_t d)
    (λ t IH_t d, leaf (IH_t d))
    (λ l r IH_l IH_r d, br (IH_l d) (IH_r d))
    (λ X P l b IH_X IH_P IH_l IH_b d,
    ind (IH_X d) (IH_P d) (IH_l d) (IH_b d))) d

definition w : ptm → ptm := lift 0

namespace subst
  inductive rel : ℕ → ptm → ptm → ptm → Prop :=
  | typ : ∀ {i v}, rel i v μ μ
  | bot : ∀ {i v}, rel i v ⊥ ⊥
  | top : ∀ {i v}, rel i v ⊤ ⊤
  | unit : ∀ {i v}, rel i v unit unit
  | var_eq : ∀ {i v}, rel i v (var i) v
  | var_lt : ∀ {i j v}, i < j → rel i v (var j) (var (pred j))
  | var_gt : ∀ {i j v}, i > j → rel i v (var j) (var j)
  | pi  : ∀ {i v d d' c c'}, rel i v d d' → rel (succ i) (w v) c c' → rel i v (d ⇒ c) (d' ⇒ c')
  | lam : ∀ {i v t t' b b'}, rel i v t t' → rel (succ i) (w v) b b' → rel i v (t ↦ b) (t' ↦ b')
  | app : ∀ {i v f f' x x'}, rel i v f f' → rel i v x x' → rel i v (f ⊛ x) (f' ⊛ x')
  | tree : ∀ {i v X X'}, rel i v X X' → rel i v (tree X) (tree X')
  | leaf : ∀ {i v l l'}, rel i v l l' → rel i v (leaf l) (leaf l')
  | br   : ∀ {i v l l' r r'}, rel i v l l' → rel i v r r' → rel i v (br l r) (br l' r')
  | ind  : ∀ {i v X X' P P' l l' b b'}, rel i v X X'
                                      → rel i v P P'
                                      → rel i v l l'
                                      → rel i v b b'
                                      → rel i v (ind X P l b) (ind X' P' l' b')

  definition func : Π (i : ℕ) (v : ptm) (e : ptm), { r | rel i v e r }
  | i v μ := tag μ rel.typ
  | i v ⊥ := tag ⊥ rel.bot
  | i v ⊤ := tag ⊤ rel.top
  | i v unit := tag unit rel.unit
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
                let IH_f := func i v f, IH_x := func i v x in
                tag (elt_of IH_f ⊛ elt_of IH_x) (rel.app (has_property IH_f) (has_property IH_x))
  | i v (tree X) := let IH_X := func i v X in tag (tree $ elt_of IH_X) $ rel.tree $ has_property IH_X
  | i v (leaf t) := let IH_t := func i v t in tag (leaf $ elt_of IH_t) $ rel.leaf $ has_property IH_t
  | i v (br l r) := let IH_l := func i v l, IH_r := func i v r in tag (br (elt_of IH_l) (elt_of IH_r)) $ rel.br (has_property IH_l) (has_property IH_r)
  | i v (ind X P l b) := let IH_X := func i v X, IH_P := func i v P in
                         let IH_l := func i v l, IH_b := func i v b in
                         tag (ind (elt_of IH_X) (elt_of IH_P) (elt_of IH_l) (elt_of IH_b)) $ rel.ind (has_property IH_X) (has_property IH_P)
                                                                                                     (has_property IH_l) (has_property IH_b)

  definition val (i : ℕ) (v : ptm) (e : ptm) := elt_of (func i v e)
  definition has_prop (i : ℕ) (v : ptm) (e : ptm) : rel i v e (val i v e) := has_property (func i v e)
end subst
end ptm
