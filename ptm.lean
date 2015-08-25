import data.list data.nat
import logic

open eq eq.ops decidable subtype
open function nat list

inductive tree (X : Type) : Type :=
| br : tree X → tree X → tree X
| leaf : tree X

inductive ptm : Type :=
| typ  : ptm
| btr  : ptm
| bot  : ptm
| top  : ptm
| pi   : ptm → ptm → ptm
| sig  : ptm → ptm → ptm
| app  : ptm → ptm → ptm
| var  : ℕ → ptm
| unit : ptm
| lam  : ptm → ptm → ptm
| mkp  : ptm → ptm → ptm
| leaf : ptm
| br   : ptm → ptm → ptm
| bot_rec : ptm → ptm
| top_rec : ptm → ptm → ptm
| sig_rec : ptm → ptm → ptm
| ind : ptm → ptm → ptm → ptm

namespace ptm

notation `μ`:500 := typ
notation `⊥`:500 := bot
notation `⊤`:500 := top
notation `τ`:500 := btr
infixr `⇒`:10 := pi
infixr `⊗`:10 := sig
infixl `⊛`:50 := app
prefix `*`:500 := var
infixr `↦`:10 := lam
notation `ℓ`:500 := leaf
infix `⊕`:50 := br

infixl `|>`:1 := λ x f, f x

definition lift (d : ℕ) (t : ptm) : ptm :=
  d |> ptm.rec_on t
         (λ d, μ)
         (λ d, τ)
         (λ d, ⊥)
         (λ d, ⊤)
         (λ a b IH_a IH_b d, IH_a d ⇒ IH_b (succ d))
         (λ a b IH_a IH_b d, IH_a d ⊗ IH_b d)
         (λ f x IH_f IH_x d, IH_f d ⊛ IH_x d)
         (λ i d, if d ≤ i then * succ i else * i)
         (λ d, unit)
         (λ a b IH_a IH_b d, IH_a d ↦ IH_b (succ d))
         (λ a b IH_a IH_b d, mkp (IH_a d) (IH_b d))
         (λ d, ℓ)
         (λ l r IH_l IH_r d, IH_l d ⊕ IH_r d)
         (λ P P' d,      bot_rec (P' d))
         (λ P u P' u' d, top_rec (P' d) (u' d))
         (λ P p P' p' d, sig_rec (P' d) (p' d))
         (λ P l b IH_P IH_l IH_b d,
           ind (IH_P d) (IH_l d) (IH_b d))

definition w : ptm → ptm := lift 0

namespace subst
  inductive rel : ℕ → ptm → ptm → ptm → Prop :=
  | typ : ∀ {i v}, rel i v μ μ
  | btr : ∀ {i v}, rel i v τ τ
  | bot : ∀ {i v}, rel i v ⊥ ⊥
  | top : ∀ {i v}, rel i v ⊤ ⊤
  | pi  : ∀ {i v d d' c c'}, rel i v d d' → rel (succ i) (w v) c c' → rel i v (d ⇒ c) (d' ⇒ c')
  | sig : ∀ {i v X X' P P'}, rel i v X X' → rel i v P P' → rel i v (X ⊗ P) (X' ⊗ P')
  | app : ∀ {i v f f' x x'}, rel i v f f' → rel i v x x' → rel i v (f ⊛ x) (f' ⊛ x')
  | var_eq  : ∀ {i v}, rel i v (var i) v
  | var_lt  : ∀ {i j v}, i < j → rel i v (var j) (var (pred j))
  | var_gt  : ∀ {i j v}, i > j → rel i v (var j) (var j)
  | unit    : ∀ {i v}, rel i v unit unit
  | lam     : ∀ {i v t t' b b'}, rel i v t t' → rel (succ i) (w v) b b' → rel i v (t ↦ b) (t' ↦ b')
  | mkp     : ∀ {i v p1 p1' p2 p2'}, rel i v p1 p1' → rel i v p2 p2' → rel i v (mkp p1 p2) (mkp p1' p2')
  | leaf    : ∀ {i v}, rel i v ℓ ℓ
  | br      : ∀ {i v l l' r r'}, rel i v l l' → rel i v r r' → rel i v (l ⊕ r) (l' ⊕ r')
  | bot_rec : ∀ {i v P P'}, rel i v P P' → rel i v (bot_rec P) (bot_rec P')
  | top_rec : ∀ {i v P P' u u'}, rel i v P P' → rel i v u u' → rel i v (top_rec P u) (top_rec P' u')
  | sig_rec : ∀ {i v P P' p p'}, rel i v P P' → rel i v p p' → rel i v (sig_rec P p) (sig_rec P' p')
  | ind  : ∀ {i v P P' l l' b b'}, rel i v P P'
                                 → rel i v l l'
                                 → rel i v b b'
                                 → rel i v (ind P l b) (ind P' l' b')

  definition func : Π (i : ℕ) (v : ptm) (e : ptm), { r | rel i v e r }
  | i v μ := tag μ rel.typ
  | i v τ := tag τ rel.btr
  | i v ⊥ := tag ⊥ rel.bot
  | i v ⊤ := tag ⊤ rel.top
  | i v (d ⇒ c) :=
    let IH_d := func i v d, IH_c := func (succ i) (w v) c
    in  tag (elt_of IH_d ⇒ elt_of IH_c)
    $   rel.pi (has_property IH_d) (has_property IH_c)
  | i v (X ⊗ P) :=
    let IH_X := func i v X, IH_P := func i v P
    in  tag (elt_of IH_X ⊗ elt_of IH_P)
    $   rel.sig (has_property IH_X) (has_property IH_P)
  | i v (f ⊛ x) :=
    let IH_f := func i v f, IH_x := func i v x
    in  tag (elt_of IH_f ⊛ elt_of IH_x)
    $   rel.app (has_property IH_f) (has_property IH_x)
  | i v (var j) := lt.by_cases
    (take H : i < j, tag (* pred j) (rel.var_lt H))
    (take H : i = j, tag v (H ▸ rel.var_eq))
    (take H : i > j, tag (* j) (rel.var_gt H))
  | i v unit := tag unit rel.unit
  | i v (t ↦ b) :=
    let IH_t := func i v t, IH_b := func (succ i) (w v) b
    in  tag (elt_of IH_t ↦ elt_of IH_b)
    $   rel.lam (has_property IH_t) (has_property IH_b)
  | i v (mkp p1 p2) :=
    let IH_1 := func i v p1, IH_2 := func i v p2
    in  tag (mkp (elt_of IH_1) (elt_of IH_2))
    $   rel.mkp (has_property IH_1) (has_property IH_2)
  | i v ℓ := tag ℓ rel.leaf
  | i v (l ⊕ r) :=
    let IH_l := func i v l, IH_r := func i v r
    in  tag (br (elt_of IH_l) (elt_of IH_r))
    $   rel.br (has_property IH_l) (has_property IH_r)
  | i v (bot_rec P) :=
    let IH := func i v P
    in  tag (bot_rec $ elt_of IH)
    $   rel.bot_rec $ has_property IH
  | i v (top_rec P u) :=
    let IH_P := func i v P, IH_u := func i v u
    in  tag (top_rec (elt_of IH_P) (elt_of IH_u))
    $   rel.top_rec (has_property IH_P) (has_property IH_u)
  | i v (sig_rec P p) :=
    let IH_P := func i v P, IH_p := func i v p
    in  tag (sig_rec (elt_of IH_P) (elt_of IH_p))
    $   rel.sig_rec (has_property IH_P) (has_property IH_p)
  | i v (ind P l b) :=
    let IH_P := func i v P, IH_l := func i v l, IH_b := func i v b
    in  tag (ind (elt_of IH_P) (elt_of IH_l) (elt_of IH_b))
    $   rel.ind (has_property IH_P) (has_property IH_l) (has_property IH_b)


  definition val (i : ℕ) (v : ptm) (e : ptm) := elt_of (func i v e)
  definition has_prop (i : ℕ) (v : ptm) (e : ptm) : rel i v e (val i v e) := has_property (func i v e)
end subst
end ptm
