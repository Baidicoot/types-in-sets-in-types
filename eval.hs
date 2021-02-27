data Term
    = Var Int
    | Lam Term
    | App Term Term

lift :: Int -> Term -> Term
lift i (Var v) | v < i = Var v
lift i (Var v) | v >= i = Var (v+1)
lift i (Lam b) =
    let b' = lift (i+1) b in Lam b'
lift i (App f a) =
    let f' = lift (i+1) f
        a' = lift (i+1) a
    in App f' a'

subst :: Int -> Term -> Term -> Term
subst i st (Var v) | i == v = st
subst i st (Var v) | i /= v = Var v
subst i st (App f a) =
    let f' = subst i st f
        a' = subst i st a
    in App f' a'
subst i st (Lam b) =
    let b' = subst (i+1) st b
    in Lam b'

lower :: Int -> Term -> Term
lower i (Var v) | v < i = Var v
lower i (Var v) | v >= i = Var (v-1)
lower i (App f a) =
    let f' = lower i f
        a' = lower i a
    in App f' a'
lower i (Lam b) =
    let b' = lower (i+1) b
    in Lam b'

eval :: Term -> Term
eval (Lam b) = Lam b
eval (App f a) =
    let (Lam b) = eval f
        sb = subst 0 a b
        ex = eval sb
    in ex

{-
Definition liftΓ X :=
    (for x, y ∈ ω, given y ∈ x, ⟨⟨x,var y⟩,var y⟩+>∅)
    ∪ (for x, y ∈ ω, given x ⊆ y, ⟨⟨x,var y⟩,var (Suc y)⟩+>∅)
    ∪ (for f, a, f', a' ∈ terms, for x ∈ ω,
        given ⟨⟨x,f⟩,f'⟩ ∈ X,
        given ⟨⟨x,a⟩,a'⟩ ∈ X,
        ⟨⟨x,app f a⟩,app f' a'⟩+>∅)
    ∪ (for b, b' ∈ terms, for x ∈ ω,
        given ⟨⟨Suc x,b⟩,b'⟩ ∈ X,
        ⟨⟨x,lam b⟩,lam b'⟩+>∅).

Definition lift := lfp liftΓ.

Definition lowerΓ X :=
    (for i, v ∈ ω, given i ∈ v, ⟨⟨i,var v⟩,var v⟩+>∅)
    ∪ (for i, v ∈ ω, given (Suc v) ⊆ i, ⟨⟨i,var (Suc v)⟩,var v⟩+>∅)
    ∪ (for f, a, f', a' ∈ terms, for i ∈ ω,
        given ⟨⟨i,f⟩,f'⟩ ∈ X,
        given ⟨⟨i,a⟩,a'⟩ ∈ X,
        ⟨⟨i,app f a⟩,app f' a'⟩+>∅)
    ∪ (for b, b' ∈ terms, for i ∈ ω,
        given ⟨⟨Suc i,b⟩,b'⟩ ∈ X,
        ⟨⟨i,lam b⟩,lam b'⟩+>∅).

Definition lower := lfp lowerΓ.

Definition substΓ X :=
    (for v ∈ ω, for st ∈ terms, ⟨⟨⟨v,st⟩,var v⟩,st⟩+>∅)
    ∪ (for i, v ∈ ω, for st ∈ terms, given i <> v,
        ⟨⟨⟨i,st⟩,var v⟩,var v⟩+>∅)
    ∪ (for i ∈ ω, for st, f, f', a, a' ∈ terms,
        given ⟨⟨⟨i,st⟩,f⟩,f'⟩ ∈ X,
        given ⟨⟨⟨i,st⟩,a⟩,a'⟩ ∈ X,
        ⟨⟨⟨i,st⟩,app f a⟩,app f' a'⟩+>∅)
    ∪ (for i ∈ ω, for st, st', b, b' ∈ terms,
        given ⟨⟨∅,st⟩,st'⟩ ∈ lift,
        given ⟨⟨⟨Suc i,st'⟩,b⟩,b'⟩ ∈ X,
        ⟨⟨⟨i,st⟩,lam b⟩,lam b'⟩+>∅).

Definition subst := lfp substΓ.

(* CBN WHNF evaluation *)
Definition evalΓ X :=
    (for b ∈ terms, ⟨lam b,lam b⟩)
    ∪ (for f, a, b, sb, lb, vb ∈ terms,
        given ⟨f,lam b⟩ ∈ X,
        given ⟨⟨⟨∅,a⟩,b⟩,sb⟩ ∈ subst,
        given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
        given ⟨lb,vb⟩ ∈ X,
        ⟨app f a,vb⟩+>∅).

Definition eval := lfp evalΓ.
-}