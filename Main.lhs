> module Main where

> import Control.Applicative hiding (Const)

An implementation of Martin-Löf's Logical Framework. The MLLF consists of a
single universe and a primitive dependent function type; then binding and
substitution for theories defined in sigantures is given in terms of primitive
abstraction and application.

> data Type sig
>   = Set
>   | El (ITm sig)
>   | Fun (Type sig) (Type sig)
>     deriving Show

> data ITm sig
>   = Ann (CTm sig) (Type sig)
>   | Var Int
>   | ITm sig :@ CTm sig
>   | Const sig
>     deriving Show

> infixl 9 :@

> data CTm sig
>   = Inf (ITm sig)
>   | Abs (CTm sig)
>     deriving Show

> data Val sig
>   = VAbs (Val sig -> Val sig)
>   | VNeut (Neutral sig)

> data Neutral sig
>   = VConst sig
>   | VApp (Neutral sig) (Val sig)

A signature consists of a family of constants which may be given types;
additionally, the MLLF permits the definition of non-canonical constants by
assert judgemental equations. [I have not yet figured out the correct way to
incorporate judgemental equations into signatures.]

> class Signature sig where
>   sigType :: sig -> Type sig

Then, as an example, we can define a fragment of the Monomorphic Theory of Sets
as a theory in the logical framework.

> data MTS
>   = Unit
>   | Void | Magic
>   | Plus | Inl | Inr | Decide
>     deriving Show

> instance Signature MTS where
>   sigType Unit = Set
>   sigType Void = Set

We represent reductio ad absurdum in the logical framework as a constant:
< Magic : (A : Set) (M : El Void) A

>   sigType Magic
>     = Fun Set
>     $ Fun (El (Const Void))
>     $ El (Var 1)

We implement the disjoint union as the following constants:
< Plus : (A : Set) (B : Set) Set
< Inl : (A : Set) (B : Set) (M : El A) El (Plus A B)
< Inr : (A : Set) (B : Set) (M : El B) El (Plus A B)
< Decide : (A : Set) (B : Set) (C : (x : El (Plus A B)) Set) (L : (x : El A) El(C[Inl x])) (R : (x : El B) El(C[Inr x])) (M : El (Plus A B)) El C[M]

>   sigType Plus
>     = Fun Set
>     $ Fun Set Set
>   sigType Inl
>     = Fun Set
>     $ Fun Set
>     $ Fun (El (Var 1))
>     $ El $ Const Plus :@ Inf (Var 2) :@ Inf (Var 1)
>   sigType Inr
>     = Fun Set
>     $ Fun Set
>     $ Fun (El (Var 0))
>     $ El $ Const Plus :@ Inf (Var 2) :@ Inf (Var 1)
>   sigType Decide
>     = Fun Set
>     $ Fun Set
>     $ Fun (Fun (El $ Const Plus :@ Inf (Var 1) :@ Inf (Var 2)) Set)
>     $ Fun (Fun (El $ Var 2) (El $ Var 1 :@ Inf (Const Inl :@ Inf (Var 0))))
>     $ Fun (Fun (El $ Var 2) (El $ Var 2 :@ Inf (Const Inr :@ Inf (Var 0))))
>     $ Fun (El $ Const Plus :@ Inf (Var 5) :@ Inf (Var 4))
>     $ El (Var 3 :@ Inf (Var 0))


Now, a bidirectional type checking algorithm is given which is polymorphic over
signatures:

> data TErr = Welp
> type TC a = Either TErr a
> type Context sig = [Type sig]

> check
>   :: Signature sig
>   => Int
>   -> Context sig
>   -> CTm sig
>   -> Type sig
>   -> TC ()
> check i γ (Inf e) τ = _
> check i γ (Abs e) τ = _

> infer
>   :: Signature sig
>   => Int
>   -> Context sig
>   -> ITm sig
>   -> TC (Type sig)
> infer i γ (Ann e τ) =
>   τ <$ check i γ e τ
> infer i γ (Const c) =
>   pure $ sigType c
> infer i γ e = _


