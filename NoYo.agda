-- This file is from Conor McBride, and demonstrates that the Freer monad is
   not isomorphic to the Free Monad in Agda's type theory.

module NoYo where

open import Agda.Primitive

-- three small types
data Zero : Set where
record One : Set where constructor <>
data Two : Set where tt ff : Two

-- equality
data _==_ {l}{X : Set l}(x : X) : X -> Set where
  refl : x == x

-- substitutivity of equality
-- a property of a thing is a property of its equals
subst : forall {k l}{X : Set k}{x y : X}(q : x == y)
        (P : X -> Set l) -> P x -> P y
subst refl P p = p

-- Zero is not One, because one has the property of being inhabited
diffZeroOne : Zero == One -> Zero
diffZeroOne q = subst q (\ X -> X -> Zero) (\ z -> z) <>

-- tt is not ff, because we can easily compute them apart
diffTF : tt == ff -> Zero
diffTF q = subst q (\ { tt -> One ; ff -> Zero }) <>

-- One is not Two, because one has the property of being uniquely inhabited
diffOneTwo : One == Two -> Zero
diffOneTwo q = diffTF
  (subst q (\ X -> (x y : X) -> x == y) (\ _ _ -> refl) tt ff)

-- Here's the "Freer" type. It's a relative monad, not a monad, because
-- of the size increase. (In Coq with impredicative Set switched on, this
-- size issue goes away.)

data Freer (F : Set -> Set)(X : Set) : Set1 where
  ret : X -> Freer F X
  com : (Y : Set)(fy : F Y)(k : Y -> Freer F X) -> Freer F X

-- In Haskell, existentials are weak. You can't unpack Y from a com
-- and look at it. And you can't extract the fy from a com, as its
-- type would escape its scope.
-- In Type Theory, existentials are strong. There is no problem
-- about looking inside com.

Type : forall {F X} -> Freer F X -> Set
Type (ret x)       = One
Type (com Y fy k)  = Y

shape : forall {F X} -> F One -> (a : Freer F X) -> F (Type a)
shape dummy (ret x) = dummy
shape dummy (com Y fy k) = fy

-- Here's a concrete example.

Delay : Set -> Set1
Delay = Freer \ X -> X

-- The usual free presentation is

data DELAY (X : Set) : Set where
  now  : X -> DELAY X
  wait : DELAY X -> DELAY X

-- Predicativity makes the Yoneda encoding is a little tricky in Agda.
-- This direction is fine.

froYo : forall {X} -> Delay X -> DELAY X
froYo (ret x) = now x
froYo (com Y fy k) = wait (froYo (k fy))

-- For the other direction, Delay X is TOO BIG to be the witness to the
-- existential. I've given an equivalent encoding of the same data.
-- In Coq with impredicative Set, the size problem would go away, but
-- you'd still be picking a particular set as com's first argument.

toYo : forall {X} -> DELAY X -> Delay X
toYo (now x)  = (ret x)
toYo (wait d) = com One <> (\ _ -> toYo d)

-- In Haskell, there's no way to tell the following computation trees
-- apart. The Yoneda encoding maps them all to the tree which delays
-- once then returns <>.

thing1 : Delay One
thing1 = com One <> (\ _ -> ret <>)
thing2 : Delay One
thing2 = com Two tt (\ _ -> ret <>)
thing3 : Delay One
thing3 = com Two ff (\ _ -> ret <>)

check12 : froYo thing1 == froYo thing2
check12 = refl
check13 : froYo thing1 == froYo thing3
check13 = refl
check23 : froYo thing2 == froYo thing3
check23 = refl

-- In Type Theory, we can prove they're different.

diff12 : thing1 == thing2 -> Zero
diff12 q = diffOneTwo (subst q (\ b -> Type thing1 == Type b) refl)

diff13 : thing1 == thing3 -> Zero
diff13 q = diffOneTwo (subst q (\ b -> Type thing1 == Type b) refl)

diff23 : thing2 == thing3 -> Zero
diff23 q = diffTF
  (subst q (\ b ->
            (Q : Type b == Two) ->
            shape <> thing2 == subst Q (\ X -> X) (shape <> b))
  (\ { refl -> refl })
  refl)

-- So the Yoneda encoding is not an iso, unlike in Haskell.
