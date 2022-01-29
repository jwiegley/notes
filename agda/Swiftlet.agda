module Swiftlet where

open import Data.Integer
open import Data.Product
open import Data.String
open import Data.List

Name : Set
Name = String

mutual
  Context : Set
  Context = Name → Qual × Value

  Prog : Set
  Prog = List Struct × Expr

  Struct : Set
  Struct = Name × List Bind

  data Qual : Set where
    qlet, qvar : Qual

  Bind : Set
  Bind = Qual × Name × Type

  data Arg : Set where
    apath : Path → Arg
    aexpr : Expr → Arg

  data Expr : Set where
    seq   : Expr → Expr → Expr
    e=in  : Bind → Expr → Expr → Expr
    e     : Path → Expr → Expr
    [e]   : List Expr → Expr
    epath : Path → Expr
    eval  : Value → Expr
    ecall : Name → List Expr → Expr
    earg  : Expr → List Arg → Expr
    etern : Expr → Expr → Expr → Expr
    etyp  : Expr → Type → Expr

  data Param : Set where
    inout : Type → Param
    param : Type → Param

  data Type : Set where
    func  : List Param → Type → Type
    array : List Type → Type
    ty    : Name → Type
    Int   : Type
    Any   : Type
    unit  : Type

  data Path : Set where
    dot  : Expr → Name → Path
    sub  : Expr → Expr → Path
    lval : LValue → Path

  data Value : Set where
    lam  : List (Name × Param) → Expr → Value
    ctx  : Context → Value
    ary  : List Value → Value
    box  : Value → Value
    int  : ℤ → Value

  data LValue : Set where
    ldot  : LValue → Name → LValue
    lsub  : LValue → ℤ → LValue
    lname : Name → LValue

-- c x, s µ , φs  g d m b a e

-- p τ r v w

-- :

-- ::=

-- X

-- →

-- M

-- ×

-- V

-- de

-- :: { }

-- =

-- struct

-- s

-- b

-- ;

-- ::=

-- ::=

-- ::=

-- let | var

-- mx: τ &r | e

-- :: | | | |

-- =

-- e;

-- e

-- b

-- =

-- e

-- in

-- e

-- r

-- =

-- e

-- |

-- [

-- e

-- ]

-- r

-- v

-- |

-- |

-- ::=

-- s |

-- ( |

-- e |

-- )

-- e

-- (

-- a

-- )

-- e

-- ?

-- e

-- :

-- e

-- e

-- as

-- τ

-- func x ( x : p) → τ { [ x ] in e } in e

-- inout τ | τ

-- ::

-- =

-- (

-- p

-- )

-- →

-- τ

-- |

-- [

-- τ

-- ]

-- |

-- s

-- |

-- Z

-- |

-- Any

-- |

-- ()

-- ::=

-- e.x | e[e]

-- |

-- w

-- :: | φ s | | |

-- =

-- λ

-- (

-- x

-- :

-- p,

-- e

-- )

-- [

-- v

-- ]

-- box

-- (

-- v

-- )

-- c

-- ::=

-- w.x | w[c]

-- |

-- x
