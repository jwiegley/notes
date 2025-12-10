Require Import Bool.Bool Arith List.

Inductive type:Set:=Nat|Bool.

Inductive tbinop:type->type->type->Set:=
  |TPlus:tbinop Nat Nat Nat
  |TTimes:tbinop Nat Nat Nat
  |TEq:forall t, tbinop t t Bool
  |Tlt:tbinop Nat Nat Bool.

Inductive texp:type->Set:=
  |TNConst:nat->texp Nat
  |TBConst:bool->texp Bool
  |TBinop:forall t1 t2 t, tbinop t1 t2 t->texp t1->texp t2->texp t.

Definition typeDenote(t:type):Set:=
  match t with
    |Nat=>nat
    |Bool=>bool
  end.

Definition tbinopDenote arg1 arg2 res(b:tbinop arg1 arg2 res):typeDenote
arg1->typeDenote arg2->typeDenote res:=
  match b with
    |TPlus=>plus
    |TTimes=>mult
    |TEq Nat=>beq_nat
    |TEq Bool=>eqb
    |TLt=>leb
  end.

Fixpoint texpDenote t (e:texp t):typeDenote t:=
  match e with
    |TNConst n=>n
    |TBConst b=>b
    |TBinop _ _ _ b e1 e2=> tbinopDenote _ _ _ b (texpDenote _ e1) (texpDenote _ e2)
  end.
