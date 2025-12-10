Class Functor f := {
  fmap : forall a b : Type, (a -> b) -> f a -> f b
}.

Extraction Language Haskell.

Set Extraction KeepSingleton.
Unset Extraction AutoInline.
Unset Extraction Optimize.

Extraction Functor.

(* data Functor f = *)
(*    Build_Functor (() -> () -> (Any -> Any) -> f -> f) *)

Inductive Yoneda (f : Type -> Type) (a : Type) :=
  Y : (forall {r : Type}, (a -> r) -> f r) -> Yoneda f a.

Definition Foo {f : Type -> Type} `{Functor f} (n : f nat) : Yoneda f nat :=
  Y f nat (fun _ k => fmap _ _ k n).

Recursive Extraction Foo.