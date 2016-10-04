Require Import String.

(** Here's the type that we want to embed all of our computation in: *)

Inductive ErrorOrResult {T} :=
| Result : forall v: T, @ErrorOrResult T
| Error : forall s: string, @ErrorOrResult T.

(** Our first kind of expressions only manipulates [nat]s: *)

Inductive expr :=
| var : forall s: string, expr
| const : forall c: nat, expr
| sum : forall e1 e2: expr, expr.

(** Here's the eval function.  Note the type of env (it returns an error if it
    can't find the variable). *)

Fixpoint evalBasic (env: string -> @ErrorOrResult nat) expr :=
  match expr with
  | const c => Result c
  | var s => env s
  | sum e1 e2 =>
    match evalBasic env e1 with
    | Error err => Error err
    | Result n1 => match evalBasic env e2 with
                  | Error err => Error err
                  | Result n2 => Result (n1 + n2)
                  end
    end
  end.

(** The error handling part is painful, so we introduce the error monad: *)
Definition Bind {T} : @ErrorOrResult T -> (T -> @ErrorOrResult T) -> @ErrorOrResult T :=
  fun val func =>
    match val with
    | Error err => Error err
    | Result v => (func v)
    end.

Notation ret v := (Result v).

Notation "x <- m ; y" := (Bind m (fun x => y))
                           (at level 51, right associativity,
                            format "'[v' x  <-  m ; '/' y ']'").

(** Here's our new function: *)

Fixpoint evalMonad env e :=
  match e with
  | const c => ret c
  | var s => env s
  | sum e1 e2 =>
    n1 <- evalMonad env e1;
    n2 <- evalMonad env e2;
    ret (n1 + n2)
  end.

(** Of course, these two things are exactly the same under the hood: *)

Lemma evalBasic_evalMonad :
  forall env e,
    evalBasic env e = evalMonad env e.
Proof.
  induction e; reflexivity.
Qed.

(** Here's a second example, this time with two types: *)

Inductive Value :=
| Nat: forall n: nat, Value
| Bool: forall b: bool, Value.

Inductive expr' :=
| var' : forall s: string, expr'
| const' : forall c: Value, expr'
| not' : forall e: expr', expr'       (* for booleans *)
| sum' : forall e1 e2: expr', expr'.  (* for nats *)

Fixpoint eval'Basic env expr :=
  match expr with
  | const' c => Result c
  | var' s => env s
  | sum' e1 e2 =>
    match eval'Basic env e1 with
    | Error err => Error err
    | Result v1 => match v1 with
                  | Bool _ => Error "Type error"
                  | Nat n1 => match eval'Basic env e2 with
                             | Error err => Error err
                             | Result v2 =>
                               match v2 with
                               | Bool _ => Error "Type error"
                               | Nat n2 => Result (Nat (n1 + n2))
                               end
                             end
                  end
    end
  | not' e =>
    match eval'Basic env e with
    | Error err => Error err
    | Result v => match v with
                 | Nat _ => Error "Type error"
                 | Bool b => Result (Bool (negb b))
                 end
    end
  end.

(** We can apply the same trick to simplify away the boilerplate: *)

Notation raise e := (Error e).

Fixpoint eval'Monad env expr :=
  match expr with
  | const' c => Result c
  | var' s => env s
  | sum' e1 e2 =>
    v1 <- eval'Monad env e1;
    match v1 with
    | Bool _ => raise "Type error"
    | Nat n1 => v2 <- eval'Monad env e2;
               match v2 with
               | Bool _ => raise "Type error"
               | Nat n2 => ret (Nat (n1 + n2))
               end
    end
  | not' e =>
    v <- eval'Monad env e;
    match v with
    | Nat _ => raise "Type error"
    | Bool b => ret (Bool (negb b))
    end
  end.

(** Finally, adding an extra layer of notations helps clean things up: *)

Definition BindNat : ErrorOrResult -> (nat -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | Bool _ => Error "Type error"
    | Nat n => func n
    end.

Definition BindBool : ErrorOrResult -> (bool -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | Nat _ => Error "Type error"
    | Bool b => func b
    end.

Notation "x <nat- m ; y" := (BindNat m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <nat-  m ; '/' y ']'").

Notation "x <bool- m ; y" := (BindBool m (fun x => y))
                              (at level 51, right associativity,
                               format "'[v' x  <bool-  m ; '/' y ']'").

Notation retNat v := (Result (Nat v)).
Notation retBool v := (Result (Bool v)).

Fixpoint eval'Notations env e :=
  match e with
  | const' c => ret c
  | var' s => env s
  | sum' e1 e2 =>
    n1 <nat- eval'Notations env e1;
    n2 <nat- eval'Notations env e2;
    retNat (n1 + n2)
  | not' e =>
    b <bool- eval'Notations env e;
    retBool (negb b)
  end.

(** Again, this is all syntactic sugar: *)
Lemma eval'Basic_eval'Notations :
  forall env e,
    eval'Basic env e = eval'Notations env e.
Proof.
  induction e; reflexivity.
Qed.
