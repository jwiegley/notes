Inductive AuthLevel := Public | Secret.

Definition doPublicComputation (l : AuthLevel) (H : l = Public) : nat := 0.
Definition doSecureComputation (l : AuthLevel) (H : l = Secret) : nat := 100.

Definition authenticator : AuthLevel := Public.

Definition executor :=
  let level := authenticator
  in match level with
    (* This fails with the following error:

       The term "doPublicComputation level" has type "level = Public -> nat"
        while it is expected to have type "level = Secret -> nat".

       If I flip the functions, it compiles fine.
    *)
    | Secret => doPublicComputation level
    | Public => doSecureComputation level
  end.
