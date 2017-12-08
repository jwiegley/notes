Require Import Coq.Program.Wf.

Program Fixpoint blef (arg: nat * string) {measure (mm arg)} : bool :=
   let seq n m :=
      fun s1s2 => match s1s2 with
      | (s1, s2) => if blef (n, s1) then blef (m, s2) else false
      end
   in
   let subs n m :=
      fix subs s1s2s := match s1s2s with
      | [] => false
      | s1s2 :: more => if seq n m s1s2 then true else subs more
      end
   in
   match arg with
   | (S n, s0) =>
        subs n (S n) (get_substrings s0)
   | _ => false
   end.
Next Obligation.
  (* n + length s < mm (n0, s3) *)
Admitted.
Next Obligation.
  (* m + length s0 < mm (n0, s3) *)
Admitted.
