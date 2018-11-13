---- MODULE simple ----

EXTENDS Integers, TLC

(* --algorithm simple {
  variables value =
    CHOOSE <<x, y>> \in (-10..10) \X (-10..10):
      /\ 2*x +   y = -2
      /\ 3*x - 2*y = 11;

  {
    print value;
  }
} *)

\* BEGIN TRANSLATION
VARIABLES value, pc

vars == << value, pc >>

Init == (* Global variables *)
        /\ value = (CHOOSE <<x, y>> \in (-10..10) \X (-10..10):
                      /\ 2*x +   y = -2
                      /\ 3*x - 2*y = 11)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(value)
         /\ pc' = "Done"
         /\ value' = value

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Mar 25 08:41:58 CET 2015 by bela
\* Created Wed Mar 25 08:25:16 CET 2015 by bela
