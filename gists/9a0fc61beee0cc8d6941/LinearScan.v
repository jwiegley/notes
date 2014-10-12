(** The extent of a [Range] is the set of locations it ranges over.  By
    summing the extent of a list of ranges, we have an idea of how much ground
    is left to cover, and this gives us a notion of well-founded recursion for
    iterating over intervals that may split as we examine them -- i.e., whose
    total extent must decrease after each pass.

    A Range is built up from a set of use positions, and defines the inclusive
    range of those positions.  It can be extended, or split, but never shrunk.
    Also, the non-empty list of use positions is not guaranteed to be in any
    order, and overlapping use positions are accepted but only the most recent
    one "wins". *)

Record RangeDesc := {
    rbeg : nat;
    rend : nat;
    ups  : NonEmpty UsePos
}.

Inductive Range : RangeDesc -> Set :=
  | R_Sing u :
      Range {| rbeg := uloc u
             ; rend := uloc u
             ; ups  := NE_Sing u
             |}
  | R_Cons u x :
      Range x
        -> uloc u < rbeg x
        -> Range {| rbeg := min (uloc u) (rbeg x)
                  ; rend := rend x
                  ; ups  := NE_Cons u (ups x)
                  |}
  | R_Extend x b' e' :
      Range x
        -> Range {| rbeg := min b' (rbeg x)
                  ; rend := Peano.max e' (rend x)
                  ; ups  := ups x
                  |}.
