  - (* right_identity *)
    intros.
    destruct f.
    unfold nat_identity, nat_compose.
    simpl.
    (* rewrite <- right_identity with (f := transport0) in naturality0. *)
    apply f_equal2.
