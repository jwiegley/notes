  - (* monad_law_2 *) intros. ext_eq. simpl.
    unfold compose, EitherT_join, EitherT_eta.
    simpl. destruct x.
    unfold EitherT_map, id.
    simpl. f_equal.
    rewrite fun_composition_x.
    unfold compose, Either_map.
    rewrite <- uncompose with (f := mu).
      assert ((fun x : Either E X =>
                 match
                   match x with
                   | Left e => Left E (EitherT E M X) e
                   | Right x' =>
                       Right E (EitherT E M X)
                         (EitherT_ E M X ((eta/M) (Right E X x')))
                   end
                 with
                 | Left e => (eta/M) (Left E X e)
                 | Right (EitherT_ mx') => mx'
                 end) = (@eta M _ (Either E X))).
        ext_eq. destruct x; reflexivity. rewrite H0. clear H0.
    apply monad_law_2_x.
    assumption.
