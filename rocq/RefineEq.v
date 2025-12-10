(* [23:04:01] <Cypi> The idea is to generalize [@macroNStep conf n
   (finalConfig_dec conf)] and the equality at the same time *)

Lemma macroStepLemma: forall conf W C n,
  correct_configuration conf ->
    @macroNStep conf n (finalConfig_dec conf) = Some (@macroStep conf W C n).
Proof.
  intros.
  unfold macroStep.
  refine (
    (fun H => _) (_ :
    (forall (x : option configuration)
            (e : x = macroNStep n (finalConfig_dec conf)),
     macroNStep n (finalConfig_dec conf) =
     Some (match x as o return
         (o = macroNStep n (finalConfig_dec conf) -> configuration)
       with
       | Some conf' =>
           fun _ : Some conf' = macroNStep n (finalConfig_dec conf) => conf'
       | None =>
           fun Heq_anonymous : None = macroNStep n (finalConfig_dec conf) => !
       end e)))).
  - apply H.
  - intros. destruct x.
    + rewrite <- e.
      reflexivity.
    + exfalso.
      destruct (finalConfig_dec _) eqn:?.
        destruct n; discriminate.
      induction n; [discriminate|].
      apply IHn; clear IHn.
      simpl in e.
      rewrite <- Heqs; clear Heqs.
      (* jww (2017-12-21): I'm not sure this theorem helps... Is macroNStep
         defined correctly? *)
      destruct (wellFormedNoErrorNotFinal W (initialImplyProgress C) H n0).
      rewrite <- H0 in e; clear H0.
      rewrite e; clear e.
      (* jww (2017-12-21): The goal is now:

         macroNStep n (finalConfig_dec x) = macroNStep n (finalConfig_dec conf)

         But what do we know about the relationship between [x] and [conf]? *)
Admitted.
