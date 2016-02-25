  Lemma parse_item'_eq
        (offset : nat) (len : nat)
        (str_matches_nonterminal' :
           nonterminal_carrierT -> option simple_parse_of)
        (str_matches_nonterminal_eq :
           forall nt t,
             str_matches_nonterminal' nt = Some t ->
             simple_parse_of_correct G (substring offset len str)
                                     (Lookup G (to_nonterminal nt)) t)
        (it : item Char) t
  : SimpleRecognizer.parse_item'
      str str_matches_nonterminal' offset len it = Some t ->
      match it with
      | Terminal x => True
      | NonTerminal s => List.In s (Valid_nonterminals G)
      end ->
      simple_parse_of_item_correct G (substring offset len str) it t.
  Proof.
    intro H.
    destruct it; simpl in *; intros.
    { (* Terminal case *)
      clear str_matches_nonterminal' str_matches_nonterminal_eq.
      destruct (EqNat.beq_nat len 1 && char_at_matches offset str b)%bool eqn:Heqe;
        [| discriminate].
      pose proof Heqe.
      inversion H; clear H; subst.
      apply Bool.andb_true_iff in H1; destruct H1.
      apply EqNat.beq_nat_true in H; subst.
      admit. }
    { destruct (str_matches_nonterminal' (of_nonterminal s)) eqn:Heqe; simpl in *;
        [| discriminate].
      specialize (str_matches_nonterminal_eq (of_nonterminal s) s0 Heqe).
      inversion H; clear H; subst.
      clear Heqe str_matches_nonterminal'.
      rewrite to_of_nonterminal in str_matches_nonterminal_eq.
      unfold simple_parse_of_correct in str_matches_nonterminal_eq.
      unfold simple_parse_of_item_correct.
      induction s0; simpl in *; intros; intuition.
      assumption. }
  Qed.
