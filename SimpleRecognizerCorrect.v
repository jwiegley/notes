    Lemma parse_item'_eq
          (offset : nat) (len : nat)
          (str_matches_nonterminal' :
             nonterminal_carrierT -> option simple_parse_of)
          (str_matches_nonterminal_eq :
             forall nt t,
               str_matches_nonterminal' nt = Some t ->
               simple_parse_of_correct G (substring offset len str) (Lookup G (to_nonterminal nt)) t)
          (it : item Char) nt t
    : SimpleRecognizer.parse_item' str str_matches_nonterminal' offset len it = Some t ->
      simple_parse_of_correct G (substring offset len str) (Lookup G (to_nonterminal nt)) t.
    Proof.
      
      t ltac:(rewrite !str_matches_nonterminal_eq).
    Qed.
