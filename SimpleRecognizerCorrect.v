    Lemma parse_item'_eq
          (str_matches_nonterminal' : nonterminal_carrierT -> option simple_parse_of)
          (str_matches_nonterminal_eq : forall nt t, str_matches_nonterminal' nt = Some t)
          (offset : nat) (len : nat)
          (it : item Char) str t
    : SimpleRecognizer.parse_item' str str_matches_nonterminal' offset len it = Some t.
