Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  induction c; intros;
  inversion H; inversion H0; clear H H0;
  try congruence; subst;
  try solve [ eapply IHc1; eauto | eapply IHc2; eauto ];
  firstorder.
  - apply IHc1 with st st' st'0 SContinue SContinue in H3; eauto.
    destruct H3; subst.
    eapply IHc2; eauto.
  - apply IHc1 with st st' st'0 SContinue SContinue in H3; eauto.
    destruct H3; subst.
    eapply IHc2; eauto.
  - apply IHc1 with st st' st2 SContinue SBreak in H3; eauto.
    destruct H3; discriminate.
  - apply IHc1 with st st' st2 SContinue SBreak in H3; eauto.
    destruct H3; discriminate.
  - apply IHc1 with st st1 st'0 SBreak SContinue in H6; eauto.
    destruct H6; discriminate.
  - apply IHc1 with st st1 st'0 SBreak SContinue in H6; eauto.
    destruct H6; discriminate.
  - apply IHc with st st' st'0 SContinue SContinue in H4; eauto.
    destruct H4; subst.
    pose proof (while_continue _ _ _ _ _ H8); subst.
    pose proof (while_continue _ _ _ _ _ H16); subst.
    admit.
  - apply IHc with st st' st2 SContinue SBreak in H4; eauto.
    destruct H4; discriminate.
  - apply IHc with st st1 st'0 SBreak SContinue in H7; eauto.
    destruct H7; discriminate.
  - apply IHc with st st1 st2 SBreak SBreak in H7; eauto.
    intuition.
Admitted.