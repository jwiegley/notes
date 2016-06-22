  Case "tfix". (* JSTOLAREK : stuck here *)
    apply T_Fix.
    apply IHt.
    inversion H.
      assumption.
    subst.
