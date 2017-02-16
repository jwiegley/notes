Require Import Reals.

Open Scope R_scope.

Definition irrational (n : R) :=
  not (exists p : nat, exists q : nat, n = INR p / INR q).

Lemma sqrt_inv : forall x y, 0 <= x -> sqrt x = y -> x = y².
Proof.
  intros.
  rewrite <- H0.
  rewrite Rsqr_sqrt; trivial.
Qed.

Lemma Rdiv_mult : forall x y z, x = y / z -> x * z = y.
Admitted.

Lemma Rplus_split : forall p q n : R, p = q + n.
Admitted.

(* Theorem: The square root of 3 is irrational.

Proof: Let us proceed by assuming the square root of 3 is in fact rational.
That is, √3 = p/q (1), for some integers p and q, having no common factors,
and where p > q.

Our equation may be rewritten 3q² = p² (2).  Now, if q were even, the since
multiplying an even by even (as in qq) is even, and multiplying an odd by an
even is even, p would also be even.  However, then p and q would have a common
factor, namely 2, which we stated they did not.  Therefore both p and q must
be odd.

Further, since p > q, p can be substituted by q + n, where n is some positive
integer.  So our equation is now 3q² = (q+n)², and can be simplified in terms
of q as follows:

    3q² = (q + n)²                                       (3)
    3q² = q² + 2qn + n²                                  (4)
    3q² - q² = q² + 2qn + n² - q²                        (5)
    2q² = 2qn + n²                                       (6)
    q² = qn + n²/2                                       (7)

Since we know that q and p are both odd, n must be a multiple of two, since
only by adding an even to an odd may we reach another even.  We can express
this by saying that n = 2k for some positive integer k, and by substituting
this term in our equation:

    q² = 2kq + (2k)²/2                                   (8)
    q² = 2kq + 4k²/2                                     (9)
    q² = 2kq + 2k²                                      (10)
    q² = 2(kq + k²)                                     (11)

Since the right side is even, q² must be even, and so q must be even.  But
since we asserted that q must be odd, our assumption is therefore false.  Thus
the hypothesis, that the square root of 3 is irrational, has been proven
true. ∎ *)
Theorem sqrt_3_irrational : irrational (sqrt 3).
Proof.
  unfold irrational, not; intros.
  do 2 destruct H.
  remember (INR x) as p.
  remember (INR x0) as q.
  evar (n : R).
  erewrite (@Rplus_split p q n) in H.
  apply sqrt_inv in H.
  rewrite Rsqr_div in H.
  apply Rdiv_mult in H.
  rewrite Rsqr_plus in H.
Abort.
