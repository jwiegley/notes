Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Hask.Data.List.

Generalizable All Variables.

Inductive Context a := C : seq a -> a -> seq a -> Context a.

Arguments C : default implicits.

Definition context_join `(x : Context (Context a)) : Context a :=
  match x with
  | C ins (C innerIns n innerOuts) outs =>
    C (flatten (map (fun c => match c with C i x o => i ++ x :: o end) ins)
        ++ innerIns)
      n
      (innerOuts ++
       flatten (map (fun c => match c with C i x o => i ++ x :: o end) outs))
  end.

Instance Context_Functor : Functor Context := {
  fmap := fun _ _ f x => match x with
    | C ins a outs => C (map f ins) (f a) (map f outs)
    end
}.

Instance Context_Applicative : Applicative Context := {
  pure := fun _ x => C [::] x [::];
  ap   := fun _ _ fs xs => match fs with
    | C fins fa fouts => match xs with
      | C xins xa xouts => C (map (fun f => f xa) fins ++ map fa xins)
                             (fa xa)
                             (map (fun f => f xa) fouts ++ map fa xouts)
      end
    end
}.

Instance Context_Monad : Monad Context := {
  join := fun _ => context_join
}.

Module ContextLaws.

Include ListLaws.

Program Instance Context_FunctorLaws : FunctorLaws Context.
Obligation 1.
  move=> [ins x outs].
  by rewrite !map_id.
Qed.
Obligation 2.
  move=> [ins x outs].
  by rewrite /funcomp /= -!map_comp /funcomp.
Qed.

Program Instance Context_ApplicativeLaws : ApplicativeLaws Context.
Obligation 1.
  move=> [ins x outs].
  by rewrite !map_id.
Qed.
Obligation 2.
  move: u => [u_ins u_x u_outs].
  move: v => [v_ins v_x v_outs].
  move: w => [w_ins w_x w_outs].
  by rewrite -!map_comp !map_cat -!map_comp !catA.
Qed.
Obligation 4.
  move: u => [u_ins u_x u_outs].
  by rewrite !cats0.
Qed.

Program Instance Context_MonadLaws : MonadLaws Context.
Obligation 1.
  move=> [ins x outs].
  rewrite /funcomp.
  move: x => [x_ins [x_ins' x x_outs'] x_outs] /=.
  rewrite !catA -!flatten_cat -!map_cat.
  elim: outs => [|out outs IHouts] //=.
    elim: ins => [|in_ ins IHins] //=.
      by rewrite !cats0.
    inversion IHins.
    f_equal.
    rewrite -catA {}H0 {IHins H1}.
    rewrite !map_cat !flatten_cat -!catA.
    f_equal.
    move: in_ => [in_ins [innerIns in_ innerOuts] in_outs] /=.
    rewrite -!catA !map_cat !flatten_cat.
    f_equal.
    by rewrite /= -!catA cat_cons.
  inversion IHouts.
  rewrite {IHouts H0}.
  f_equal.
  rewrite -catA.
  rewrite !map_cat !flatten_cat.
  f_equal.
  f_equal.
  rewrite -flatten_cat -map_cat.
  move: out => [out_ins [innerIns out innerOuts] out_outs] /=.
  rewrite -!catA !map_cat !flatten_cat.
  f_equal.
  rewrite /= -!catA cat_cons.
  f_equal.
  f_equal.
  f_equal.
  f_equal.
  rewrite -catA in H1.
  assert (forall (xs ys zs : seq a), xs ++ ys = xs ++ zs -> ys = zs).
    elim=> [|w ws IHws] //=.
    move=> ys zs H.
    apply: IHws.
    by inversion H.
  move: H1.
  set ys := (X in x_outs' ++ X = _).
  set zs := (X in x_outs' ++ _ = x_outs' ++ X).
  move/(H x_outs' ys zs).
  rewrite /ys /zs.
  rewrite !map_cat !flatten_cat.
  move/H => H1.
  by rewrite H1.
Qed.
Obligation 2.
  move=> [ins x outs].
  rewrite /funcomp /=.
  elim: outs => [|out outs IHouts] //=.
    elim: ins => [|in_ ins IHins] //=.
    f_equal.
    inversion IHins.
    by rewrite !H0.
  elim: ins => [|in_ ins IHins] //= in IHouts *.
    f_equal.
    inversion IHouts.
    by rewrite !H0.
  f_equal.
    inversion IHouts.
    by rewrite !H0.
  inversion IHouts.
  by rewrite !H1.
Qed.
Obligation 3.
  move=> [ins x outs].
  by rewrite /funcomp /= cats0.
Qed.
Obligation 4.
  move=> [ins x outs].
  rewrite /funcomp /=.
  move: x => [x_ins x x_outs].
  f_equal.
    rewrite !map_cat.
    f_equal.
    elim: ins => [|in_ ins IHins] //=.
    move: in_ => [in_ins in_ in_outs].
    rewrite -!catA map_cat.
    f_equal.
    rewrite map_cat -map_cons.
    f_equal.
    by rewrite IHins.
  rewrite !map_cat.
  f_equal.
  elim: outs => [|out outs IHouts] //=.
  move: out => [out_ins out out_outs].
  rewrite -!catA map_cat.
  f_equal.
  rewrite map_cat -map_cons.
  f_equal.
  by rewrite IHouts.
Qed.
