Require Import
  Coq.Strings.String
  Hask.Control.Monad
  Hask.Control.Monad.Freer
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Inductive IO r :=
  | PutStrLn : string -> r -> IO r.

Instance IO_Functor : Functor IO := {
  fmap := fun _ _ f x =>
            match x with
            | PutStrLn s r => PutStrLn s (f r)
            end
}.

Open Scope string_scope.

Definition initS     := "init".
Definition putStrLnS := "putStrLn".

Definition IOSpec : ADT _ := ADTRep (Free IO unit) {
  Def Constructor0 initS : rep := ret (pure[Free IO] tt),
  Def Method1 putStrLnS (r : Free IO unit) (s : string) : rep * unit :=
    ret ((r >> liftF (PutStrLn s tt))%monad, tt)
}%ADTParsing.

Axiom IO_       : Type -> Type.
Axiom IOReturn_ : forall {a}, a -> IO_ a.
Axiom IOBind_   : forall {a b}, IO_ a -> IO_ b -> IO_ b.
Axiom putStrLn_ : string -> IO_ unit.

Axiom IO_monad_ : forall x : IO_ (),
  IOBind_ (IOReturn_ ()) x = IOBind_ x (IOReturn_ ()).
Axiom IO_monad_assoc_ : forall x y z : IO_ (),
  IOBind_ (IOBind_ x y) z = IOBind_ x (IOBind_ y z).

Definition interpret {a} (v : IO (IO_ a)) : IO_ a :=
  match v with
  | PutStrLn s z => IOBind_ (putStrLn_ s) z
  end.

Definition teardown `(f : Free IO a) : IO_ a :=
  @iter IO _ (IO_ a) interpret (fmap IOReturn_ f).

Program Definition Interpret_AbsR {A} (r_o : Free IO A) (r_n : IO_ A) :=
  r_n = teardown r_o.

Axiom Free_parametricity :
  forall `(fr : Free f a) `(k : a -> a) p
         (j : forall x : Type, (x -> a) -> f x -> a),
  k (fr a p j) = fr a (fun v => k (p v)) j.

Theorem HaskellIO : FullySharpened IOSpec.
Proof.
  start sharpening ADT.
  hone representation using Interpret_AbsR.
  {
    simplify with monad laws.
    refine pick val (IOReturn_ ()).
      finish honing.
    compute.
    reflexivity.
  }
  {
    simplify with monad laws.
    unfold Interpret_AbsR, comp; simpl.
    refine pick val (IOBind_ r_n (putStrLn_ d)).
      simplify with monad laws.
      finish honing.
    rewrite H0.
    unfold teardown, iter, comp, id; simpl.
    unfold comp.
    remember (fun (x : Type) (k : x -> IO_ ()) (x0 : IO x) =>
                interpret match x0 with
                          | PutStrLn s r => PutStrLn s (k r)
                          end) as k eqn:Heqe.
    pose proof (@Free_parametricity
                  IO (IO_ ()) (fmap IOReturn_ r_o)
                  (fun x => IOBind_ x (putStrLn_ d))
                  (fun _ => IOReturn_ ()) k) as H1.
    simpl in H1.
    unfold comp in H1.
    replace (fun x : () => IOReturn_ x) with (fun _ : () => IOReturn_ ()).
      compute.
      rewrite H1, Heqe.
      compute.
      f_equal.
      extensionality x.
      rewrite IO_monad_.
      reflexivity.
    extensionality x.
    destruct x.
    reflexivity.
  }
  finish_SharpeningADT_WithoutDelegation.
Defined.

Time Definition haskellIO := Eval simpl in (projT1 HaskellIO).
Print haskellIO.

Definition IO' := ComputationalADT.cRep haskellIO.

Definition initIO : IO' := Eval simpl in CallConstructor haskellIO initS.
Definition putStrLnIO (s : string) (r : IO') `(k : IO' -> a) : a :=
  Eval simpl in k (fst (CallMethod haskellIO putStrLnS r s)).

Definition notifyS := "notify".

Definition MonitorSpec : ADT _ := ADTRep unit {
  Def Constructor0 initS : rep := ret tt,
  Def Method2 notifyS (r : rep) (io : IO') (s : string) :
    rep * IO' :=
    putStrLnIO s io (fun io' => ret (tt, io'))
}%ADTParsing.

Definition runS := "run".

Definition MyProg : ADT _ := ADTRep unit {
  Def Constructor0 initS : rep := ret tt,
  Def Method1 runS (r : rep) (io : IO') : rep * IO' :=
    m   <- callCons MonitorSpec initS;
    putStrLnIO "Hello" io (fun io1 =>
      p   <- callMeth MonitorSpec notifyS m io1 "This is a test";
      putStrLnIO "Goodbye" (snd p) (fun io2 =>
        ret (tt, io2)))
}%ADTParsing.

Theorem SharpenedProg : FullySharpened MyProg.
Proof.
  start sharpening ADT.
  hone representation using eq.
  {
    simplify with monad laws.
    refine pick eq.
    finish honing.
  }
  {
    simplify with monad laws.
    simpl.
    rewrite !IO_monad_assoc_.
    refine pick eq.
    simplify with monad laws.
    finish honing.
  }
  finish_SharpeningADT_WithoutDelegation.
Defined.

Time Definition impl := Eval simpl in (projT1 SharpenedProg).
Print impl.

Definition initProg : ComputationalADT.cRep impl :=
  Eval simpl in CallConstructor impl initS.
Definition runProg (r : ComputationalADT.cRep impl) (io : IO') : IO' :=
  Eval simpl in snd (CallMethod impl runS r io).

Extraction Language Haskell.

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive Datatypes.prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extract Inductive Ascii.ascii => "Prelude.Char"
[ "{-- If this appears, you're using Ascii internals. Please don't --}
   (\b0 b1 b2 b3 b4 b5 b6 b7 ->
     let f b i = if b then Data.Bits.shiftL 1 (Prelude.fromIntegral i) else 0
     in Data.Char.chr (f b0 0 Prelude.+ f b1 1 Prelude.+ f b2 2 Prelude.+ f b3 3 Prelude.+ f b4 4 Prelude.+ f b5 5 Prelude.+ f b6 6 Prelude.+ f b7 7))"
]
"{-- If this appears, you're using Ascii internals. Please don't --}
 (\f c ->
   let n   = Data.Char.ord c
       h i = (Data.Bits..&.) n (Data.Bits.shiftL 1 (Prelude.fromIntegral i)) Prelude./= 0
   in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
".

Extract Constant IO_ "a" => "Prelude.IO a".
Extract Inlined Constant IOReturn_ => "(Prelude.return :: a -> Prelude.IO a)".
Extract Inlined Constant IOBind_ =>
  "((Prelude.>>) :: Prelude.IO a -> Prelude.IO b -> Prelude.IO b)".
Extract Inlined Constant putStrLn_ => "Prelude.putStrLn".

Extraction "HaskellIO.hs" initProg runProg.
