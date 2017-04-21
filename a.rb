ghc: panic! (the 'impossible' happened)
  (GHC version 8.0.2 for x86_64-apple-darwin):
	ccc post-transfo check. Lint
  <no location info>: warning:
      In the expression: curry
                           @ (NonDet Int)
                           @ (V 'V2 Int)
                           @ (V 'V2 Int)
                           @ (V 'V2 Int)
                           ($fClosedCatNonDet @ Int $fNumInt)
                           (($fYes1ka @ * @ (V 'V2 Int), $fYes1ka @ * @ (V 'V2 Int),
                             $fYes1ka @ * @ (V 'V2 Int))
                            `cast` ((Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N,
                                     Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N,
                                     Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N)_R
                                    :: ((Yes1 (V 'V2 Int), Yes1 (V 'V2 Int),
                                         Yes1 (V 'V2 Int)) :: Constraint)
                                       ~R#
                                       ((Ok (NonDet Int) (V 'V2 Int), Ok (NonDet Int) (V 'V2 Int),
                                         Ok (NonDet Int) (V 'V2 Int)) :: Constraint)))
                           (ccc
                              @ (NonDet Int)
                              @ (Prod (->) (V 'V2 Int) (V 'V2 Int))
                              @ (V 'V2 Int)
                              ($fProgramCat(->)Int_$cadd @ 'V2))
                           ((boxI 2#)
                            `cast` (Sym (N:V[0] <'V2>_P <Int>_R)
                                    :: (Int :: *) ~R# (V 'V2 Int :: *)))
      Non-function type in function position
      Fun type:
          NonDet Int (V 'V2 Int) (Exp (NonDet Int) (V 'V2 Int) (V 'V2 Int))
      Arg type: V 'V2 Int
      Arg:
          (boxI 2#)
          `cast` (Sym (N:V[0] <'V2>_P <Int>_R)
                  :: (Int :: *) ~R# (V 'V2 Int :: *))
  ccc
    @ (NonDet Int)
    @ (V 'V2 Int)
    @ (V 'V2 Int)
    (curry
       @ (->)
       @ (V 'V2 Int)
       @ (V 'V2 Int)
       @ (V 'V2 Int)
       $fClosedCat(->)
       (($fYes1ka @ * @ (V 'V2 Int), $fYes1ka @ * @ (V 'V2 Int),
         $fYes1ka @ * @ (V 'V2 Int))
        `cast` ((Sym R:Ok(->)[0] <V 'V2 Int>_N,
                 Sym R:Ok(->)[0] <V 'V2 Int>_N, Sym R:Ok(->)[0] <V 'V2 Int>_N)_R
                :: ((Yes1 (V 'V2 Int), Yes1 (V 'V2 Int),
                     Yes1 (V 'V2 Int)) :: Constraint)
                   ~R#
                   ((Ok (->) (V 'V2 Int), Ok (->) (V 'V2 Int),
                     Ok (->) (V 'V2 Int)) :: Constraint)))
       ($fProgramCat(->)Int_$cadd @ 'V2)
       ((boxI 2#)
        `cast` (Sym (N:V[0] <'V2>_P <Int>_R)
                :: (Int :: *) ~R# (V 'V2 Int :: *))))
  -->
  curry
    @ (NonDet Int)
    @ (V 'V2 Int)
    @ (V 'V2 Int)
    @ (V 'V2 Int)
    ($fClosedCatNonDet @ Int $fNumInt)
    (($fYes1ka @ * @ (V 'V2 Int), $fYes1ka @ * @ (V 'V2 Int),
      $fYes1ka @ * @ (V 'V2 Int))
     `cast` ((Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N,
              Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N,
              Sym (R:OkNonDet[0] <Int>_N) <V 'V2 Int>_N)_R
             :: ((Yes1 (V 'V2 Int), Yes1 (V 'V2 Int),
                  Yes1 (V 'V2 Int)) :: Constraint)
                ~R#
                ((Ok (NonDet Int) (V 'V2 Int), Ok (NonDet Int) (V 'V2 Int),
                  Ok (NonDet Int) (V 'V2 Int)) :: Constraint)))
    (ccc
       @ (NonDet Int)
       @ (Prod (->) (V 'V2 Int) (V 'V2 Int))
       @ (V 'V2 Int)
       ($fProgramCat(->)Int_$cadd @ 'V2))
    ((boxI 2#)
     `cast` (Sym (N:V[0] <'V2>_P <Int>_R)
             :: (Int :: *) ~R# (V 'V2 Int :: *)))