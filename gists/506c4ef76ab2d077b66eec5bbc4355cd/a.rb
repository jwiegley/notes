✔ ~/src/categories [master|✚ 2]
15:31:30 [1.769s] Vulcan $ cabal build && ./dist/build/categories/categories
Building categories-0.1.0.0...
Preprocessing executable 'categories' for categories-0.1.0.0...
[1 of 2] Compiling Categorical      ( src/Categorical.hs, dist/build/categories/categories-tmp/Categorical.o )
[2 of 2] Compiling Main             ( src/Main.hs, dist/build/categories/categories-tmp/Main.o )
ghc: panic! (the 'impossible' happened)
  (GHC version 8.0.2 for x86_64-apple-darwin):
	ccc - couldn't build dictionary for
  coerceC
    @ (->)
    @ (State# RealWorld -> (# State# RealWorld, () #))
    @ (IO ()) :: CoerceCat
                   (->) (State# RealWorld -> (# State# RealWorld, () #)) (IO ()) =>
                 (State# RealWorld -> (# State# RealWorld, () #)) -> IO ():
  coercion holes:  [$dCoercible_am6a
                      :: Coercible
                           (State# RealWorld -> (# State# RealWorld, () #)) (IO ())
                    [LclId, Str=DmdType]
                    $dCoercible_am6a =
                      MkCoercible
                        @ *
                        @ (State# RealWorld -> (# State# RealWorld, () #))
                        @ (IO ())
                        @~ (U(hole:{am6b}, State# RealWorld
                                           -> (# State# RealWorld, () #), IO ())_R
                            :: ((State# RealWorld -> (# State# RealWorld, () #)) :: *)
                               ~R#
                               (IO () :: *))]

Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug