{- Maybe capabilities are a poor man's replacement for dependency types. -}

{------------------------------------------------------------------------}

{-
Definition State (s a : Type) := s → (a * s).

Definition sell (seller buyer : Person) (house : House) :
  State [Person * House] ().

Definition get_ice_cream : State [Person * IceCream] IceCream
-}

list (Name * PublicKey)

withdraw : Name → Signed SecretKey a → Amount → Bank → Bank

deposit : Name → Amount → Bank → Bank

transfer : Name → Signed SecretKey a → Name → Amount
