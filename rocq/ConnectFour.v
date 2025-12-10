Inductive Color := Red | Yellow.

Inductive CFour (fp : Color) : Color -> Set :=
  | GameWon : CFour fp fp
  | Move color : nat -> nat -> CFour fp color
                   -> CFour fp (if color then Yellow else Red).
