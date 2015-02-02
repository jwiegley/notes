module hello where

open import Data.Unit using (⊤)
open import IO
import IO.Primitive as Prim

main′ : IO ⊤
main′ = putStrLn "Hello. world"

main : Prim.IO ⊤
main = run main′
