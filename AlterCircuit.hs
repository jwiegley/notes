{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Transform.AlterCircuit where

import Java

data Transform = Transform @firrtl.Transform deriving Class
data CircuitForm = CircuitForm @firrtl.CircuitForm deriving Class
data LowForm = LowForm @firrtl.LowForm$ deriving Class

type instance Inherits LowForm = '[CircuitForm]

data CircuitState = CircuitState @firrtl.CircuitState deriving Class
data Utils = Utils @firrtl.Utils
data Circuit = Circuit @firrtl.ir.Circuit deriving Class
data DefModule = DefModule @firrtl.ir.DefModule deriving Class
data Statement = Statement @firrtl.ir.Statement deriving Class
data Expression = Expression @firrtl.ir.Expression deriving Class
data Mux = Mux @firrtl.ir.Mux deriving Class

foreign import java unsafe "@static firrtl.LowForm$.MODULE$"
    lowForm :: LowForm

data AlterCircuit = AlterCircuit @tutorial.lesson3.AlterCircuit
   deriving Class

type instance Inherits AlterCircuit = '[Transform]

foreign import java unsafe get :: (c <: Transform) => Java c Int
foreign import java unsafe set :: (c <: Transform) => Int -> Java c ()

inputForm :: Java AlterCircuit CircuitForm
inputForm = return $ superCast lowForm

outputForm :: Java AlterCircuit CircuitForm
outputForm = return $ superCast lowForm

execute :: CircuitState -> Java AlterCircuit CircuitState
execute = error "Pass not implemented"

foreign export java inputForm  :: Java AlterCircuit CircuitForm
foreign export java outputForm :: Java AlterCircuit CircuitForm
foreign export java execute    :: CircuitState -> Java AlterCircuit CircuitState
