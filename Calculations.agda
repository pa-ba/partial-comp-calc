{-# OPTIONS --sized-types --guardedness #-}

module Calculations where

-- Stack machine calculations
import Calculations.Stack.Cond
import Calculations.Stack.CondPrint
import Calculations.Stack.Lambda
import Calculations.Stack.LambdaBoolFix
import Calculations.Stack.LambdaFix
import Calculations.Stack.RaTT
import Calculations.Stack.LambdaConcur

-- Register machine calculations
import Calculations.Memory.Lambda
import Calculations.Memory.Loop
import Calculations.Memory.Print
import Calculations.Memory.Concur
import Calculations.Memory.LambdaConcur

-- Termination arguments
import Calculations.Terminating.LambdaConcur
