{-# OPTIONS --sized-types #-}

module Calculations where

-- Calculation in the Maybe monad
import Calculations.Maybe.Cond

-- Stack machine calculations
import Calculations.Stack.Cond
import Calculations.Stack.CondPrintFlip
import Calculations.Stack.Lambda
import Calculations.Stack.LambdaBoolFix
import Calculations.Stack.LambdaFix
import Calculations.Stack.Rattus
import Calculations.Stack.LambdaConcur

-- Register machine calculations
import Calculations.Memory.Lambda
import Calculations.Memory.Loop
import Calculations.Memory.Print
import Calculations.Memory.Concur
import Calculations.Memory.LambdaConcur

-- Termination arguments
import Calculations.Terminating.Stack.Lambda
import Calculations.Terminating.Stack.LambdaBoolFix
import Calculations.Terminating.Stack.LambdaFix
import Calculations.Terminating.Stack.Rattus
import Calculations.Terminating.Stack.LambdaConcur
import Calculations.Terminating.Memory.Lambda
import Calculations.Terminating.Memory.LambdaConcur
