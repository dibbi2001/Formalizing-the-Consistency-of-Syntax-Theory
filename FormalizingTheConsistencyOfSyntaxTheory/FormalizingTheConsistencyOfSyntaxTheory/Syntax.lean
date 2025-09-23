import Mathlib.ModelTheory.Semantics

namespace FirstOrder

inductive peanoarithmeticFunc : ℕ → Type
  | zero : peanoarithmeticFunc 0
  | succ : peanoarithmeticFunc 1
  | add : peanoarithmeticFunc 2
  | mult : peanoarithmeticFunc 2
  deriving DecidableEq

def Language.peanoarithmetic : Language :=
  { Functions := peanoarithmeticFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic
