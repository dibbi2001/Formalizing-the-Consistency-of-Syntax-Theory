import Mathlib.ModelTheory.Semantics

variable {α : Type*} {n : ℕ}

namespace FirstOrder

inductive peanoarithmeticFunc : ℕ → Type
  | zero : peanoarithmeticFunc 0
  | succ : peanoarithmeticFunc 1
  | add : peanoarithmeticFunc 2
  | mult : peanoarithmeticFunc 2
  | neg : peanoarithmeticFunc 1
  | and : peanoarithmeticFunc 2
  | or : peanoarithmeticFunc 2
  | imp : peanoarithmeticFunc 2
  | all : peanoarithmeticFunc 1
  | ex : peanoarithmeticFunc 1
  deriving DecidableEq

inductive peanoarithmeticRel : ℕ → Type
  | var : peanoarithmeticRel 1
  | term : peanoarithmeticRel 1
  | const : peanoarithmeticRel 1
  | bdform : peanoarithmeticRel 1
  deriving DecidableEq

def Language.peanoarithmetic : Language :=
  { Functions := peanoarithmeticFunc
    Relations := peanoarithmeticRel }

namespace Language.peanoarithmetic

universe u

instance : Zero (peanoarithmetic.Term α) where
  zero := Constants.term .zero

def null : Term peanoarithmetic α :=
  Constants.term .zero

def numeral : ℕ → peanoarithmetic.Term α
  | .zero => null
  | .succ n => Term.func peanoarithmeticFunc.succ (λ _ => numeral n)

class Succ (α : Type u) where
  succ : α → α

instance : Succ (peanoarithmetic.Term α) where
  succ := Functions.apply₁ .succ

instance : Add (peanoarithmetic.Term α) where
  add := Functions.apply₂ .add

instance : Mul (peanoarithmetic.Term α) where
  mul := Functions.apply₂ .mult

instance : Neg (peanoarithmetic.Term α) where
  neg := Functions.apply₁ .neg

instance : Min (peanoarithmetic.Term α) where
  min := Functions.apply₂ .and

instance : Max (peanoarithmetic.Term α) where
  max := Functions.apply₂ .or

class Imp (α : Type u) where
  imp : α → α → α

class Univ (α : Type u) where
  all : α → α

class Ex (α : Type u) where
  ex : α → α

instance : Imp (peanoarithmetic.Term α) where
  imp := Functions.apply₂ .imp

instance : Univ (peanoarithmetic.Term α) where
  all := Functions.apply₁ .all

instance : Ex (peanoarithmetic.Term α) where
  ex := Functions.apply₁ .ex

class IsVar (α : Type u) where
  var : α

class IsConst (α : Type u) where
  const : α

class IsTerm (α : Type u) where
  term : α

class IsBdform (α : Type u) where
  bdform : α

instance : IsVar (peanoarithmeticRel 1) where
  var := peanoarithmeticRel.var

instance : IsConst (peanoarithmeticRel 1) where
  const := peanoarithmeticRel.const

instance : IsTerm (peanoarithmeticRel 1) where
  term := peanoarithmeticRel.term

instance : IsBdform (peanoarithmeticRel 1) where
  bdform := peanoarithmeticRel.bdform

notation "S(" n ")" => Succ.succ n
notation n "add" m => Add.add n m
notation n "times" m => Mul.mult n m
notation n "⬝∧" m => And.and n m
notation n "⬝∨" m => Or.or n m
notation "⬝∼" n => Neg.neg n
notation n "⬝⟹" m => Imp.imp n m
notation "⬝∀" n => Univ.all n
notation "⬝∃" n => Ex.ex n

notation "Var(" x ")" => IsVar.var x
notation "Const(" c ")" => IsConst.const c
notation "Term(" t ")" => IsTerm.term t
notation "BdForm(" t ")" => IsBdform.bdform t


#check (∀' ∼(peanoarithmetic.null =' S(&0)))
