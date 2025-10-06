import FormalizingTheConsistencyOfSyntaxTheory.Syntax

open FirstOrder
open Language
open peanoarithmetic

/-- Peano arithemtic -/
inductive peano_axioms : ℒ.Theory where
  | first : peano_axioms (∀' ∼(peanoarithmetic.null =' S(&0)))
  | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : peano_axioms (∀' ((&0 add peanoarithmetic.null) =' &0))
  | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : peano_axioms (∀' ((&0 times peanoarithmetic.null) =' peanoarithmetic.null))
  | sixth : peano_axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
