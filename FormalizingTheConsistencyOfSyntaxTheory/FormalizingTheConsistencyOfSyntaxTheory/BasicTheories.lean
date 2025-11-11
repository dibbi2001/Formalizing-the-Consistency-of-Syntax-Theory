import FormalizingTheConsistencyOfSyntaxTheory.Syntax

open FirstOrder
open Language
open peanoarithmetic
open Structure

variable {α : Type*}

/-- Peano arithemtic -/

inductive peano_axioms : ℒ.Theory where
  | first : peano_axioms (∀' ∼(null =' S(&0)))
  | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : peano_axioms (∀' ((&0 add null) =' &0))
  | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : peano_axioms (∀' ((&0 times null) =' null))
  | sixth : peano_axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))

def r : ℕ → ℕ := fun x => x

/-- all Peano axioms hold in `nat_structure` (ℕ). -/
theorem peano_axioms_hold (r : Empty → ℕ) :
  ∀ {φ}, peano_axioms φ → BoundedFormula.Realize (L := peanoarithmetic) φ r ![] := by
  intro φ h
  cases h
  case first =>
    intro n
    simp [BoundedFormula.Realize]
  case second =>
    intro n
    simp [BoundedFormula.Realize]
    sorry
  case third =>
    intro x
    simp [Term.realize]
    sorry
  case fourth =>
    sorry
  case fifth =>
    sorry
  case sixth =>
    sorry
