import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax
import FormalizingTheConsistencyOfSyntaxTheory.BasicSemantics

open FirstOrder
open Language
open peanoarithmetic
open TermEncoding
open TermDecoding
open NatCoding

variable {α : Type*}

/-- Peano arithemtic -/
inductive peano_axioms : ℒ.Theory where
  | first : peano_axioms (∀' ∼(null =' S(&0)))
  | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : peano_axioms (∀' ((&0 add null) =' &0))
  | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : peano_axioms (∀' ((&0 times null) =' null))
  | sixth : peano_axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))

/-- all Peano axioms hold in `nat_structure` (ℕ). -/
theorem peano_axioms_hold (r : Empty → ℕ) :
  ∀ {φ}, peano_axioms φ → BoundedFormula.Realize (L := peanoarithmetic) φ r ![] := by
  intro φ h
  cases h
  case first =>
    intro x
    exact Nat.zero_ne_add_one x
  case second =>
    intro x y hxy
    exact Nat.succ_injective hxy
  case third =>
    intro x
    exact Nat.add_zero x
  case fourth =>
    intro x y
    exact Nat.add_succ y x
  case fifth =>
    intro x
    exact Nat.mul_zero x
  case sixth =>
    intro x y
    exact Nat.mul_succ y x

def realize_zero_eq_zero (r : Fin 0 → ℕ) :
  BoundedFormula.Realize (BoundedFormula.equal null null) (fun x => x) r := by
  rfl

def realize_eq_self (t : Term ℒ (ℕ ⊕ Fin 0)) (r : Fin 0 → ℕ) :
  BoundedFormula.Realize (BoundedFormula.equal t t) (fun x => x) r := by
  rfl

def realize_numeral_eq_self (n : ℕ) (r : ℕ → ℕ) :
  Term.realize r (numeral n) = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [numeral]
    rw [ih]
    rfl
