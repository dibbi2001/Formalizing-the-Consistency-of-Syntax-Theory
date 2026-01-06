import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax
import FormalizingTheConsistencyOfSyntaxTheory.BasicSemantics


open FirstOrder
open Language
open peanoarithmetic
open BoundedFormula
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

lemma realize_zero_eq_zero (r : Fin 0 → ℕ) :
  BoundedFormula.Realize (BoundedFormula.equal null null) (fun x => x) r := by
  rfl

lemma realize_eq_self (t : Term ℒ (ℕ ⊕ Fin 0)) (r : Fin 0 → ℕ) :
  BoundedFormula.Realize (BoundedFormula.equal t t) (fun x => x) r := by
  rfl

lemma realize_boundedFormula_and (φ ψ : BoundedFormula ℒ ℕ 0) (r : Fin 0 → ℕ) :
  BoundedFormula.Realize (φ ∧' ψ) (fun x => x) r := by
  simp [BoundedFormula.land, BoundedFormula.Realize]
  apply And.intro
  sorry
  sorry

lemma realize_numeral_eq_self (n : ℕ) (r : ℕ → ℕ) :
  Term.realize r (numeral n) = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [numeral]
    rw [ih]
    rfl

namespace SyntaxTheory
-- Formation Rules
def ax_var_term : Sentence ℒ :=
  ∀' (Var(&0) ⟹ Term(&0))

def ax_const_term : Sentence ℒ :=
  ∀' (Const(&0) ⟹ Term(&0))

-- def ax_eq_form : Sentence ℒ :=
--   ∀' ∀' ((Term(&0) ∧' Term(&1)) ⟹ BdForm(&0 =' &1))

-- Arithmetic Operations
def ax_succ_term : Sentence ℒ :=
  ∀' (Term(&0) ⟹ Term(S(&0)))

def ax_add_term : Sentence ℒ :=
  ∀' ∀' (Term(&0) ∧' Term(&1) ⟹ Term(&0 addₛ &1))

def ax_mult_term : Sentence ℒ :=
  ∀' ∀' (Term(&0) ∧' Term(&1) ⟹ Term(&0 timesₛ &1))

-- Logical Connectives
def ax_neg_form : Sentence ℒ :=
  ∀' (BdForm(&0) ⟹ BdForm(⬝∼ &0))

def ax_and_form : Sentence ℒ :=
  ∀' ∀' (BdForm(&0) ∧' BdForm(&1) ⟹ BdForm(&0 ⬝∧ &1))

def ax_or_form : Sentence ℒ :=
  ∀' ∀' (BdForm(&0) ∨' BdForm(&1) ⟹ BdForm(&0 ⬝∨ &1))

def ax_imp_form : Sentence ℒ :=
  ∀' ∀' (BdForm(&0) ⟹ BdForm(&1) ⟹ BdForm(&0 ⬝⟹ &1))

def ax_all_form : Sentence ℒ :=
  ∀' (BdForm(&0) ⟹ BdForm(⬝∀ &0))

def ax_ex_form : Sentence ℒ :=
  ∀' (BdForm(&0) ⟹ BdForm(⬝∃ &0))

-- Injectivity
def ax_succ_inj : Sentence ℒ :=
  ∀' ∀' (S(&0) =' S(&1) ⟹ (&0 =' &1))

def ax_add_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀'((&0 addₛ &1) =' (&2 addₛ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_mult_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀'((&0 timesₛ &1) =' (&2 timesₛ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_neg_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∼ &0) =' (⬝∼ &1) ⟹ &0 ='&1)

def ax_and_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀'((&0 ⬝∧ &1) =' (&2 ⬝∧ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_or_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀'((&0 ⬝∨ &1) =' (&2 ⬝∨ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_imp_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀'((&0 ⬝⟹ &1) =' (&2 ⬝⟹ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_all_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∀ &0) =' (⬝∀ &1) ⟹ &0 ='&1)

def ax_ex_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∃ &0) =' (⬝∃ &1) ⟹ &0 ='&1)

--Distinctness
def ax_neg_ne_and : Sentence ℒ :=
  ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝∧ &2))

def ax_neg_ne_or : Sentence ℒ :=
  ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝∨ &2))

def ax_neg_ne_imp : Sentence ℒ :=
  ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝⟹ &2))

def ax_neg_ne_all : Sentence ℒ :=
  ∀' ∀' ∼((⬝∼&0) =' (⬝∀ &1))

def ax_neg_ne_ex : Sentence ℒ :=
  ∀' ∀' ∼((⬝∼&0) =' (⬝∃ &1))

def ax_and_ne_or : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (&2 ⬝∨ &3))

def ax_and_ne_imp : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (&2 ⬝⟹ &3))

def ax_and_ne_all : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (⬝∀ &2))

def ax_and_ne_ex : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (⬝∃ &2))

def ax_or_ne_imp : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (&2 ⬝⟹ &3))

def ax_or_ne_all : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (⬝∀ &2))

def ax_or_ne_ex : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (⬝∃ &2))

def ax_imp_ne_all : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝⟹ &1) =' (⬝∀ &2))

def ax_imp_ne_ex : Sentence ℒ :=
  ∀' ∀' ∀' ∼((&0 ⬝⟹ &1) =' (⬝∃ &2))

def ax_all_ne_ex : Sentence ℒ :=
  ∀' ∀' ∼((⬝∀&0) =' (⬝∃ &1))

end SyntaxTheory
