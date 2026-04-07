import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax
import FormalizingTheConsistencyOfSyntaxTheory.BasicSemantics


open FirstOrder
open Language
open peanoarithmetic
open BoundedFormula
open TermEncoding
open TermDecoding
open SyntaxStructure
open Languages


namespace PeanoArithmetic
variable {α : Type*}

/-- Peano arithemtic -/
-- inductive peano_axioms : ℒ.Theory where
--   | first : peano_axioms (∀' (Nat(null) ∧' Nat(&0) ⟹ ∼(null =' S(&0))))
--   | second :peano_axioms (∀' ∀' (Nat(&0) ∧' Nat(&1) ⟹ (S(&1) =' S(&0)) ⟹ (&1 =' &0)))
--   | third : peano_axioms (∀' (Nat(null) ∧' Nat(&0) ⟹ (&0 add null) =' &0))
--   | fourth : peano_axioms (∀' ∀' (Nat(&1) ∧' Nat(&0) ⟹ (&1 add S(&0)) =' S(&1 add &0)))
--   | fifth : peano_axioms (∀' (Nat(null) ∧' Nat(&0) ⟹ ((&0 times null) =' null)))
--   | sixth : peano_axioms (∀' ∀' (Nat(&1) ∧' Nat(&0) ⟹ ((&1 times S(&0)) =' ((&1 times &0)) add &1)))

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

-- lemma realize_numeral_eq_self (n : ℕ) (r : ℕ → ℕ) :
--   Term.realize r (numeral n) = n := by
--   induction n with
--   | zero =>
--     rfl
--   | succ n ih =>
--     simp [numeral]
--     rw [ih]
--     rfl

end PeanoArithmetic

-- conditional intro
-- look into lemma's that use Realize
-- look into how the Realize function works
-- think about what lemma's would be useful to have
-- look at how the model structure works

namespace SyntaxTheory

-- Formation Rules
def ax_bound_var : Sentence ℒ :=
  ∀' (Nat(&0) ⇔ Var(&ₛ(&0)))

-- def ax_var_term : Sentence ℒ :=
--   ∀' ∀' ((Nat(&0) ⟹ Var(&ₛ(&0)) ⟹ ∀' ((Nat(&1) ⟹ (&0 ≥ &1)) ⟹ Term(&0, &1))))

def ax_null_term : Sentence ℒ := Term(0, nullₛ)

def ax_eq_form : Sentence ℒ :=
  ∀' ∀' ((Term(&0, &0) ∧' Term(&0, &1)) ⟹ Term(&0, &0 ⬝= &1))

def ax_succ_term : Sentence ℒ :=
  ∀' (Term(&0, &0) ⟹ Term(Sₛ(&0), &0))

-- Addition preserves termhood and same context
def ax_add_term : Sentence ℒ :=
  ∀' ∀' ((Term(&0, &0) ∧' Term(&0, &1)) ⟹ Term(&0 +ₛ &1, &0))

-- Multiplication preserves termhood and same context
def ax_mult_term : Sentence ℒ :=
  ∀' ∀' ((Term(&0, &0) ∧' Term(&0, &1)) ⟹ Term(&0 timesₛ &1, &0))

-- Logical Connectives
def ax_neg_form : Sentence ℒ :=
  ∀' ∀' (BdForm(&0, &1) ⟹ BdForm(&0, ⬝∼ &1))

def ax_and_form : Sentence ℒ :=
  ∀' ∀' ∀' ((BdForm(&0, &1) ∧' BdForm(&0, &2)) ⟹ BdForm(&0, &1 ⬝∧ &2))

def ax_or_form : Sentence ℒ :=
  ∀' ∀' ∀' ((BdForm(&0, &1) ∧' BdForm(&0, &2)) ⟹ BdForm(&0, &1 ⬝∨ &2))

def ax_imp_form : Sentence ℒ :=
  ∀' ∀' ∀' ((BdForm(&0, &1) ∧' BdForm(&0, &2)) ⟹ BdForm(&0, &1 ⬝⟹ &2))

-- def ax_all_form : Sentence ℒ :=
--   ∀' ∀' (BdForm(&0 + 1, &1) ⟹ BdForm(&0, ⬝∀ &1))

def ax_all_form : Sentence ℒ :=
  ∀' ∀' (BdForm(Sₛ(&0), &1) ⟹  BdForm(&0, ⬝∀ &1))

-- def ax_ex_form : Sentence ℒ :=
--   ∀' ∀' (BdForm(&0 + 1, &1) ⟹ BdForm(&0, ⬝∃ &1))

def ax_ex_form : Sentence ℒ :=
  ∀' ∀' (BdForm(Sₛ(&0), &1) ⟹ BdForm(&0, ⬝∃ &1))

-- Injectivity
def ax_succ_inj : Sentence ℒ :=
  ∀' ∀' (Sₛ(&0) =' Sₛ(&1) ⟹ (&0 =' &1))

def ax_add_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ((&0 +ₛ &1) =' (&2 +ₛ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_mult_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ((&0 timesₛ &1) =' (&2 timesₛ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_neg_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∼ &0) =' (⬝∼ &1) ⟹ (&0 =' &1))

def ax_and_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ((&0 ⬝∧ &1) =' (&2 ⬝∧ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_or_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ((&0 ⬝∨ &1) =' (&2 ⬝∨ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_imp_inj : Sentence ℒ :=
  ∀' ∀' ∀' ∀' ((&0 ⬝⟹ &1) =' (&2 ⬝⟹ &3) ⟹ ((&0 =' &2) ∧' (&1 =' &3)))

def ax_all_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∀ &0) =' (⬝∀ &1) ⟹ (&0 =' &1))

def ax_ex_inj : Sentence ℒ :=
  ∀' ∀' ((⬝∃ &0) =' (⬝∃ &1) ⟹ (&0 =' &1))

--Distinctness
-- def ax_neg_ne_and : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝∧ &2))

-- def ax_neg_ne_or : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝∨ &2))

-- def ax_neg_ne_imp : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((⬝∼&0) =' (&1 ⬝⟹ &2))

-- def ax_neg_ne_all : Sentence ℒ :=
--   ∀' ∀' ∼((⬝∼&0) =' (⬝∀ &1))

-- def ax_neg_ne_ex : Sentence ℒ :=
--   ∀' ∀' ∼((⬝∼&0) =' (⬝∃ &1))

-- def ax_and_ne_or : Sentence ℒ :=
--   ∀' ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (&2 ⬝∨ &3))

-- def ax_and_ne_imp : Sentence ℒ :=
--   ∀' ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (&2 ⬝⟹ &3))

-- def ax_and_ne_all : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (⬝∀ &2))

-- def ax_and_ne_ex : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝∧ &1) =' (⬝∃ &2))

-- def ax_or_ne_imp : Sentence ℒ :=
--   ∀' ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (&2 ⬝⟹ &3))

-- def ax_or_ne_all : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (⬝∀ &2))

-- def ax_or_ne_ex : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝∨ &1) =' (⬝∃ &2))

-- def ax_imp_ne_all : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝⟹ &1) =' (⬝∀ &2))

-- def ax_imp_ne_ex : Sentence ℒ :=
--   ∀' ∀' ∀' ∼((&0 ⬝⟹ &1) =' (⬝∃ &2))

-- def ax_all_ne_ex : Sentence ℒ :=
--   ∀' ∀' ∼((⬝∀&0) =' (⬝∃ &1))

-- lemma listDecode_listEncode :
--   ∀ t : Term ℒ (ℕ ⊕ Fin 0),
--   Term.listDecode t.listEncode = [t] := by
--   apply Encodable.encodek
--   intro t
--   induction t
--   case var =>
--     simp [Term.listEncode, Term.listDecode]
--   case func =>
--     unfold Term.listDecode Term.listEncode
--     apply Encodable.encodek
--     simp [List.flatMap, List.finRange]
--     apply Encodable.encodek

inductive syntax_axioms : ℒ.Theory
  | bound_var     : syntax_axioms ax_bound_var
  -- | var_term      : syntax_axioms ax_var_term
  | null_term     : syntax_axioms ax_null_term
  | eq_form       : syntax_axioms ax_eq_form

  | succ_term     : syntax_axioms ax_succ_term
  | add_term      : syntax_axioms ax_add_term
  | mult_term     : syntax_axioms ax_mult_term

  | neg_form      : syntax_axioms ax_neg_form
  | and_form      : syntax_axioms ax_and_form
  | or_form       : syntax_axioms ax_or_form
  | imp_form      : syntax_axioms ax_imp_form
  | all_form      : syntax_axioms ax_all_form
  | ex_form       : syntax_axioms ax_ex_form

  | succ_inj      : syntax_axioms ax_succ_inj
  | add_inj       : syntax_axioms ax_add_inj
  | mult_inj      : syntax_axioms ax_mult_inj
  | neg_inj       : syntax_axioms ax_neg_inj
  | and_inj       : syntax_axioms ax_and_inj
  | or_inj        : syntax_axioms ax_or_inj
  | imp_inj       : syntax_axioms ax_imp_inj
  | all_inj       : syntax_axioms ax_all_inj
  | ex_inj        : syntax_axioms ax_ex_inj

  -- | neg_ne_and    : syntax_axioms ax_neg_ne_and
  -- | neg_ne_or     : syntax_axioms ax_neg_ne_or
  -- | neg_ne_imp    : syntax_axioms ax_neg_ne_imp
  -- | neg_ne_all    : syntax_axioms ax_neg_ne_all
  -- | neg_ne_ex     : syntax_axioms ax_neg_ne_ex
  -- | and_ne_or     : syntax_axioms ax_and_ne_or
  -- | and_ne_imp    : syntax_axioms ax_and_ne_imp
  -- | and_ne_all    : syntax_axioms ax_and_ne_all
  -- | and_ne_ex     : syntax_axioms ax_and_ne_ex
  -- | or_ne_imp     : syntax_axioms ax_or_ne_imp
  -- | or_ne_all     : syntax_axioms ax_or_ne_all
  -- | or_ne_ex      : syntax_axioms ax_or_ne_ex
  -- | imp_ne_all    : syntax_axioms ax_imp_ne_all
  -- | imp_ne_ex     : syntax_axioms ax_imp_ne_ex
  -- | all_ne_ex     : syntax_axioms ax_all_ne_ex

end SyntaxTheory

namespace Substitution

variable {L : Language}

@[simp]
def liftTerm {α : Type} {n : ℕ} : Term L (α ⊕ Fin n) → Term L (α ⊕ Fin (n + 1))
  | Term.var v =>
    match v with
    | Sum.inl a => Term.var (Sum.inl a)
    | Sum.inr i => Term.var (Sum.inr (Fin.succ i))
  | Term.func f ts => Term.func f (fun i => liftTerm (ts i))

@[simp]
def liftFormula {α : Type} {n : ℕ} : BoundedFormula L α n → BoundedFormula L α (n + 1)
  | .falsum => .falsum
  | .equal t1 t2 => .equal (liftTerm t1) (liftTerm t2)
  | .rel R ts => .rel R (fun i => liftTerm (ts i))
  | .imp φ ψ => .imp (liftFormula φ) (liftFormula ψ)
  | .all φ => .all (liftFormula φ)

@[simp]
def term_substitution {α : Type} {n : ℕ} (t : Term L (α ⊕ Fin n)) : Term L (Fin 1 ⊕ Fin n) → Term L (α ⊕ Fin n)
  | Term.var (Sum.inl ⟨0,_⟩) => t
  | Term.var (Sum.inr i) => Term.var (Sum.inr i)
  | Term.func f ts => Term.func f (fun i => term_substitution t (ts i))

@[simp]
def formula_substitution {α : Type} {n : ℕ} (t : Term L (α ⊕ Fin n)) : BoundedFormula L (Fin 1) n → BoundedFormula L α n
  | .falsum => .falsum
  | .equal t1 t2 => .equal (term_substitution t t1) (term_substitution t t2)
  | .rel R ts => .rel R (fun i => term_substitution t (ts i))
  | .imp φ ψ => .imp (formula_substitution t φ) (formula_substitution t ψ)
  | .all φ => .all (formula_substitution (liftTerm t) φ)

@[simp]
def bv_term_substitution {α : Type} {n : ℕ} (t : Term L (α ⊕ Fin (n + 1))) : Term L (Fin 1 ⊕ Fin n) → Term L (α ⊕ Fin (n + 1))
  | Term.var v =>
    match v with
    | Sum.inl ⟨0,_⟩ => t
    | Sum.inr i => liftTerm (Term.var (Sum.inr i))
  | Term.func f ts => Term.func f (fun i => term_substitution t (liftTerm (ts i)))

@[simp]
def bv_formula_substitution {α : Type} {n : ℕ} (t : Term L (α ⊕ Fin (n + 1))) : BoundedFormula L (Fin 1) n → BoundedFormula L α (n + 1)
  | .falsum => .falsum
  | .equal t1 t2 => .equal (bv_term_substitution t t1) (bv_term_substitution t t2)
  | .rel R ts => .rel R (fun i => bv_term_substitution t (ts i))
  | .imp φ ψ => .imp (bv_formula_substitution t φ) (bv_formula_substitution t ψ)
  | .all φ => .all (bv_formula_substitution (liftTerm t) φ)

end Substitution

namespace Induction

open Substitution
open Term
open BoundedFormula

def induction_axiom_PA (φ : BoundedFormula ℒ (Fin 1) 0) : Sentence ℒ :=
  (formula_substitution null φ ∧'
    ∀' (bv_formula_substitution (&0) φ ⟹
       bv_formula_substitution (S(&0)) φ)) ⟹
  ∀' (bv_formula_substitution (&0) φ)

def induction_axiom_syntax_carlo (φ : BoundedFormula ℒ (Fin 1) 0) : Sentence ℒ :=
  (formula_substitution nullₛ φ ∧'
    ∀' (bv_formula_substitution (&0) φ ⟹
        bv_formula_substitution (Sₛ(&0)) φ)) ⟹
  ∀' (bv_formula_substitution (&0) φ)

def induction_axiom_syntax_term (φ : BoundedFormula ℒ (Fin 1) 0) : Sentence ℒ :=
  (formula_substitution nullₛ φ ∧'
    (∀'(bv_formula_substitution (&0) φ ⟹ bv_formula_substitution (Sₛ(&0)) φ)) ∧'
      (∀'(bv_formula_substitution (&0) φ) ∧' (∀'(bv_formula_substitution (&0) (liftFormula φ)) ⟹ (bv_formula_substitution ((&1) +ₛ (&0)) φ))) ∧'
        (∀'(bv_formula_substitution (&0) φ) ∧' (∀'(bv_formula_substitution (&0) (liftFormula φ)) ⟹ (bv_formula_substitution ((&1) timesₛ(&0)) φ))) ⟹
           (∀'(bv_formula_substitution (&0) φ))
  )

def induction_axiom_syntax_formula (φ : BoundedFormula ℒ (Fin 1) 0) : Sentence ℒ :=
  (formula_substitution nullₛ φ ∧'
    (∀'(bv_formula_substitution (&0) φ ⟹ bv_formula_substitution (⬝∼ &0) φ)) ∧'
      (∀'(bv_formula_substitution (&0) φ) ∧' (∀'(bv_formula_substitution (&0) (liftFormula φ)) ⟹ (bv_formula_substitution ((&1) ⬝∧ (&0)) φ))) ∧'
        (∀'(bv_formula_substitution (&0) φ) ∧' (∀'(bv_formula_substitution (&0) (liftFormula φ)) ⟹ (bv_formula_substitution ((&1) ⬝∨ (&0)) φ))) ∧'
          (∀'(bv_formula_substitution (&0) φ) ∧' (∀'(bv_formula_substitution (&0) (liftFormula φ)) ⟹ (bv_formula_substitution ((&5) ⬝⟹ (&0)) φ))) ∧'
            (∀'(bv_formula_substitution (&0) φ ⟹ bv_formula_substitution (⬝∀ &0) φ)) ∧'
              (∀'(bv_formula_substitution (&0) φ ⟹ bv_formula_substitution (⬝∃ &0) φ)) ⟹
                (∀'(bv_formula_substitution (&0) φ))
  )

end Induction


open Induction
open Substitution
open SyntaxTheory
open PeanoArithmetic

def induction_schema : ℒ.Theory :=
  { ψ | ∃ φ : BoundedFormula ℒ (Fin 1) 0, ψ = induction_axiom_PA φ }

def peano_arithmetic : ℒ.Theory :=
  peano_axioms ∪ induction_schema

def induction_schema_syntax_term : ℒ.Theory :=
  { ψ | ∃ φ : BoundedFormula ℒ (Fin 1) 0, ψ = induction_axiom_syntax_term φ}

def induction_schema_syntax_formula : ℒ.Theory :=
  { ψ | ∃ φ : BoundedFormula ℒ (Fin 1) 0, ψ = induction_axiom_syntax_formula φ}

def syntax_theory : ℒ.Theory :=
  syntax_axioms ∪ induction_schema_syntax_term ∪ induction_schema_syntax_formula
