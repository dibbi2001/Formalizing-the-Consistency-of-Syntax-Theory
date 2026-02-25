import FormalizingTheConsistencyOfSyntaxTheory.BasicTheories
import Mathlib.ModelTheory.Satisfiability

open FirstOrder
open Language
open peanoarithmetic
open BoundedFormula
open Classical
open PeanoArithmetic
open SyntaxTheory
open Structure
open PAStructure
open SyntaxStructure

namespace Consistency

variable {M : Type*}

abbrev semantically_consistent (T : Theory ℒ) : Prop :=
  T.IsSatisfiable

def implies (T : Theory ℒ) (φ : Sentence ℒ) :  Prop :=
  ¬ (T ∪ {φ.not}).IsSatisfiable

lemma inconsistent (r : Fin 0 → ℕ):
¬ BoundedFormula.Realize ((BoundedFormula.equal null null) ∧' (BoundedFormula.not (BoundedFormula.equal null null))) (fun x => x) r := by
  simp [BoundedFormula.land, BoundedFormula.not]

theorem nat_models_peano_axioms : ℕ ⊨ peano_axioms := by
  simp
  intro φ hφ
  cases hφ
  case first =>
    simp
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

def standardModel : peano_axioms.ModelType :=
{
  Carrier := ℕ,
  struc := nat_structure,
  is_model := nat_models_peano_axioms,
  nonempty' := ⟨0⟩
}

theorem peano_axioms_satisfiable : (peano_axioms : Theory peanoarithmetic).IsSatisfiable := by
  refine ⟨standardModel⟩

theorem nat_models_syntax_axioms : ℕ ⊨ syntax_axioms := by
  simp
  intro φ hφ
  cases hφ
  case var_term =>
    intro x
    aesop
  case const_term =>
    intro x
    aesop
  case eq_form =>
    intro x
    aesop
  case succ_term =>
    intro x
    aesop
  case add_term =>
    sorry
  case mult_term =>
    sorry
  case neg_form =>
    intro x
    aesop
  case and_form =>
    sorry
  case or_form =>
    sorry
  case imp_form =>
    sorry
  case all_form =>
    intro x
    aesop
  case ex_form =>
    intro x
    aesop
  case succ_inj =>
    sorry
  case add_inj =>
    sorry
  case mult_inj =>
    sorry
  case neg_inj =>
    sorry
  case and_inj =>
    sorry
  case or_inj =>
    sorry
  case imp_inj =>
    sorry
  case all_inj =>
    sorry
  case ex_inj =>
    sorry
  case neg_ne_and =>
    sorry
  case neg_ne_or =>
    sorry
  case neg_ne_imp =>
    sorry
  case neg_ne_all =>
    sorry
  case neg_ne_ex =>
    sorry
  case and_ne_or =>
    sorry
  case and_ne_imp =>
    sorry
  case and_ne_all =>
    sorry
  case and_ne_ex =>
    sorry
  case or_ne_imp =>
    sorry
  case or_ne_all =>
    sorry
  case or_ne_ex =>
    sorry
  case imp_ne_all =>
    sorry
  case imp_ne_ex =>
    sorry
  case all_ne_ex =>
    sorry


-- def syntaxModel : syntax_axioms.ModelType :=
-- {
--   Carrier := ℕ,
--   struc := nat_syntax_structure
--   is_model := nat_models_syntax_axioms
--   nonempty' := ⟨0⟩
-- }

theorem syntax_axioms_satisfiable : (syntax_axioms : ℒ.Theory).IsSatisfiable := by
  sorry

end Consistency
