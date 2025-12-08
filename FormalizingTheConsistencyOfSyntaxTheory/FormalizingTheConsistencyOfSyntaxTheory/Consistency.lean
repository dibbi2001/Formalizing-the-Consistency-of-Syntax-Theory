import FormalizingTheConsistencyOfSyntaxTheory.BasicTheories
import Mathlib.ModelTheory.Satisfiability

open FirstOrder
open Language
open peanoarithmetic
open BoundedFormula
open Classical

namespace Consistency

abbrev semantically_consistent (T : Theory ℒ) : Prop :=
  T.IsSatisfiable

def implies (T : Theory ℒ) (φ : Sentence ℒ) :  Prop :=
  ¬ (T ∪ {φ.not}).IsSatisfiable

lemma inconsistent (r : Fin 0 → ℕ):
¬ BoundedFormula.Realize ((BoundedFormula.equal null null) ∧' (BoundedFormula.not (BoundedFormula.equal null null))) (fun x => x) r := by
  simp [BoundedFormula.land, BoundedFormula.not]

theorem nat_models_peano_axioms :
  ℕ ⊨ (peano_axioms : ℒ.Theory) := by
  sorry

theorem peano_axioms_satisfiable : (peano_axioms : Theory peanoarithmetic).IsSatisfiable := by
  sorry

end Consistency
