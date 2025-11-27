import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax

open FirstOrder
open Language
open peanoarithmetic


variable {α : Type*} {n : ℕ} {M : Type*} {v : α → M}
universe u

namespace Structure

variable (neg_repres : (Fin 1 → M) → M) (and_repres : (Fin 2 → M) → M) (or_repres : (Fin 2 → M) → M)
(var_prop : (Fin 1 → M) → Prop) (const_prop : (Fin 1 → M) → Prop) (term_prop : (Fin 1 → M) → Prop) (bdform_prop : (Fin 1 → M) → Prop)

class NegDot (α : Type u) where
  negdot : α → α

class MinDot (α : Type u) where
  mindot : α → α → α

class MaxDot (α : Type u) where
  maxdot : α → α → α

instance : NegDot M  where
  negdot α := neg_repres ![α]

instance : MinDot M where
  mindot α β := and_repres ![α, β]

instance: MaxDot M where
  maxdot α β := or_repres ![α, β]

class IsVarDot (α : Type u) where
  vardot : (Fin 1 → α) → Prop

class IsConstDot (α : Type u) where
  constdot : (Fin 1 → α) → Prop

class IsTermDot (α : Type u) where
  termdot : (Fin 1 → α) → Prop

class IsBdformDot (α : Type u) where
  bdformdot : (Fin 1 → α) → Prop

instance : IsVarDot M where
  vardot := var_prop

instance : IsConstDot M where
  constdot := const_prop

instance : IsTermDot M where
  termdot := term_prop

instance : IsBdformDot M where
  bdformdot := bdform_prop

variable [Zero M] [Succ M] [Add M] [Mul M]
[NegDot M] [MinDot M] [MaxDot M]
[Imp M] [Univ M] [Ex M]
[IsVarDot M] [IsConstDot M] [IsTermDot M] [IsBdformDot M]

instance : peanoarithmetic.Structure M where
  funMap
  | .zero, _  => 0
  | .succ, v => Succ.succ (v 0)
  | .add, v => (v 0) + (v 1)
  | .mult, v => (v 0 ) * (v 1)
  | .neg, v => NegDot.negdot (v 0)
  | .and, v => MinDot.mindot (v 0) (v 1)
  | .or, v => MaxDot.maxdot (v 0) (v 1)
  | .imp, v => Imp.imp (v 0) (v 1)
  | .all, v => Univ.all (v 0)
  | .ex, v => Ex.ex (v 0)
  RelMap
  | .var, v => IsVarDot.vardot v
  | .const, v => IsConstDot.constdot v
  | .term, v => IsTermDot.termdot v
  | .bdform, v => IsBdformDot.bdformdot v


section
@[simp] theorem funMap_zero {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.zero v = 0 := rfl

@[simp] theorem funMap_succ {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.succ v = Succ.succ (v 0) := rfl
@[simp] theorem funMap_add {v} :
Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_mult {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.mult v = v 0 * v 1 := rfl

@[simp] theorem funMap_neg {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.neg v = NegDot.negdot (v 0) := rfl

@[simp] theorem funMap_and {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.and v = MinDot.mindot (v 0) (v 1) := rfl

@[simp] theorem funMap_or {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.or v = MaxDot.maxdot (v 0) (v 1) := rfl

@[simp] theorem funMap_imp {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.imp v = Imp.imp (v 0) (v 1) := rfl

@[simp] theorem funMap_all {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.all v = Univ.all (v 0) := rfl

@[simp] theorem funMap_ex {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.ex v = Ex.ex (v 0) := rfl


@[simp] theorem realize_null : Term.realize v (Language.peanoarithmetic.null : peanoarithmetic.Term α) = 0 := rfl

@[simp] theorem realize_succ (t : peanoarithmetic.Term α) :
  Term.realize v (Succ.succ t) = Succ.succ (Term.realize v t) := rfl

@[simp] theorem realize_add (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

@[simp] theorem realize_mult (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (t₁ * t₂) = Term.realize v t₁ * Term.realize v t₂ := rfl

@[simp] theorem realize_neg (t : peanoarithmetic.Term α) :
  Term.realize v (Neg.neg t) = NegDot.negdot (Term.realize v t) := rfl

@[simp] theorem realize_and (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (Min.min t₁ t₂) = MinDot.mindot (Term.realize v t₁) (Term.realize v t₂) := rfl

@[simp] theorem realize_or (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (Max.max t₁ t₂) = MaxDot.maxdot (Term.realize v t₁) (Term.realize v t₂) := rfl

@[simp] theorem realize_imp (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (Imp.imp t₁ t₂) = Imp.imp (Term.realize v t₁) (Term.realize v t₂) := rfl

@[simp] theorem realize_all (t : peanoarithmetic.Term α) :
  Term.realize v (Univ.all t) = Univ.all (Term.realize v t) := rfl

@[simp] theorem realize_ex (t : peanoarithmetic.Term α) :
  Term.realize v (Ex.ex t) = Ex.ex (Term.realize v t) := rfl

end

namespace ModelN
  def nat_structure : peanoarithmetic.Structure ℕ where
    funMap
    | .zero, _  => 0
    | .succ, v  => Nat.succ (v 0)
    | .add, v   => v 0 + v 1
    | .mult, v  => v 0 * v 1
    | .neg, v   => v 0
    | .and, v   => 0
    | .or, v    => 0
    | .imp, v   => 0
    | .all, v   => 0
    | .ex, v    => 0

    RelMap
    | .var, _    => False
    | .const, _  => False
    | .term, _   => False
    | .bdform, _ => False

  instance : peanoarithmetic.Structure ℕ := nat_structure

  def r : ℕ → ℕ := fun x => x

  def first_axiom : ℒ.BoundedFormula ℕ 0 :=
    (∀' ∼(null =' S(&0)))

  def p : ℕ → ℕ := id

  #eval Term.realize r (S(S(0) + S(0)) : peanoarithmetic.Term ℕ)
  #eval Term.realize r (S(S(S(0))) * S(S(S(0))) : peanoarithmetic.Term ℕ)
  #eval Term.realize r (null + null)
  #eval Term.realize r (S(null) ⬝⟹ S(null))
  #eval Term.realize r (.var 2 : peanoarithmetic.Term ℕ)
  #reduce BoundedFormula.Realize first_axiom p ![]

  #check BoundedFormula.Realize first_axiom r 0

  theorem first_axiomholds : BoundedFormula.Realize first_axiom r 0 := by
    intro n
    exact Nat.zero_ne_add_one n

end ModelN
end Structure

open TermEncoding
open TermDecoding
open BoundedFormula

variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]

namespace NatCoding
  -- /-- Negation on encoded formulas. Returns #¬φ if n encodes a formula, n otherwise. -/
  -- def neg_repres_0 (k : ℕ) {n : ℕ} : ℕ :=
  --   match formula_ofnat_general k with
  --   | some φ => formula_tonat (BoundedFormula.not φ)
  --   | none   => k

  -- def neg_repres_1 (n : ℕ) (k : List ((k : ℕ) × L.Term (ℕ ⊕ Fin 0) × L.Relations n ⊕ ℕ)) (φ : BoundedFormula L ℕ n): ℕ :=
  --   match Encodable.decodeList (BoundedFormula.listDecode k) with
  --   | some φ => formula_tonat (BoundedFormula.not φ)
  --   | none   => n

  -- def neg_repres_2 {n : ℕ} (k : ℕ) (i : Option (BoundedFormula L ℕ n)) : ℕ :=
  --   match i with
  --   | some φ => formula_tonat (BoundedFormula.not φ)
  --   | none   => k

  def neg_repres (k : ℕ) : ℕ :=
    match formula_ofnat (n := n) k with
    | some (φ : BoundedFormula L ℕ n) =>
        formula_tonat (BoundedFormula.not φ)
    | none =>
        k

  def and_repres (k₁ k₂ : ℕ) : ℕ :=
    match formula_ofnat (n := n) k₁, formula_ofnat (n := n) k₂ with
    | some (φ : BoundedFormula L ℕ n), some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat (φ ∧' ψ)
    | some (φ : BoundedFormula L ℕ n), none =>
        formula_tonat φ
    | none, some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat ψ
    | none, none =>
        Nat.min k₁ k₂

  def or_repres (k₁ k₂ : ℕ) : ℕ :=
    match formula_ofnat (n := n) k₁, formula_ofnat (n := n) k₂ with
    | some (φ : BoundedFormula L ℕ n), some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat (φ ∨' ψ)
    | some (φ : BoundedFormula L ℕ n), none =>
        formula_tonat φ
    | none, some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat ψ
    | none, none =>
        Nat.min k₁ k₂

  def imp_repres (k₁ k₂ : ℕ) : ℕ :=
    match formula_ofnat (n := n) k₁, formula_ofnat (n := n) k₂ with
    | some (φ : BoundedFormula L ℕ n), some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat (BoundedFormula.imp φ ψ)
    | some (φ : BoundedFormula L ℕ n), none =>
        formula_tonat φ
    | none, some (ψ : BoundedFormula L ℕ n) =>
        formula_tonat ψ
    | none, none =>
        Nat.min k₁ k₂

  def all_repres (k : ℕ) : ℕ :=
    match (formula_ofnat (n := n + 1) k : Option (BoundedFormula L ℕ (n + 1))) with
    | some (φ : BoundedFormula L ℕ (n + 1)) => formula_tonat (BoundedFormula.all φ)
    | none => k

  def ex_repres (k : ℕ) : ℕ :=
    match (formula_ofnat (n := n + 1) k : Option (BoundedFormula L ℕ (n + 1))) with
    | some (φ : BoundedFormula L ℕ (n + 1)) => formula_tonat (BoundedFormula.ex φ)
    | none => k

  def φ : BoundedFormula ℒ ℕ 0 := BoundedFormula.equal (null) (null)
  def ψ : BoundedFormula ℒ Empty 0 := (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  def t : Term ℒ (ℕ ⊕ Fin 0) := S(S(null))
  def s : Term ℒ (Empty ⊕ Fin 0) := null

  #eval formula_tonat φ
  #eval term_tonat (L := ℒ) t
  #eval sentence_term_tonat s
  #eval sent_tonat ψ

  -- #eval (⌜ φ ⌝)

  #eval formula_ofnat (L := ℒ) (n := 1) (formula_tonat (L := ℒ) φ)
  #eval formula_ofnat (L := ℒ) (n := 1) (13442315822)

  #eval term_ofnat (L := ℒ) (term_tonat t)
  -- #eval sentence_term_ofnat (L := ℒ) (sentence_term_tonat (L := ℒ) s) --add tostr fun for closed terms?

  -- #eval sent_ofnat (L := ℒ) (sent_tonat (L := ℒ) ψ) --add tostr fun for sentences??

end NatCoding
