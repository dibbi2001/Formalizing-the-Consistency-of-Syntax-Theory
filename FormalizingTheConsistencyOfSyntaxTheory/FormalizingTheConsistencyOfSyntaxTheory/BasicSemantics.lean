import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax

open FirstOrder
open Language
open peanoarithmetic
open TermEncoding


variable {α : Type*} {n : ℕ} {M : Type*} {v : α → M}
universe u

namespace Structure

variable (neg_repres : (Fin 1 → M) → M) (and_repres : (Fin 2 → M) → M) (or_repres : (Fin 2 → M) → M)
(var_prop : (Fin 1 → M) → Prop) (const_prop : (Fin 1 → M) → Prop) (term_prop : (Fin 2 → M) → Prop) (bdform_prop : (Fin 2 → M) → Prop)
(nat_prop : (Fin 1 → M) → Prop) (le_prop : (Fin 2 → M) → Prop)

/-- A model interprets syntactic function symbols and relation symbols as actual
functions and predicates on a structure `M`. This section packages those
interpretations into typeclasses and instances, providing the semantic
counterpart of the syntactic constructors defined in the language ℒ. -/

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
  termdot : (Fin 2 → α) → Prop

class IsBdformDot (α : Type u) where
  bdformdot : (Fin 2 → α) → Prop

class IsNatDot (α : Type u) where
  natdot : (Fin 1 → α) → Prop

class IsLeDot (α : Type u) where
  ledot : (Fin 2 → α) → Prop

instance : IsVarDot M where
  vardot := var_prop

instance : IsConstDot M where
  constdot := const_prop

instance : IsTermDot M where
  termdot := term_prop

instance : IsBdformDot M where
  bdformdot := bdform_prop

instance : IsNatDot M where
  natdot := nat_prop

instance : IsLeDot M where
  ledot := le_prop

variable [Zero M] [Succ M] [Add M] [Mul M]
[NegDot M] [MinDot M] [MaxDot M]
[Imp M] [Eq M] [Univ M] [Ex M] [BoundVar M]
[IsVarDot M] [IsConstDot M] [IsTermDot M] [IsBdformDot M]
[IsNatDot M] [IsLeDot M]
[Zeroₛ M] [Succₛ M] [Addₛ M] [Mulₛ M]

/-- The semantic structure for the language of Peano arithmetic on a
domain `M`. It interprets each function symbol as an actual operation on `M`
and each relation symbol as a predicate on `M`, thereby specifying how the
syntactic language ℒ is realized inside the structure. -/
instance : peanoarithmetic.Structure M where
  funMap
  | .zero, _  => 0
  | .succ, v => Succ.succ (v 0)
  | .add, v => (v 0) + (v 1)
  | .mult, v => (v 0 ) * (v 1)
  | .zeroₛ, _ => Zeroₛ.zeroₛ
  | .succₛ, v => Succₛ.succₛ (v 0)
  | .addₛ, v => Addₛ.addₛ (v 0) (v 1)
  | .multₛ, v => Mulₛ.mulₛ (v 0) (v 1)
  | .negₛ, v => NegDot.negdot (v 0)
  | .andₛ, v => MinDot.mindot (v 0) (v 1)
  | .orₛ, v => MaxDot.maxdot (v 0) (v 1)
  | .impₛ, v => Imp.imp (v 0) (v 1)
  | .eqₛ, v =>  Eq.eq (v 0) (v 1)
  | .allₛ, v => Univ.all (v 0)
  | .exₛ, v => Ex.ex (v 0)
  | .boundₛ, v => BoundVar.bv (v 0)
  RelMap
  | .var, v => IsVarDot.vardot v
  | .const, v => IsConstDot.constdot v
  | .term, v => IsTermDot.termdot v
  | .bdform, v => IsBdformDot.bdformdot v
  | .nat, v => IsNatDot.natdot v
  | .le, v => IsLeDot.ledot v

section
-- some simp lemmas
@[simp] theorem funMap_zero {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.zero v = 0 := rfl

@[simp] theorem funMap_succ {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.succ v = Succ.succ (v 0) := rfl
@[simp] theorem funMap_add {v} :
Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_mult {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.mult v = v 0 * v 1 := rfl

@[simp] theorem funMap_neg {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.negₛ v = NegDot.negdot (v 0) := rfl

@[simp] theorem funMap_and {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.andₛ v = MinDot.mindot (v 0) (v 1) := rfl

@[simp] theorem funMap_or {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.orₛ v = MaxDot.maxdot (v 0) (v 1) := rfl

@[simp] theorem funMap_imp {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.impₛ v = Imp.imp (v 0) (v 1) := rfl

@[simp] theorem funMap_eq {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.eqₛ v = Eq.eq (v 0) (v 1) := rfl

@[simp] theorem funMap_all {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.allₛ v = Univ.all (v 0) := rfl

@[simp] theorem funMap_ex {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.exₛ v = Ex.ex (v 0) := rfl

@[simp] theorem funMap_bv {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.boundₛ v = BoundVar.bv (v 0) := rfl

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

@[simp] theorem realize_eq (t₁ t₂ : peanoarithmetic.Term α) :
  Term.realize v (Eq.eq t₁ t₂) = Eq.eq (Term.realize v t₁) (Term.realize v t₂) := rfl

@[simp] theorem realize_all (t : peanoarithmetic.Term α) :
  Term.realize v (Univ.all t) = Univ.all (Term.realize v t) := rfl

@[simp] theorem realize_ex (t : peanoarithmetic.Term α) :
  Term.realize v (Ex.ex t) = Ex.ex (Term.realize v t) := rfl

@[simp] theorem realize_bv (t : peanoarithmetic.Term α) :
  Term.realize v (BoundVar.bv t) = BoundVar.bv (Term.realize v t) := rfl

end

namespace PAStructure
/-- The standard model of Peano arithmetic on the natural numbers ℕ.
It interprets the arithmetic function symbols in the usual way on ℕ, while giving
arbitrary (but fixed) interpretations to the syntactic symbols, and assigning
constant truth values to relation symbols.

This provides a concrete structure in which the Peano language ℒ is interpreted
over the natural numbers. -/
  def nat_structure : peanoarithmetic.Structure ℕ where
    funMap
    | .zero, _  => 0
    | .succ, v  => Nat.succ (v 0)
    | .add, v   => v 0 + v 1
    | .mult, v  => v 0 * v 1
    | .zeroₛ, _  => 0   -- add meaningful interpretations for syntactic objects
    | .succₛ, v  => Nat.succ (v 0)
    | .addₛ, v   => v 0 + v 1
    | .multₛ, v  => v 0 * v 1
    | .negₛ, v   => v 0
    | .andₛ, v   => 0
    | .orₛ, v    => 0
    | .impₛ, v   => 0
    | .eqₛ, v    => 0
    | .allₛ, v   => 0
    | .exₛ, v    => 0
    | .boundₛ, v => 0

    RelMap
    | .var, _    => False
    | .const, _  => False
    | .term, _   => False
    | .bdform, _ => False
    | .nat, _    => False
    | .le, _     => False

  instance : peanoarithmetic.Structure ℕ := nat_structure

end PAStructure
end Structure

open TermEncoding
open TermDecoding
open BoundedFormula

variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]

namespace SyntaxStructure
/-- Syntactic function and relation symbols of the language ℒ.
Each function symbol is interpreted as a computable transformation on
natural numbers encoding syntax trees.
In most failure cases (non-decodable inputs), the functions default to simple
fallback values (e.g. identity or `Nat.min`) to ensure totality.
-/
  def zeroₛ_repres : ℕ :=
    TermEncoding.term_tonat (L := peanoarithmetic) (Term.func (L := peanoarithmetic) peanoarithmeticFunc.zeroₛ ![])

  def succₛ_repres (k : ℕ) : ℕ :=
    match term_ofnat k with
    | some (t : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat (Sₛ(t))
    | none =>
        k

  def addₛ_repres (k₁ k₂ : ℕ) : ℕ :=
    match term_ofnat k₁, term_ofnat k₂ with
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat (t +ₛ s)
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), none =>
        term_tonat t
    | none, some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat s
    | none, none =>
        term_tonat (Term.var (Sum.inl 0) : Term ℒ (ℕ ⊕ Fin 0))

  def multₛ_repres (k₁ k₂ : ℕ) : ℕ :=
    match term_ofnat k₁, term_ofnat k₂ with
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat (t timesₛ s)
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), none =>
        term_tonat t
    | none, some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat s
    | none, none =>
        Nat.min k₁ k₂

  def neg_repres (k : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k with
    | some φ => TermEncoding.formula_tonat (L := peanoarithmetic) (BoundedFormula.not φ)
    | none => k

  def and_repres (k₁ k₂ : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₁,
    TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₂ with
    | some φ, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) (φ ∧' ψ)
    | some φ, none => TermEncoding.formula_tonat (L := peanoarithmetic) φ
    | none, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) ψ
    | none, none => Nat.min k₁ k₂

  def or_repres (k₁ k₂ : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₁,
    TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₂ with
    | some φ, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) (φ ∨' ψ)
    | some φ, none => TermEncoding.formula_tonat (L := peanoarithmetic) φ
    | none, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) ψ
    | none, none => Nat.min k₁ k₂

  def imp_repres (k₁ k₂ : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₁,
    TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0) k₂ with
    | some φ, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) (BoundedFormula.imp φ ψ)
    | some φ, none => TermEncoding.formula_tonat (L := peanoarithmetic) φ
    | none, some ψ => TermEncoding.formula_tonat (L := peanoarithmetic) ψ
    | none, none => Nat.min k₁ k₂

  def eq_repres (k₁ k₂ : ℕ) : ℕ :=
    match term_ofnat k₁, term_ofnat k₂ with
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        formula_tonat (BoundedFormula.equal t s)
    | some (t : Term ℒ (ℕ ⊕ Fin 0)), none =>
        term_tonat t
    | none, some (s : Term ℒ (ℕ ⊕ Fin 0)) =>
        term_tonat s
    | none, none =>
        Nat.min k₁ k₂

  def all_repres (k : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0 + 1) k with
    | some φ => TermEncoding.formula_tonat (L := peanoarithmetic) (BoundedFormula.all φ)
    | none => k

  def ex_repres (k : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat (L := peanoarithmetic) (n := 0 + 1) k with
    | some φ => TermEncoding.formula_tonat (L := peanoarithmetic) (BoundedFormula.ex φ)
    | none => k

  def var_repres (k : ℕ) : ℕ :=
    match TermDecoding.term_ofnat (L := peanoarithmetic) k with
    | some (.var _) => 1
    | _             => 0

  def term_repres (k : ℕ) : ℕ :=
    match TermDecoding.term_ofnat (L := peanoarithmetic) k with
    | some _ => 1
    | none   => 0

  def const_repres (k : ℕ) : ℕ :=
    match TermDecoding.term_ofnat (L := peanoarithmetic) k with
    | some (.func peanoarithmeticFunc.zeroₛ ![]) => 1
    | _ => 0

  def bdform_repres (k : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat_general (L := peanoarithmetic) k with
    | some _ => 1
    | none   => 0

  def nat_repres (k : ℕ) : ℕ := k

/-- Syntax structure of the Peano language interpreted over ℕ.
This structure thus internalises the syntax of the language inside ℕ,
realising a form of arithmetised syntax.
-/
  def nat_syntax_structure : peanoarithmetic.Structure ℕ where
  funMap
  | .zero, _  => 0
  | .succ, v  => Nat.succ (v 0)
  | .add, v   => v 0 + v 1
  | .mult, v  => v 0 * v 1

  | .zeroₛ, _  => zeroₛ_repres
  | .succₛ, v  => succₛ_repres (v 0)
  | .addₛ, v   => addₛ_repres (v 0) (v 1)
  | .multₛ, v  => multₛ_repres (v 0) (v 1)
  | .negₛ, v   => neg_repres (v 0)
  | .andₛ, v   => and_repres (v 0) (v 1)
  | .orₛ, v    => or_repres (v 0) (v 1)
  | .impₛ, v   => imp_repres (v 0) (v 1)
  | .eqₛ, v    => eq_repres (v 0) (v 1)
  | .allₛ, v   => all_repres (v 0)
  | .exₛ, v    => ex_repres (v 0)
  | .boundₛ, v => 0

  RelMap
  | .var, v    => var_repres (v 0) = 1
  | .term, v   => term_repres (v 0) = 1
  | .const, v  => const_repres (v 0) = 1
  | .bdform, v => bdform_repres (v 0) = 1
  | .nat, v    => nat_repres (v 0) = 1
  | .le, v     => True
end SyntaxStructure

namespace Lifting
variable {L : Language}

/-- Lifting operations on terms and bounded formulas.

Lifting is used to adjust expressions when the number of bound variables increases,
ensuring that variable indices remain correct under the introduction of new binders.

- `liftTerm`:
  Raises a term from context `(α ⊕ Fin n)` to `(α ⊕ Fin (n + 1))` by shifting
  bound variables (`Fin n`) while leaving free variables unchanged.

- `liftFormula`:
  Extends lifting to bounded formulas by applying `liftTerm` pointwise to all
  term occurrences and recursively lifting through logical structure. -/

@[simp]
-- @[match_pattern]
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
end Lifting

namespace Homophonic
open Structure
open Lifting

/-- The homophonic domain, which is used as a unified domain for interpreting both numerical and syntactic
objects within a single structure. -/

abbrev SynDomain (ℒ : Language) :=
  ℕ ⊕ (Σ n : ℕ, Term ℒ (ℕ ⊕ Fin n)) ⊕ (Σ n : ℕ, BoundedFormula ℒ ℕ n)

-- some nice definitions
def isNat : SynDomain ℒ → Prop
| Sum.inl _ => True
| _ => False

def isTerm : SynDomain ℒ → Prop
| Sum.inr (Sum.inl ⟨_, _⟩) => True
| _ => False

def isBdForm : SynDomain ℒ → Prop
| Sum.inr (Sum.inr ⟨_, _⟩) => True
| _ => False

-- instances for the model
instance : IsNatDot (SynDomain ℒ) :=
  { natdot := fun v =>
      match v 0 with
      | Sum.inl _ => True
      | _ => False }

instance : IsTermDot (SynDomain ℒ) :=
{ termdot := fun v =>
    match v 0, v 1 with
    | Sum.inl n, Sum.inr (Sum.inl ⟨m, _⟩) => n = m
    | _, _ => False
}

instance : IsBdformDot (SynDomain ℒ) :=
{ bdformdot := fun v =>
    match v 0, v 1 with
    | Sum.inl n, Sum.inr (Sum.inr ⟨m, _⟩) => n = m
    | _, _ => False
}

instance : IsVarDot (SynDomain ℒ) where
  vardot v :=
    match v 0 with
    | Sum.inr (Sum.inl _) => True
    | _ => False

instance : IsConstDot (SynDomain ℒ) where
  constdot v :=
    match v 0 with
    | Sum.inr (Sum.inl ⟨_, Term.func peanoarithmeticFunc.zero _⟩) => True
    | _ => False

instance : IsLeDot (SynDomain ℒ) where
  ledot v :=
    match v 0, v 1 with
    | Sum.inl n, Sum.inl m => n ≤ m
    | _, _ => False

instance : Zero (SynDomain ℒ) :=  ⟨Sum.inl 0⟩

instance : Succ (SynDomain ℒ) where
  succ x :=
    match x with
    | Sum.inl n => Sum.inl (n + 1)
    | _ => x

instance : Add (SynDomain ℒ) :=
⟨fun x y =>
  match x, y with
  | Sum.inl a, Sum.inl b => Sum.inl (a + b)
  | _, _ => x
⟩

instance : Mul (SynDomain ℒ) :=
⟨fun x y =>
  match x, y with
  | Sum.inl a, Sum.inl b => Sum.inl (a * b)
  | _, _ => x
⟩

instance : Zeroₛ (SynDomain ℒ) where
  zeroₛ := Sum.inr (Sum.inl ⟨0, Term.func peanoarithmeticFunc.zero ![]⟩)

instance : Succₛ (SynDomain ℒ) where
  succₛ x :=
    match x with
    | Sum.inr (Sum.inl ⟨n, t⟩) =>
        Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.succ ![t]⟩)
    | _ => x

instance : Addₛ (SynDomain ℒ) where
  addₛ x y :=
    match x, y with
    | Sum.inr (Sum.inl ⟨n₁, t₁⟩), Sum.inr (Sum.inl ⟨n₂, t₂⟩) =>
        if h : n₁ = n₂ then
          let t₂' : Term ℒ (ℕ ⊕ Fin n₁) := by
            cases h
            exact t₂
          Sum.inr (Sum.inl ⟨n₁, Term.func peanoarithmeticFunc.add ![t₁, t₂']⟩)
        else x
    | _, _ => x

instance : Mulₛ (SynDomain ℒ) where
  mulₛ x y :=
    match x, y with
    | Sum.inr (Sum.inl ⟨n₁, t₁⟩), Sum.inr (Sum.inl ⟨n₂, t₂⟩) =>
        if h : n₁ = n₂ then
          let t₂' : Term ℒ (ℕ ⊕ Fin n₁) := by
            cases h
            exact t₂
          Sum.inr (Sum.inl ⟨n₁, Term.func peanoarithmeticFunc.mult ![t₁, t₂']⟩)
        else x
    | _, _ => x

instance : MinDot (SynDomain ℒ) where
  mindot x y :=
    match x, y with
    | Sum.inr (Sum.inr ⟨n, φ⟩), Sum.inr (Sum.inr ⟨m, ψ⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by
            cases h
            exact φ ∧' ψ⟩)
        else x
    | _, _ => x

instance : MaxDot (SynDomain ℒ) where
  maxdot x y :=
    match x, y with
    | Sum.inr (Sum.inr ⟨n, φ⟩), Sum.inr (Sum.inr ⟨m, ψ⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by
            cases h
            exact φ ∨' ψ⟩)
        else x
    | _, _ => x

instance : NegDot (SynDomain ℒ) where
  negdot x :=
    match x with
    | Sum.inr (Sum.inr ⟨n, φ⟩) =>
        Sum.inr (Sum.inr ⟨n, BoundedFormula.not φ⟩)
    | _ => x

instance : Imp (SynDomain ℒ) where
  imp x y :=
    match x, y with
    | Sum.inr (Sum.inr ⟨n, φ⟩), Sum.inr (Sum.inr ⟨m, ψ⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by
            cases h
            exact BoundedFormula.imp φ ψ⟩)
        else x
    | _, _ => x


instance : Eq (SynDomain ℒ) where
  eq x y :=
    match x, y with
    | Sum.inr (Sum.inl ⟨n₁, t₁⟩), Sum.inr (Sum.inl ⟨n₂, t₂⟩) =>
        if h : n₁ = n₂ then
          let t₂' : ℒ.Term (ℕ ⊕ Fin n₁) := by
            cases h
            exact t₂
          Sum.inr (Sum.inr ⟨n₁, BoundedFormula.equal t₁ t₂'⟩)
        else
          Sum.inl 0
    | _, _ => Sum.inl 0

instance : Univ (SynDomain ℒ) where
  all x :=
    match x with
    | Sum.inr (Sum.inr ⟨n, φ⟩) =>
        Sum.inr (Sum.inr ⟨n + 1, liftFormula φ⟩)
    | _ => x

instance : Ex (SynDomain ℒ) where
  ex x :=
    match x with
    | Sum.inr (Sum.inr ⟨n, φ⟩) =>
        Sum.inr (Sum.inr ⟨n + 1, liftFormula φ⟩)
    | _ => x

instance : BoundVar (SynDomain ℒ) where
  bv x :=
    match x with
    | Sum.inl n => Sum.inr (Sum.inl ⟨n, boundVar (numeral n)⟩)
    | Sum.inr (Sum.inl ⟨k, u⟩) => Sum.inr (Sum.inl ⟨k, u⟩)
    | _ => x

/-- The homophonic syntax structure on `SynDomain ℒ`.
The resulting structure allows syntax and semantics to coexist in a single
domain, enabling homophonic (self-referential) interpretation of the language.
-/

def homophonic_syntax_structure : peanoarithmetic.Structure (SynDomain ℒ) where
  funMap
  | .zero, _  => 0
  | .succ, v  => Succ.succ (v 0)
  | .add, v   => v 0 + v 1
  | .mult, v  => v 0 * v 1

  | .zeroₛ, _  => Zeroₛ.zeroₛ
  | .succₛ, v  => Succₛ.succₛ (v 0)
  | .addₛ, v   => Addₛ.addₛ (v 0) (v 1)
  | .multₛ, v  => Mulₛ.mulₛ (v 0) (v 1)
  | .negₛ, v   => NegDot.negdot (v 0)
  | .andₛ, v   => MinDot.mindot (v 0) (v 1)
  | .orₛ, v    => MaxDot.maxdot (v 0) (v 1)
  | .impₛ, v   => Imp.imp (v 0) (v 1)
  | .eqₛ, v    => Eq.eq (v 0) (v 1)
  | .allₛ, v   => Univ.all (v 0)
  | .exₛ, v    => Ex.ex (v 0)
  | .boundₛ, v => BoundVar.bv (v 0)

  RelMap
  | .var, v    => IsVarDot.vardot v
  | .const, v  => IsConstDot.constdot v
  | .term, v   => IsTermDot.termdot v
  | .bdform, v => IsBdformDot.bdformdot v
  | .nat, v    => IsNatDot.natdot v
  | .le, v     => IsLeDot.ledot v

-- simp lemmas for the homophonic structure
@[simp] lemma nat_realize (v : Fin 1 → SynDomain ℒ) :
  IsNatDot.natdot v =
    match v 0 with
    | Sum.inl _ => True
    | _ => False :=
rfl

@[simp] lemma term_realize (v : Fin 2 → SynDomain ℒ) :
  IsTermDot.termdot v =
    match v 0, v 1 with
    | Sum.inl n, Sum.inr (Sum.inl ⟨m, _⟩) => n = m
    | _, _ => False :=
rfl

@[simp] lemma bdform_realize (v : Fin 2 → SynDomain ℒ) :
  IsBdformDot.bdformdot v =
    match v 0, v 1 with
    | Sum.inl n, Sum.inr (Sum.inr ⟨m, _⟩) => n = m
    | _, _ => False :=
rfl

@[simp] lemma var_realize (v : Fin 1 → SynDomain ℒ) :
  IsVarDot.vardot v =
    match v 0 with
    | Sum.inr (Sum.inl _) => True   -- ← accept all term encodings
    | _ => False :=
rfl

@[simp] lemma const_realize (v : Fin 1 → SynDomain ℒ) :
  IsConstDot.constdot v =
    match v 0 with
    | Sum.inr (Sum.inl ⟨_, Term.func peanoarithmeticFunc.zero _⟩) => True
    | _ => False :=
rfl

@[simp] lemma le_realize (v : Fin 2 → SynDomain ℒ) :
  IsLeDot.ledot v =
    match v 0, v 1 with
    | Sum.inl n, Sum.inl m => n ≤ m
    | _, _ => False :=
rfl

-- nat constructors
@[simp] lemma zero_realize : (0 : SynDomain ℒ) = Sum.inl 0 := rfl

@[simp] lemma succ_realize (n : SynDomain ℒ) :
  Succ.succ n =
    match n with
    | Sum.inl k => Sum.inl (k + 1)
    | _ => n :=
rfl

@[simp] lemma add_realize (x y : SynDomain ℒ) :
  x + y =
    match x, y with
    | Sum.inl a, Sum.inl b => Sum.inl (a + b)
    | _, _ => x :=
rfl

@[simp] lemma mul_realize (x y : SynDomain ℒ) :
  x * y =
    match x, y with
    | Sum.inl a, Sum.inl b => Sum.inl (a * b)
    | _, _ => x :=
rfl

-- syntax constructors
@[simp] lemma zeroₛ_realize :
  Zeroₛ.zeroₛ =
    (Sum.inr (Sum.inl ⟨0, Term.func peanoarithmeticFunc.zero ![]⟩) : SynDomain ℒ) :=
rfl

@[simp] lemma succₛ_realize (t : SynDomain ℒ) :
  Succₛ.succₛ t =
    match t with
    | Sum.inr (Sum.inl ⟨n, u⟩) =>
        Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.succ ![u]⟩)
    | _ => t :=
rfl

@[simp] lemma addₛ_realize (t₁ t₂ : SynDomain ℒ) :
  Addₛ.addₛ t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl ⟨n₁, u₁⟩), Sum.inr (Sum.inl ⟨n₂, u₂⟩) =>
        if h : n₁ = n₂ then
          let u₂' : Term ℒ (ℕ ⊕ Fin n₁) := by
            cases h
            exact u₂
          Sum.inr (Sum.inl ⟨n₁, Term.func peanoarithmeticFunc.add ![u₁, u₂']⟩)
        else t₁
    | _, _ => t₁ :=
rfl

@[simp] lemma mulₛ_realize (t₁ t₂ : SynDomain ℒ) :
  Mulₛ.mulₛ t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl ⟨n₁, u₁⟩), Sum.inr (Sum.inl ⟨n₂, u₂⟩) =>
        if h : n₁ = n₂ then
          let u₂' : Term ℒ (ℕ ⊕ Fin n₁) := by
            cases h
            exact u₂
          Sum.inr (Sum.inl ⟨n₁, Term.func peanoarithmeticFunc.mult ![u₁, u₂']⟩)
        else t₁
    | _, _ => t₁ :=
rfl

-- logical operators
@[simp] lemma neg_realize (t : SynDomain ℒ) :
  NegDot.negdot t =
    match t with
    | Sum.inr (Sum.inr ⟨n, u⟩) => Sum.inr (Sum.inr ⟨n, BoundedFormula.not u⟩)
    | _ => t :=
rfl

@[simp] lemma and_realize (φ ψ : SynDomain ℒ) :
  MinDot.mindot φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr ⟨n, f₁⟩), Sum.inr (Sum.inr ⟨m, f₂⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by cases h; exact f₁ ∧' f₂⟩)
        else φ
    | _, _ => φ :=
rfl

@[simp] lemma or_realize (φ ψ : SynDomain ℒ) :
  MaxDot.maxdot φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr ⟨n, f₁⟩), Sum.inr (Sum.inr ⟨m, f₂⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by cases h; exact f₁ ∨' f₂⟩)
        else φ
    | _, _ => φ :=
rfl

@[simp] lemma imp_realize (φ ψ : SynDomain ℒ) :
  Imp.imp φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr ⟨n, f₁⟩), Sum.inr (Sum.inr ⟨m, f₂⟩) =>
        if h : n = m then
          Sum.inr (Sum.inr ⟨n, by cases h; exact BoundedFormula.imp f₁ f₂⟩)
        else φ
    | _, _ => φ :=
rfl

@[simp] lemma eq_realize (t₁ t₂ : SynDomain ℒ) :
  Eq.eq t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl ⟨n₁, u₁⟩), Sum.inr (Sum.inl ⟨n₂, u₂⟩) =>
        if h : n₁ = n₂ then
          let u₂' : ℒ.Term (ℕ ⊕ Fin n₁) := by
            cases h
            exact u₂
          Sum.inr (Sum.inr ⟨n₁, BoundedFormula.equal u₁ u₂'⟩)
        else
          Sum.inl 0
    | _, _ => Sum.inl 0 :=
rfl

@[simp] lemma all_realize (φ : SynDomain ℒ) :
  Univ.all φ =
    match φ with
    | Sum.inr (Sum.inr ⟨n, f⟩) => Sum.inr (Sum.inr ⟨n+1, liftFormula f⟩)
    | _ => φ :=
rfl

@[simp] lemma ex_realize (φ : SynDomain ℒ) :
  Ex.ex φ =
    match φ with
    | Sum.inr (Sum.inr ⟨n, f⟩) => Sum.inr (Sum.inr ⟨n+1, liftFormula f⟩)
    | _ => φ :=
rfl

-- bound variables
@[simp] lemma bv_realize (t : SynDomain ℒ) :
  BoundVar.bv t =
    match t with
    | Sum.inl n => Sum.inr (Sum.inl ⟨n, boundVar (numeral n)⟩)
    | Sum.inr (Sum.inl ⟨k, u⟩) => Sum.inr (Sum.inl ⟨k, u⟩)
    | _ => t :=
rfl

@[simp]
lemma isBdForm_iff (φ : SynDomain ℒ) :
  isBdForm φ ↔ ∃ n f, φ = Sum.inr (Sum.inr ⟨n, f⟩) := by
    cases φ
    case inl =>
      simp [isBdForm]
    case inr val =>
      cases val
      case inl =>
        simp [isBdForm]
      case inr t =>
        simp [isBdForm]
        cases t with
        | mk n f =>
          exact ⟨n, f, rfl⟩

@[simp]
lemma bdformdot_iff (v : Fin 2 → SynDomain ℒ) :
  IsBdformDot.bdformdot v ↔
    ∃ n f, v 1 = Sum.inr (Sum.inr ⟨n, f⟩) ∧ v 0 = Sum.inl n := by
  cases v 0
  case inl n =>
    cases v 1
    case inl m =>
      simp [IsBdformDot.bdformdot]
      sorry
    case inr val =>
      cases val
      case inl t =>
        simp [IsBdformDot.bdformdot]
        sorry
      case inr t =>
        cases t with
        | mk m f =>
          simp [IsBdformDot.bdformdot]
          sorry
  case inr val =>
    cases val
    case inl t =>
      cases v 1 <;> simp [IsBdformDot.bdformdot]
      sorry
      sorry
    case inr t =>
      cases v 1 <;> simp [IsBdformDot.bdformdot]
      sorry
      sorry


@[simp]
lemma natdot_realize_iff (v : Fin 1 → SynDomain ℒ) :
  IsNatDot.natdot v ↔ ∃ n, v 0 = Sum.inl n := by
  cases h : v 0 <;> simp [IsNatDot.natdot, h]

@[simp]
lemma termdot_realize_iff (v : Fin 2 → SynDomain ℒ) :
  IsTermDot.termdot v ↔  ∃ n m t, v 0 = Sum.inl n ∧ v 1 = Sum.inr (Sum.inl ⟨m, t⟩) ∧ n = m := by
  cases h0 : v 0 <;>
  cases h1 : v 1 <;>
  simp [IsTermDot.termdot, h0, h1]
  sorry

@[simp] lemma funMap_zero {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.zero v = 0 := rfl

@[simp] theorem funMap_succ {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.succ v = Succ.succ (v 0) := rfl
@[simp] theorem funMap_add {v} :
Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.add v = v 0 + v 1 := rfl

@[simp] theorem funMap_mult {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.mult v = v 0 * v 1 := rfl

@[simp] lemma funMap_zeroₛ {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.zeroₛ v = Zeroₛ.zeroₛ := rfl

@[simp] theorem funMap_succₛ {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.succₛ v = Succₛ.succₛ (v 0) := rfl

@[simp] theorem funMap_addₛ {v} :
Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.addₛ v = v 0 +ₛ v 1 := rfl

@[simp] theorem funMap_multₛ {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.multₛ v = v 0 timesₛ v 1 := rfl

@[simp] theorem funMap_neg {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.negₛ v = NegDot.negdot (v 0) := rfl

@[simp] theorem funMap_and {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.andₛ v = MinDot.mindot (v 0) (v 1) := rfl

@[simp] theorem funMap_or {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.orₛ v = MaxDot.maxdot (v 0) (v 1) := rfl

@[simp] theorem funMap_imp {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.impₛ v = Imp.imp (v 0) (v 1) := rfl

@[simp] theorem funMap_eq {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.eqₛ v = Eq.eq (v 0) (v 1) := rfl

@[simp] theorem funMap_all {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.allₛ v = Univ.all (v 0) := rfl

@[simp] theorem funMap_ex {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.exₛ v = Ex.ex (v 0) := rfl

@[simp] theorem funMap_bv {v} :
  Structure.funMap (L := peanoarithmetic) (M := SynDomain ℒ) peanoarithmeticFunc.boundₛ v = BoundVar.bv (v 0) := rfl


@[simp] lemma nat_inl (n : ℕ) : isNat (Sum.inl n : SynDomain ℒ) := trivial

@[simp] lemma not_nat_term (t) : isNat (Sum.inr (Sum.inl t) : SynDomain ℒ) = False := rfl

@[simp] lemma not_nat_form (φ) : isNat (Sum.inr (Sum.inr φ) : SynDomain ℒ) = False := rfl

@[simp] lemma isTerm_term (t) :
  isTerm (Sum.inr (Sum.inl t) : SynDomain ℒ) := trivial

@[simp] lemma isTerm_nat (n) :
  isTerm (Sum.inl n : SynDomain ℒ) = False := rfl

@[simp] lemma isTerm_form (φ) :
  isTerm (Sum.inr (Sum.inr φ) : SynDomain ℒ) = False := rfl

@[simp] lemma isBdForm_form (φ) :
  isBdForm (Sum.inr (Sum.inr φ) : SynDomain ℒ) := trivial

@[simp] lemma isBdForm_nat (n) :
  isBdForm (Sum.inl n : SynDomain ℒ) = False := rfl

@[simp] lemma isBdForm_term (t) :
  isBdForm (Sum.inr (Sum.inl t) : SynDomain ℒ) = False := rfl

@[simp] lemma zero_nat :
  (0 : SynDomain ℒ) = Sum.inl 0 := rfl

@[simp] lemma succ_nat (n : ℕ) :
  Succ.succ (Sum.inl n : SynDomain ℒ) = Sum.inl (n + 1) := rfl

@[simp] lemma add_nat (a b : ℕ) :
  (Sum.inl a + Sum.inl b : SynDomain ℒ) = Sum.inl (a + b) := rfl

@[simp] lemma mul_nat (a b : ℕ) :
  (Sum.inl a * Sum.inl b : SynDomain ℒ) = Sum.inl (a * b) := rfl

@[simp] lemma isSuccₛ_term (n : ℕ) (t : ℒ.Term (ℕ ⊕ Fin n)) :
  isTerm (Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.succₛ ![t]⟩) : SynDomain ℒ) :=
by trivial

@[simp] lemma isAddₛ_term (n : ℕ) (t₁ t₂ : ℒ.Term (ℕ ⊕ Fin n)) :
  isTerm (Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.addₛ ![t₁, t₂]⟩) : SynDomain ℒ) :=
by trivial

@[simp] lemma isMulₛ_term (n : ℕ) (t₁ t₂ : ℒ.Term (ℕ ⊕ Fin n)) :
  isTerm (Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.multₛ ![t₁, t₂]⟩) : SynDomain ℒ) :=
by trivial

@[simp] lemma isNegₛ_term (n : ℕ) (t : ℒ.Term (ℕ ⊕ Fin n)) :
  isTerm (Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.negₛ ![t]⟩) : SynDomain ℒ) :=
by trivial

@[simp] lemma isBound_var (n : ℕ) (t : ℒ.Term (ℕ ⊕ Fin n)) :
  isTerm (Sum.inr (Sum.inl ⟨n, Term.func peanoarithmeticFunc.boundₛ ![t]⟩) : SynDomain ℒ) :=
by trivial

@[simp] lemma bdform_imp (n) (φ ψ : ℒ.BoundedFormula ℕ n) :
  isBdForm (Sum.inr (Sum.inr ⟨n, BoundedFormula.imp φ ψ⟩) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_eq (t s : ℒ.Term (ℕ ⊕ Fin 0)) :
  isBdForm (Sum.inr (Sum.inr ⟨0, BoundedFormula.equal t s⟩) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_and (n) (φ ψ : ℒ.BoundedFormula ℕ n) :
  isBdForm (Sum.inr (Sum.inr ⟨n, φ ∧' ψ⟩) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_or (n) (φ ψ : ℒ.BoundedFormula ℕ n) :
  isBdForm (Sum.inr (Sum.inr ⟨n, φ ∨' ψ⟩) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_all (n) (φ : ℒ.BoundedFormula ℕ (n + 1)) :
  isBdForm (Sum.inr (Sum.inr ⟨n + 1, ∀' liftFormula φ⟩) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_ex (n) (φ : ℒ.BoundedFormula ℕ (n + 1)) :
  isBdForm (Sum.inr (Sum.inr ⟨n + 1, ∃' liftFormula φ⟩) : SynDomain ℒ) := by trivial

-- proof of the injectivity of the liftFormula function
lemma liftFormula_injective :
  Function.Injective (@liftFormula ℒ ℕ n) := by
  intro φ ψ h
  cases φ <;> cases ψ <;> simp [liftFormula] at h
  cases h
  rfl
  sorry
  sorry
  simp
  and_intros
  cases h with
  | intro h₁ h₂ =>
    apply liftFormula_injective at h₁
    exact h₁
  cases h with
  | intro h₁ h₂ =>
    apply liftFormula_injective at h₂
    exact h₂
  simp
  sorry

open Classical
@[simp] lemma imp_true_intro (P : Prop) : (P → True) := by
  intro _
  trivial

@[simp] lemma imp_from_false (P : Prop) : (False → P) := by
  intro h
  cases h

end Homophonic
