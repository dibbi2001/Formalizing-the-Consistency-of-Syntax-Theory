import FormalizingTheConsistencyOfSyntaxTheory.BasicSyntax

open FirstOrder
open Language
open peanoarithmetic
open TermEncoding


variable {α : Type*} {n : ℕ} {M : Type*} {v : α → M}
universe u

namespace Structure

variable (neg_repres : (Fin 1 → M) → M) (and_repres : (Fin 2 → M) → M) (or_repres : (Fin 2 → M) → M)
(var_prop : (Fin 1 → M) → Prop) (const_prop : (Fin 1 → M) → Prop) (term_prop : (Fin 1 → M) → Prop) (bdform_prop : (Fin 1 → M) → Prop)
(nat_prop : (Fin 1 → M) → Prop)

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

class IsNatDot (α : Type u) where
  natdot : (Fin 1 → α) → Prop

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

variable [Zero M] [Succ M] [Add M] [Mul M]
[NegDot M] [MinDot M] [MaxDot M]
[Imp M] [Eq M] [Univ M] [Ex M] [BoundVar M]
[IsVarDot M] [IsConstDot M] [IsTermDot M] [IsBdformDot M]
[IsNatDot M]
[Zeroₛ M] [Succₛ M] [Addₛ M] [Mulₛ M]

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

end PAStructure
end Structure

open TermEncoding
open TermDecoding
open BoundedFormula

variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]

namespace SyntaxStructure
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

  -- def term_repres (k : ℕ) : Prop :=  ∃ t, (term_ofnat : ℕ → Option (Term ℒ (ℕ ⊕ Fin 0))) k = some t

  def const_repres (k : ℕ) : ℕ :=
    match TermDecoding.term_ofnat (L := peanoarithmetic) k with
    | some (.func peanoarithmeticFunc.zeroₛ ![]) => 1
    | _ => 0

  def bdform_repres (k : ℕ) : ℕ :=
    match TermDecoding.formula_ofnat_general (L := peanoarithmetic) k with
    | some _ => 1
    | none   => 0

  def nat_repres (k : ℕ) : ℕ := k

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
  -- instance : peanoarithmetic.Structure ℕ := nat_syntax_structure

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

end SyntaxStructure

namespace Homophonic
open Structure
-- inductive SynObj (ℒ : Language) where
-- | nat  : ℕ → SynObj ℒ
-- | term : FirstOrder.Language.Term ℒ (ℕ ⊕ Fin 0) → SynObj ℒ
-- | form : FirstOrder.Language.BoundedFormula ℒ Empty 0 → SynObj ℒ

-- instance : Zero (SynObj ℒ) := ⟨SynObj.nat 0⟩

-- instance : Succ (SynObj ℒ) where
--   succ
--   | SynObj.nat n => SynObj.nat (Nat.succ n)
--   | _ => SynObj.nat 0

-- -- instance : Add (SynObj ℒ) where
-- --   add
-- --   | SynObj.nat a, SynObj.nat b => SynObj.nat (a + b)
-- --   | _, _ => SynObj.nat 0

-- instance : Mul (SynObj ℒ) where
--   mul
--   | SynObj.nat a, SynObj.nat b => SynObj.nat (a * b)
--   | _, _ => SynObj.nat 0

-- instance : Addₛ (SynObj ℒ) where
--   addₛ := fun
--     | SynObj.term t₁, SynObj.term t₂ => SynObj.term (Term.func peanoarithmeticFunc.addₛ ![t₁,t₂])
--     | _, _ => SynObj.nat 0


-- instance : IsNatDot (SynObj ℒ) where
--   natdot
--   | SynObj.nat _ => True
--   | _ => False

-- instance : IsVarDot (SynObj ℒ) where
--   vardot
--   | SynObj.term (Term.var _) => True
--   | _ => False

abbrev SynDomain (ℒ : Language) :=
  ℕ ⊕ (FirstOrder.Language.Term ℒ (ℕ ⊕ Fin 0)) ⊕ (FirstOrder.Language.BoundedFormula ℒ ℕ 0)

def isNat : SynDomain ℒ → Prop
| Sum.inl _ => True
| _ => False

def isTerm : SynDomain ℒ → Prop
| Sum.inr (Sum.inl _) => True
| _ => False

def isBdForm : SynDomain ℒ → Prop
| Sum.inr (Sum.inr _) => True
| _ => False

instance synNatDot : IsNatDot (SynDomain ℒ) :=
  { natdot := fun v =>
      match v 0 with
      | Sum.inl _ => True
      | _ => False }

instance synTermDot : IsTermDot (SynDomain ℒ) :=
  { termdot := fun v =>
    match v 0 with
    | Sum.inr (Sum.inl _) => True
    | _ => False }

instance synBdformDot : IsBdformDot (SynDomain ℒ) :=
  { bdformdot := fun v =>
    match v 0 with
    | Sum.inr (Sum.inr _) => True
    | _ => False }

instance : IsVarDot (SynDomain ℒ) where
  vardot v :=
    match v 0 with
    | Sum.inr (Sum.inl (Term.var _)) => True
    | _ => False

instance : IsConstDot (SynDomain ℒ) where
  constdot v :=
    match v 0 with
    | Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.zero _)) => True
    | _ => False

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
  zeroₛ := Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.zero ![]))

instance : Succₛ (SynDomain ℒ) where
  succₛ x :=
    match x with
    | Sum.inr (Sum.inl t) =>
        Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.succ ![t]))
    | _ => x

instance : Addₛ (SynDomain ℒ) where
  addₛ x y :=
    match x, y with
    | Sum.inr (Sum.inl t₁), Sum.inr (Sum.inl t₂) =>
        Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.add ![t₁,t₂]))
    | _, _ => x

instance : Mulₛ (SynDomain ℒ) where
  mulₛ x y :=
    match x, y with
    | Sum.inr (Sum.inl t₁), Sum.inr (Sum.inl t₂) =>
        Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.mult ![t₁,t₂]))
    | _, _ => x

instance : MinDot (SynDomain ℒ) where
  mindot x y :=
    match x, y with
    | Sum.inr (Sum.inr φ), Sum.inr (Sum.inr ψ) =>
        Sum.inr (Sum.inr (φ ∧' ψ))
    | _, _ => x

instance : MaxDot (SynDomain ℒ) where
  maxdot x y :=
    match x, y with
    | Sum.inr (Sum.inr φ), Sum.inr (Sum.inr ψ) =>
        Sum.inr (Sum.inr (φ ∨' ψ))
    | _, _ => x

instance : NegDot (SynDomain ℒ) where
  negdot x :=
    match x with
    | Sum.inr (Sum.inr φ) => Sum.inr (Sum.inr (BoundedFormula.not φ))
    | _ => x

instance : Imp (SynDomain ℒ) where
  imp x y :=
    match x, y with
    | Sum.inr (Sum.inr φ), Sum.inr (Sum.inr ψ) =>
        Sum.inr (Sum.inr (BoundedFormula.imp φ ψ))
    | _, _ => x

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


instance : Eq (SynDomain ℒ) where
  eq x y :=
    match x, y with
    | Sum.inr (Sum.inl t), Sum.inr (Sum.inl s) =>
        Sum.inr (Sum.inr (BoundedFormula.equal t s))
    | _, _ => Sum.inl 0

instance : Univ (SynDomain ℒ) where
  all x :=
    match x with
    | Sum.inr (Sum.inr φ) => Sum.inr (Sum.inr (∀' liftFormula φ))
    | _ => x

instance : Ex (SynDomain ℒ) where
  ex x :=
    match x with
    | Sum.inr (Sum.inr φ) => Sum.inr (Sum.inr (∃' liftFormula φ))
    | _ => x

instance : BoundVar (SynDomain ℒ) where
  bv x :=
    match x with
    | Sum.inl n => Sum.inr (Sum.inl (Term.var (Sum.inl n)))
    | _ => x

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

@[simp] lemma nat_realize (v : Fin 1 → SynDomain ℒ) :
  IsNatDot.natdot v =
    match v 0 with
    | Sum.inl _ => True
    | _ => False :=
rfl

@[simp] lemma term_realize (v : Fin 1 → SynDomain ℒ) :
  IsTermDot.termdot v =
    match v 0 with
    | Sum.inr (Sum.inl _) => True
    | _ => False :=
rfl

@[simp] lemma bdform_realize (v : Fin 1 → SynDomain ℒ) :
  IsBdformDot.bdformdot v =
    match v 0 with
    | Sum.inr (Sum.inr _) => True
    | _ => False :=
rfl

@[simp] lemma var_realize (v : Fin 1 → SynDomain ℒ) :
IsVarDot.vardot v =
    match v 0 with
    | Sum.inr (Sum.inl (Term.var _)) => True
    | _ => False :=
rfl

@[simp] lemma const_realize (v : Fin 1 → SynDomain ℒ) :
  IsConstDot.constdot v =
    match v 0 with
    | Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.zero _)) => True
    | _ => False :=
rfl

-- Nat constructors
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

@[simp] lemma zeroₛ_realize :
  Zeroₛ.zeroₛ = (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.zero ![])) : SynDomain ℒ) := rfl

@[simp] lemma succₛ_realize (t : SynDomain ℒ) :
  Succₛ.succₛ t =
    match t with
    | Sum.inr (Sum.inl u) => Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.succ ![u]))
    | _ => t :=
rfl

@[simp] lemma addₛ_realize (t₁ t₂ : SynDomain ℒ) :
  Addₛ.addₛ t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl u₁), Sum.inr (Sum.inl u₂) =>
        Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.add ![u₁,u₂]))
    | _, _ => t₁ :=
rfl

@[simp] lemma mulₛ_realize (t₁ t₂ : SynDomain ℒ) :
  Mulₛ.mulₛ t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl u₁), Sum.inr (Sum.inl u₂) =>
        Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.mult ![u₁,u₂]))
    | _, _ => t₁ :=
rfl

@[simp] lemma neg_realize (t : SynDomain ℒ) :
  NegDot.negdot t =
    match t with
    | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr (BoundedFormula.not u))
    | _ => t :=
rfl

@[simp] lemma and_realize (φ ψ : SynDomain ℒ) :
  MinDot.mindot φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr f₁), Sum.inr (Sum.inr f₂) => Sum.inr (Sum.inr (f₁ ∧' f₂))
    | _, _ => φ :=
rfl

@[simp] lemma or_realize (φ ψ : SynDomain ℒ) :
  MaxDot.maxdot φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr f₁), Sum.inr (Sum.inr f₂) => Sum.inr (Sum.inr (f₁ ∨' f₂))
    | _, _ => φ :=
rfl

@[simp] lemma imp_realize (φ ψ : SynDomain ℒ) :
  Imp.imp φ ψ =
    match φ, ψ with
    | Sum.inr (Sum.inr f₁), Sum.inr (Sum.inr f₂) => Sum.inr (Sum.inr (BoundedFormula.imp f₁ f₂))
    | _, _ => φ :=
rfl

@[simp] lemma eq_realize (t₁ t₂ : SynDomain ℒ) :
  Eq.eq t₁ t₂ =
    match t₁, t₂ with
    | Sum.inr (Sum.inl u₁), Sum.inr (Sum.inl u₂) => Sum.inr (Sum.inr (BoundedFormula.equal u₁ u₂))
    | _, _ => Sum.inl 0 :=
rfl

@[simp] lemma all_realize (φ : SynDomain ℒ) :
  Univ.all φ =
    match φ with
    | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr (∀' liftFormula f))
    | _ => φ :=
rfl

@[simp] lemma ex_realize (φ : SynDomain ℒ) :
  Ex.ex φ =
    match φ with
    | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr (∃' liftFormula f))
    | _ => φ :=
rfl

@[simp] lemma bv_realize (t : SynDomain ℒ) :
  BoundVar.bv t =
    match t with
    | Sum.inl n => Sum.inr (Sum.inl (Term.var (Sum.inl n)))
    | _ => t :=
rfl

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

@[simp] lemma isSuccₛ_term (t : ℒ.Term (ℕ ⊕ Fin 0)) :
  isTerm (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.succₛ ![t])) : SynDomain ℒ) := by trivial

@[simp] lemma isAddₛ_term (t₁ t₂ : ℒ.Term (ℕ ⊕ Fin 0)) :
  isTerm (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.addₛ ![t₁, t₂])) : SynDomain ℒ) := by trivial

@[simp] lemma isMulₛ_term (t₁ t₂ : ℒ.Term (ℕ ⊕ Fin 0)) :
  isTerm (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.multₛ ![t₁, t₂])) : SynDomain ℒ) := by trivial

@[simp] lemma isNegₛ_term (t : ℒ.Term (ℕ ⊕ Fin 0)) :
  isTerm (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.negₛ ![t])) : SynDomain ℒ) := by trivial

@[simp] lemma isBound_var (t : ℒ.Term (ℕ ⊕ Fin 0)) :
  isTerm (Sum.inr (Sum.inl (Term.func peanoarithmeticFunc.boundₛ ![t])) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_imp (φ ψ) :
  isBdForm (Sum.inr (Sum.inr (BoundedFormula.imp φ ψ)) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_eq (t s : ℒ.Term (ℕ ⊕ Fin 0)) :
  isBdForm (Sum.inr (Sum.inr (BoundedFormula.equal t s)) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_and (t s) :
  isBdForm (Sum.inr (Sum.inr (t ∧' s)) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_or (t s) :
  isBdForm (Sum.inr (Sum.inr (t ∨' s)) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_all (t ) :
  isBdForm (Sum.inr (Sum.inr (∀' t)) : SynDomain ℒ) := by trivial

@[simp] lemma bdform_ex (t ) :
  isBdForm (Sum.inr (Sum.inr (∃' t)) : SynDomain ℒ) := by trivial

open Classical
@[simp] lemma imp_true_intro (P : Prop) : (P → True) := by
  intro _
  trivial

@[simp] lemma imp_from_false (P : Prop) : (False → P) := by
  intro h
  cases h

-- @[simp] lemma nat_lookup_inl (M := SynDomain ℒ)  (n : ℕ) :
--   Nat(var (Sum.inr 0)).Realize default (Fin.snoc default (Sum.inl n)) = True :=
-- rfl

-- @[simp] lemma var_lookup_inl_fixed :
--   let v : Fin 1 → SynDomain ℒ := fun i => Sum.inl 0
--   Var(&ₛ(var (Sum.inr 0))).Realize  (Structure ℒ : (SynDomain ℒ) ) v = False := by
--   rfl


end Homophonic
