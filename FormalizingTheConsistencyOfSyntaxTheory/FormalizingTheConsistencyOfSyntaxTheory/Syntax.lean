import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Encoding

open FirstOrder
open Language

namespace String
  def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

  #eval vecToStr !["a","b","c"]

end String

namespace Term
  variable {L : Language} {α β : Type}
  variable [∀ k, ToString (L.Functions k)] [ToString α] [ToString β]

  section ToString
    def toStr : Term L ℕ → String :=
      fun t : Term L ℕ =>
        match t with
        | .var k => "⬝" ++ toString k
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr (ts i)) ++ ")"

    instance : Repr (Term L ℕ) := ⟨fun t _ => toStr t⟩
    instance : ToString (Term L ℕ) := ⟨toStr⟩

    def toStr_oplus : Term L (α ⊕ β) → String :=
      fun t : Term L (α ⊕ β) =>
        match t with
        | .var k =>
          match k with
            | (Sum.inl l) => "#" ++ toString l
            | (Sum.inr l) => "&" ++ toString l
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr_oplus (ts i)) ++ ")"

    instance : Repr (Term L (α ⊕ β)) := ⟨fun t _ => toStr_oplus t⟩
    instance : ToString (Term L (α ⊕ β)) := ⟨toStr_oplus⟩
  end ToString
end Term

namespace BoundedFormula
  section ToString
    variable {L : Language} {α : Type} {n : ℕ}
    variable [∀ k, ToString (L.Functions k)] [∀ k, ToString (L.Relations k)] [ToString α]

    def toStr {n} : BoundedFormula L α n → String
      | .falsum                    => "⊥"
      | .equal t₁ t₂               => toString t₁ ++ " = " ++ toString t₂
      | .rel R ts                  => toString R ++ "(" ++ String.vecToStr (fun i => toString (ts i)) ++ ")"
      | .imp f₁ f₂                 => "(" ++ toStr f₁ ++ " → " ++ toStr f₂ ++ ")"
      | .all f                     => "∀" ++ toStr f

    instance : Repr (BoundedFormula L α n) := ⟨fun t _ => toStr t⟩
    instance : ToString (BoundedFormula L α n) := ⟨toStr⟩
  end ToString

 @[simp]
  def to_extra_fin {n : ℕ} (v : Fin n) : Fin (n + 1) :=
    match v with
    | .mk val isLt => by
      have step1 : n < n + 1 := by
        simp
      have step2 : val < n + 1 := by
        apply Nat.lt_trans isLt step1
      apply Fin.mk val step2

end BoundedFormula

variable {α : Type*} {n : ℕ}
universe u

namespace FirstOrder

inductive peanoarithmeticFunc : ℕ → Type _ where
  | zero : peanoarithmeticFunc 0
  | succ : peanoarithmeticFunc 1
  | add : peanoarithmeticFunc 2
  | mult : peanoarithmeticFunc 2
  deriving DecidableEq

def Language.peanoarithmetic : Language :=
  { Functions := peanoarithmeticFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

def funToStr {n}: peanoarithmeticFunc n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "×"
instance {n : ℕ}: ToString (Language.peanoarithmetic.Functions n) := ⟨funToStr⟩

namespace Language.peanoarithmetic
  -- Syntax
  instance : Zero (peanoarithmetic.Term α) where
    zero := Constants.term .zero

  -- some nice definitions
  def null : Term peanoarithmetic α :=
    Constants.term .zero

  def numeral : ℕ → peanoarithmetic.Term α
    | .zero => null
    | .succ n => Term.func peanoarithmeticFunc.succ (λ _ => numeral n)

  -- Syntax
  class Succ (α : Type u) where
    succ : α → α

  instance : Succ (peanoarithmetic.Term α) where
    succ := Functions.apply₁ .succ

  instance : Add (peanoarithmetic.Term α) where
    add := Functions.apply₂ .add

  instance : Mul (peanoarithmetic.Term α) where
    mul := Functions.apply₂ .mult

  notation "S(" n ")" => Succ.succ n
  notation n "add" m => Add.add n m
  notation n "times" m => Mul.mul n m

  abbrev ℒ := Language.peanoarithmetic

  -- Semantics

  variable {M : Type*} {v : α → M}

  section Structure

  variable [Zero M] [Succ M] [Add M] [Mul M]

  instance : peanoarithmetic.Structure M where
    funMap
    | .zero, _  => 0
    | .succ, v => Succ.succ (v 0)
    | .add, v => (v 0) + (v 1)
    | .mult, v => (v 0 ) * (v 1)
  end Structure

  section

  variable [Zero M] [Succ M] [Add M] [Mul M]

  @[simp] theorem funMap_zero {v} :
    Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.zero v = 0 := rfl

  @[simp] theorem funMap_succ {v} :
    Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.succ v = Succ.succ (v 0) := rfl
  @[simp] theorem funMap_add {v} :
  Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.add v = v 0 + v 1 := rfl

  @[simp] theorem funMap_mult {v} :
    Structure.funMap (L := peanoarithmetic) (M := M) peanoarithmeticFunc.mult v = v 0 * v 1 := rfl

  @[simp] theorem realize_null : Term.realize v (Language.peanoarithmetic.null : peanoarithmetic.Term α) = 0 := rfl

  @[simp] theorem realize_succ (t : peanoarithmetic.Term α) :
    Term.realize v (Succ.succ t) = Succ.succ (Term.realize v t) := rfl

  @[simp] theorem realize_add (t₁ t₂ : peanoarithmetic.Term α) :
    Term.realize v (t₁ + t₂) = Term.realize v t₁ + Term.realize v t₂ := rfl

  @[simp] theorem realize_mult (t₁ t₂ : peanoarithmetic.Term α) :
    Term.realize v (t₁ * t₂) = Term.realize v t₁ * Term.realize v t₂ := rfl

  instance : Succ ℕ := ⟨Nat.succ⟩
  instance : Add ℕ := ⟨Nat.add⟩
  instance : Mul ℕ := ⟨Nat.mul⟩

  def r : ℕ → ℕ := fun x => x

  #eval Term.realize r (S(S(0) + S(0)) : peanoarithmetic.Term ℕ)
  #eval Term.realize r (S(S(S(0))) * S(S(S(0))) : peanoarithmetic.Term ℕ)
  #eval Term.realize r (null + null)

  end

  section Coding
    variable {k : ℕ}
    def Func_enc : peanoarithmetic.Functions k → ℕ
      | .zero => Nat.pair 0 0 + 1
      | .succ => Nat.pair 1 0 + 1
      | .add => Nat.pair 2 0 + 1
      | .mult => Nat.pair 2 1 + 1

    def Func_dec : (n : ℕ) → Option (peanoarithmetic.Functions k)
      | 0 => none
      | e + 1 =>
        match k with
          | 0 =>
            match e.unpair.2 with
              | 0 => some (.zero)
              | _ => none
          | 1 =>
            match e.unpair.2 with
              | 0 => some (.succ)
              | _ => none
          | 2 =>
            match e.unpair.2 with
              | 0 => some (.add)
              | 1 => some (.mult)
              | _ => none
          | _ => none

    lemma Func_enc_dec : ∀ f : peanoarithmetic.Functions k, Func_dec (Func_enc f) = some f := by
      intro f
      cases f <;> simp [Func_enc, Func_dec]

    instance enc_f : Encodable (peanoarithmetic.Functions k) where
      encode := Func_enc
      decode := Func_dec
      encodek := Func_enc_dec

  end Coding

namespace TermEncoding
  variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]
  /-- Encodes terms as natural numbers -/
  def term_tonat : Term L (ℕ ⊕ Fin 0) → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)
  def sentence_term_tonat : Term L (Empty ⊕ Fin 0) → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)

/-- Encodes BoundedFormulas as natural numbers -/
  def sent_tonat : BoundedFormula L Empty 0 → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)
  def formula_tonat {n : ℕ} : BoundedFormula L ℕ n → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)

end TermEncoding

#check (∀' ∼(null =' S(&0)))
#check S(S(null))
#check (null + peanoarithmetic.null)

#eval ((S(null) + S(S(null)) : Term peanoarithmetic ℕ))
#eval (peanoarithmetic.null + peanoarithmetic.null : Term peanoarithmetic ℕ)

end Language.peanoarithmetic

namespace TermRepresentation
open peanoarithmetic

inductive Formula : ℕ → Type _ where
  | neg : Formula 1
  | and : Formula 2
  | or : Formula 2
  | imp : Formula 2
  | ex : Formula 1
  | all : Formula 1
  deriving DecidableEq

def Language.meta : Language :=
  { Functions := Formula
    Relations := fun _ => Empty }

def metaPA : Language := Language.sum (peanoarithmetic) (Language.meta)

instance {n} : ToString (metaPA.Functions n) where
  toString
  | .inl f => funToStr f
  | .inr g =>
    match g with
    | .neg => "·∼"
    | .and => "·∧"
    | .or  => "·∨"
    | .imp => "·→"
    | .ex  => "·∃"
    | .all => "·∀"

/-- Term-level representations of logical constructors -/
def negTerm (t : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.neg) ![t]
def andTerm (t₁ t₂ : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.and) ![t₁, t₂]
def orTerm (t₁ t₂ : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.or) ![t₁, t₂]
def impTerm (t₁ t₂ : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.imp) ![t₁, t₂]
def exTerm (t : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.ex) ![t]
def allTerm (t : Term metaPA α) : Term metaPA α :=
  Term.func (Sum.inr Formula.all) ![t]

notation "·∼" t => negTerm t
infixr:60 " ·∧ " => andTerm
infixr:55 " ·∨ " => orTerm
infixr:50 " ·→ " => impTerm
notation "·∃" t => exTerm t
notation "·∀" t => allTerm t

variable {k : ℕ}
def FormulaFunc_enc : Formula k → ℕ
  | .neg => Nat.pair 1 1 + 1
  | .and => Nat.pair 2 2 + 1
  | .or  => Nat.pair 2 3 + 1
  | .imp => Nat.pair 2 4 + 1
  | .ex  => Nat.pair 1 2 + 1
  | .all => Nat.pair 1 3 + 1

def FormulaFunc_dec : ℕ → Option (Formula k)
  | 0 => none
  | e + 1 =>
    match k with
      | 0 =>
        match e.unpair.2 with
        | _ => none
      | 1 =>
        match e.unpair.2 with
          | 0 => none
          | 1 => some .neg
          | 2 => some .ex
          | 3 => some .all
          | _ => none
      | 2 =>
        match e.unpair.2 with
          | 0 => none
          | 1 => none
          | 2 => some .and
          | 3 => some .or
          | 4 => some .imp
          | _ => none
      | _ => none


lemma FormulaFunc_enc_dec :
    ∀ f : Formula k, FormulaFunc_dec (FormulaFunc_enc f) = some f := by
  intro f; cases f <;> simp [FormulaFunc_enc, FormulaFunc_dec]

instance enc_formula_f : Encodable (Formula k) where
  encode := FormulaFunc_enc
  decode := FormulaFunc_dec
  encodek := FormulaFunc_enc_dec

-- instance : Encodable (metaPA.Functions k) :=
--   Sum.encodable

end TermRepresentation

end FirstOrder
