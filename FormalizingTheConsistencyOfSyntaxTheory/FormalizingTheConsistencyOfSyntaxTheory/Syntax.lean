import Mathlib.ModelTheory.Semantics
import Mathlib.Computability.Encoding
import Mathlib.Computability.Primrec

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


variable {α : Type*} {n : ℕ}
universe u

namespace FirstOrder

inductive peanoarithmeticFunc : ℕ → Type _ where
  | zero : peanoarithmeticFunc 0
  | succ : peanoarithmeticFunc 1
  | add : peanoarithmeticFunc 2
  | mult : peanoarithmeticFunc 2
  | neg : peanoarithmeticFunc 1
  | and : peanoarithmeticFunc 2
  | or : peanoarithmeticFunc 2
  | imp : peanoarithmeticFunc 2
  | all : peanoarithmeticFunc 1
  | ex : peanoarithmeticFunc 1
  deriving DecidableEq

inductive peanoarithmeticRel : ℕ → Type _ where
  | var : peanoarithmeticRel 1
  | term : peanoarithmeticRel 1
  | const : peanoarithmeticRel 1
  | bdform : peanoarithmeticRel 1
  deriving DecidableEq

def Language.peanoarithmetic : Language :=
  { Functions := peanoarithmeticFunc
    Relations := peanoarithmeticRel }

def funToStr {n}: peanoarithmeticFunc n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "×"
  | .neg => "𝑛𝑒𝑔"
  | .and => "𝑐𝑜𝑛𝑗"
  | .or => "𝑑𝑖𝑠𝑗"
  | .imp => "𝑐𝑜𝑛𝑑"
  | .all => "𝑎𝑙𝑙"
  | .ex => "𝑒𝑥"
instance {n : ℕ}: ToString (Language.peanoarithmetic.Functions n) := ⟨funToStr⟩

def relToStr {n} : Language.peanoarithmetic.Relations n → String
  | .var => "𝑣𝑎𝑟"
  | .term => "𝑡𝑒𝑟𝑚"
  | .const => "𝑐𝑜𝑛𝑠𝑡"
  | .bdform => "𝑏𝑑𝑓𝑜𝑟𝑚"
instance {n} : ToString (Language.peanoarithmetic.Relations n) := ⟨relToStr⟩

namespace Language
  namespace peanoarithmetic

    instance : Zero (peanoarithmetic.Term α) where
      zero := Constants.term .zero

    def null : Term peanoarithmetic α :=
      Constants.term .zero

    def numeral : ℕ → peanoarithmetic.Term α
      | .zero => null
      | .succ n => Term.func peanoarithmeticFunc.succ (λ _ => numeral n)

    instance {α : Type _} : OfNat (Term peanoarithmetic α) (n : Nat) where
      ofNat := numeral n

    instance : Inhabited (peanoarithmetic.Term α) :=
      ⟨peanoarithmetic.null⟩

    class Succ (α : Type u) where
      succ : α → α

    instance : Succ (peanoarithmetic.Term α) where
      succ := Functions.apply₁ .succ

    instance : Add (peanoarithmetic.Term α) where
      add := Functions.apply₂ .add

    instance : Mul (peanoarithmetic.Term α) where
      mul := Functions.apply₂ .mult

    instance : Neg (peanoarithmetic.Term α) where
      neg := Functions.apply₁ .neg

    instance : Min (peanoarithmetic.Term α) where
      min := Functions.apply₂ .and

    instance : Max (peanoarithmetic.Term α) where
      max := Functions.apply₂ .or

    class Imp (α : Type u) where
      imp : α → α → α

    class Univ (α : Type u) where
      all : α → α

    class Ex (α : Type u) where
      ex : α → α

    instance : Imp (peanoarithmetic.Term α) where
      imp := Functions.apply₂ .imp

    instance : Univ (peanoarithmetic.Term α) where
      all := Functions.apply₁ .all

    instance : Ex (peanoarithmetic.Term α) where
      ex := Functions.apply₁ .ex

    class IsVar (α : Type u) where
      var : α

    class IsConst (α : Type u) where
      const : α

    class IsTerm (α : Type u) where
      term : α

    class IsBdform (α : Type u) where
      bdform : α

    instance : IsVar (peanoarithmeticRel 1) where
      var := peanoarithmeticRel.var

    instance : IsConst (peanoarithmeticRel 1) where
      const := peanoarithmeticRel.const

    instance : IsTerm (peanoarithmeticRel 1) where
      term := peanoarithmeticRel.term

    instance : IsBdform (peanoarithmeticRel 1) where
      bdform := peanoarithmeticRel.bdform

    notation "S(" n ")" => Succ.succ n
    notation n "add" m => Add.add n m
    notation n "times" m => Mul.mul n m
    notation n "⬝∧" m => And.and n m
    notation n "⬝∨" m => Or.or n m
    notation "⬝∼" n => Neg.neg n
    notation n "⬝⟹" m => Imp.imp n m
    notation "⬝∀" n => Univ.all n
    notation "⬝∃" n => Ex.ex n

    notation "Var(" x ")" => IsVar.var x
    notation "Const(" c ")" => IsConst.const c
    notation "Term(" t ")" => IsTerm.term t
    notation "BdForm(" t ")" => IsBdform.bdform t

    -- notation "S(" n ")" => Term.func peanoarithmeticFunc.succ ![n]
    -- notation "zero" => Term.func peanoarithmeticFunc.zero ![]
    -- notation n "add" m => Term.func peanoarithmeticFunc.add ![n,m]
    -- notation n "times" m => Term.func peanoarithmeticFunc.mult ![n,m]
    -- notation n "⬝∧" m => Term.func peanoarithmeticFunc.and ![n,m]
    -- notation n "⬝∨" m => Term.func peanoarithmeticFunc.or ![n,m]
    -- notation "⬝∼" n => Term.func peanoarithmeticFunc.neg ![n]
    -- notation n "⬝⟹" m => Term.func peanoarithmeticFunc.imp ![n,m]
    -- notation "⬝∀" n => Term.func peanoarithmeticFunc.all ![n]
    -- notation "⬝∃" n => Term.func peanoarithmeticFunc.ex ![n]

    abbrev ℒ := Language.peanoarithmetic

    -- @[simp]
    -- def null : Term peanoarithmetic α :=
    --   Term.func .zero ![]

    -- @[simp]
    -- def numeral : ℕ → Term peanoarithmetic α
    --   | .zero => null
    --   | .succ n => S(numeral n)

    -- variable {M : Type*} {v : α → M}

    -- section

    -- variable [Zero M] [Succ M] [Add M] [Mul M]
    -- [Neg M] [Min M] [Max M] [Imp M] [Univ M] [Ex M]
    -- [IsVar M] [IsConst M] [IsTerm M] [IsBdform M]

    -- instance : peanoarithmetic.Structure M where
    --   funMap
    --   | .zero, _  => 0
    --   | .succ, v => Succ.succ (v 0)
    --   | .add, v => (v 0) + (v 1)
    --   | .mult, v => (v 0 ) * (v 1)
    --   | .neg, v => -(v 0)
    --   | .and, v => (v 0)
    --   | .or, v => (v 0)
    --   | .imp, v => (v 0)
    --   | .all, v => (v 0)
    --   | .ex, v => (v 0)
    --   RelMap
    --   | .var, _ => True
    --   | .const, _ => True
    --   | .term, _ => True
    --   | .bdform, _ => True

    #check (∀' ∼(null =' S(&0)))
    #check S(S(null))
    #check (peanoarithmetic.null + peanoarithmetic.null)

    #eval ((S(null) + S(null) : Term peanoarithmetic ℕ))



    -- end

end Language.peanoarithmetic
