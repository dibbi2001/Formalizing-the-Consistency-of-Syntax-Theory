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

namespace Language.peanoarithmetic
  -- Syntax
  instance : Zero (peanoarithmetic.Term α) where
    zero := Constants.term .zero

  -- some nice definitions
  def null : Term peanoarithmetic α :=
    Constants.term .zero

  def numeral : ℕ → peanoarithmetic.Term ℕ
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

  abbrev ℒ := Language.peanoarithmetic

  -- Semantics

  variable {M : Type*} {v : α → M}

  section Structure

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

  instance : IsVar ((Fin 1 → M) → Prop) where
    var := var_prop

  instance : IsConst ((Fin 1 → M) → Prop) where
    const := const_prop

  instance : IsTerm ((Fin 1 → M) → Prop) where
    term := term_prop

  instance : IsBdform ((Fin 1 → M) → Prop) where
    bdform := bdform_prop

  variable [Zero M] [Succ M] [Add M] [Mul M]
  [NegDot M] [MinDot M] [MaxDot M]
  [Imp M] [Univ M] [Ex M]
  [IsVar ((Fin 1 → M) → Prop)] [IsConst ((Fin 1 → M) → Prop)] [IsTerm ((Fin 1 → M) → Prop)] [IsBdform ((Fin 1 → M) → Prop)]

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
    | .var, v => (IsVar.var : (Fin 1 → M) → Prop) v
    | .const, v => (IsConst.const : (Fin 1 → M) → Prop) v
    | .term, v => (IsTerm.term : (Fin 1 → M) → Prop) v
    | .bdform, v => (IsBdform.bdform : (Fin 1 → M) → Prop) v

  end Structure

  section

  variable [Zero M] [Succ M] [Add M] [Mul M]
  [NegDot M] [MinDot M] [MaxDot M]
  [Imp M] [Univ M] [Ex M]
  [IsVar ((Fin 1 → M) → Prop)] [IsConst ((Fin 1 → M) → Prop)] [IsTerm ((Fin 1 → M) → Prop)] [IsBdform ((Fin 1 → M) → Prop)]


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

  -- instance : Succ ℕ := ⟨Nat.succ⟩
  -- instance : Add ℕ := ⟨Nat.add⟩
  -- instance : Mul ℕ := ⟨Nat.mul⟩
  -- instance : NegDot ℕ :=


  -- def r : ℕ → ℕ := fun x => x

  -- #eval Term.realize r (S(S(0) + S(0)) : peanoarithmetic.Term ℕ)
  -- #eval Term.realize r (S(S(S(0))) * S(S(S(0))) : peanoarithmetic.Term ℕ)
  -- #eval Term.realize r (null + null)

  end

  section Coding
    variable {k : ℕ}
    def Func_enc : peanoarithmetic.Functions k → ℕ
      | .zero => Nat.pair 0 0 + 1
      | .succ => Nat.pair 1 0 + 1
      | .neg => Nat.pair 1 1 + 1
      | .all => Nat.pair 1 2 + 1
      | .ex => Nat.pair 1 3 + 1
      | .add => Nat.pair 2 0 + 1
      | .mult => Nat.pair 2 1 + 1
      | .and => Nat.pair 2 2 + 1
      | .or => Nat.pair 2 3 + 1
      | .imp => Nat.pair 2 4 + 1

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
              | 1 => some (.neg)
              | 2 => some (.all)
              | 3 => some (.ex)
              | _ => none
          | 2 =>
            match e.unpair.2 with
              | 0 => some (.add)
              | 1 => some (.mult)
              | 2 => some (.and)
              | 3 => some (.or)
              | 4 => some (.imp)
              | _ => none
          | _ => none

    lemma Func_enc_dec : ∀ f : peanoarithmetic.Functions k, Func_dec (Func_enc f) = some f := by
      intro f
      cases f <;> simp [Func_enc, Func_dec]

    instance enc_f : Encodable (peanoarithmetic.Functions k) where
      encode := Func_enc
      decode := Func_dec
      encodek := Func_enc_dec

    def Rel_enc : peanoarithmetic.Relations k → ℕ
      | .var => Nat.pair 1 0 + 1
      | .term => Nat.pair 1 1 + 1
      | .const => Nat.pair 1 2 + 1
      | .bdform => Nat.pair 1 3 + 1


    def Rel_dec : (n : ℕ) → Option (peanoarithmetic.Relations k)
      | 0 => none
      | e + 1 =>
        match k with
          | 1 =>
            match e.unpair.2 with
              | 0 => some .var
              | 1 => some .term
              | 2 => some .const
              | 3 => some .bdform
              | _ => none
          | _ => none

    lemma Rel_enc_dec : ∀ f : peanoarithmetic.Relations k, Rel_dec (Rel_enc f) = some f := by
      intro f
      cases f <;> simp [Rel_enc, Rel_dec]

    instance enc_r : Encodable (peanoarithmetic.Relations k) where
      encode := Rel_enc
      decode := Rel_dec
      encodek := Rel_enc_dec

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

notation "⌜" t "⌝" => peanoarithmetic.numeral (term_tonat t)
notation "⌜" t "⌝" => peanoarithmetic.numeral (sentence_term_tonat t)
notation "⌜" φ "⌝" => peanoarithmetic.numeral (formula_tonat φ)

end TermEncoding

open TermEncoding

#check ⌜(∀' ∼(null =' S(&0)))⌝

#check (∀' ∼(null =' S(&0)))
#check S(S(null))
#check (null + peanoarithmetic.null)

#eval ((S(null) + S(S(null)) : Term peanoarithmetic ℕ))
#eval (peanoarithmetic.null + peanoarithmetic.null : Term peanoarithmetic ℕ)

end Language.peanoarithmetic

end FirstOrder
