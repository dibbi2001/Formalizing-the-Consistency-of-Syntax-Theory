import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Encoding

/-This file contains a tostring function, encoding function and some notation for boundedformulas,
that was already defined in a previous project by B.J.G. Swaanen.
[Formalizing Axiomatic Theories of Truth] (https://github.com/ppls-nd-prs/formalizing-axiomatic-theories-of-truth)
-/

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


-- instance toStringEmpty : ToString Empty :=
--   {toString := fun e => Empty.elim e}
-- instance reprEmpty : Repr Empty :=
--   {reprPrec := fun e _ => Empty.elim e}

-- instance toStringFin {n : Nat} : ToString (Fin n) := { toString := fun f => toString (Fin.toNat f) }
-- instance reprFin {n : Nat} : Repr (Fin n) := { reprPrec := fun f _ => toString (Fin.toNat f) }


variable {α : Type*} {n : ℕ}
universe u

namespace FirstOrder

inductive peanoarithmeticFunc : ℕ → Type _ where
-- PA
  | zero : peanoarithmeticFunc 0
  | succ : peanoarithmeticFunc 1
  | add : peanoarithmeticFunc 2
  | mult : peanoarithmeticFunc 2
-- Syntax
  | zeroₛ : peanoarithmeticFunc 0
  | succₛ : peanoarithmeticFunc 1
  | addₛ : peanoarithmeticFunc 2
  | multₛ : peanoarithmeticFunc 2
  | negₛ : peanoarithmeticFunc 1
  | andₛ : peanoarithmeticFunc 2
  | orₛ : peanoarithmeticFunc 2
  | impₛ : peanoarithmeticFunc 2
  | eqₛ : peanoarithmeticFunc 2
  | allₛ : peanoarithmeticFunc 1
  | exₛ : peanoarithmeticFunc 1
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
  | .zeroₛ => "0ₛ"
  | .succₛ => "Sₛ"
  | .addₛ => "+ₛ"
  | .multₛ => "×ₛ"
  | .negₛ => "𝑛𝑒𝑔ₛ"
  | .andₛ => "𝑐𝑜𝑛𝑗ₛ"
  | .orₛ => "𝑑𝑖𝑠𝑗ₛ"
  | .impₛ => "𝑐𝑜𝑛𝑑ₛ"
  | .eqₛ => "𝑒𝑞ₛ"
  | .allₛ => "𝑎𝑙𝑙ₛ"
  | .exₛ => "𝑒𝑥ₛ"
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

  def nullₛ : Term peanoarithmetic α :=
    Constants.term .zeroₛ

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

  class Zeroₛ (α : Type u) where
    zeroₛ : α

  class Succₛ (α : Type u) where
    succₛ : α → α

  class Addₛ (α : Type u) where
    addₛ : α → α → α

  class Mulₛ (α : Type u) where
    mulₛ : α → α → α

  instance : Succₛ (peanoarithmetic.Term α) where
    succₛ := Functions.apply₁ .succₛ

  instance : Addₛ (peanoarithmetic.Term α) where
    addₛ := Functions.apply₂ .addₛ

  instance : Mulₛ (peanoarithmetic.Term α) where
    mulₛ := Functions.apply₂ .multₛ

  instance : Neg (peanoarithmetic.Term α) where
    neg := Functions.apply₁ .negₛ

  instance : Min (peanoarithmetic.Term α) where
    min := Functions.apply₂ .andₛ

  instance : Max (peanoarithmetic.Term α) where
    max := Functions.apply₂ .orₛ

  class Imp (α : Type u) where
    imp : α → α → α

  class Eq (α : Type u) where
    eq : α → α → α

  class Univ (α : Type u) where
    all : α → α

  class Ex (α : Type u) where
    ex : α → α

  instance : Imp (peanoarithmetic.Term α) where
    imp := Functions.apply₂ .impₛ

  instance : Eq (peanoarithmetic.Term α) where
    eq := Functions.apply₂ .eqₛ

  instance : Univ (peanoarithmetic.Term α) where
    all := Functions.apply₁ .allₛ

  instance : Ex (peanoarithmetic.Term α) where
    ex := Functions.apply₁ .exₛ

  class IsVar (α : Type u) where
    var : α

  class IsConst (α : Type u) where
    const : α

  class IsTerm (α : Type u) where
    term : α

  class IsBdform (α : Type u) where
    bdform : α

  instance : IsVar (Language.peanoarithmetic.Relations 1) where
    var := peanoarithmeticRel.var

  instance : IsConst (Language.peanoarithmetic.Relations 1) where
    const := peanoarithmeticRel.const

  instance : IsTerm (Language.peanoarithmetic.Relations 1) where
    term := peanoarithmeticRel.term

  instance : IsBdform (Language.peanoarithmetic.Relations 1) where
    bdform := peanoarithmeticRel.bdform

  notation "S(" n ")" => Succ.succ n
  notation n "add" m => Add.add n m
  notation n "times" m => Mul.mul n m

  notation "Sₛ(" n ")" => Term.func peanoarithmeticFunc.succₛ ![n]
  notation n "addₛ" m => Term.func peanoarithmeticFunc.addₛ ![n, m]
  notation n "timesₛ" m => Mulₛ.mulₛ n m

  notation n "⬝∧" m => Term.func peanoarithmeticFunc.andₛ ![n, m]
  notation n "⬝∨" m => Term.func peanoarithmeticFunc.orₛ ![n, m]
  notation "⬝∼" n => Term.func peanoarithmeticFunc.negₛ ![n]
  notation n "⬝⟹" m => Term.func peanoarithmeticFunc.impₛ ![n, m]
  notation n "⬝=" m => Term.func peanoarithmeticFunc.eqₛ ![n, m]
  notation "⬝∀" n => Term.func peanoarithmeticFunc.allₛ ![n]
  notation "⬝∃" n => Term.func peanoarithmeticFunc.exₛ ![n]

  notation "Var(" x ")" =>  BoundedFormula.rel (IsVar.var) ![x]
  notation "Const(" c ")" => BoundedFormula.rel (IsConst.const) ![c]
  notation "Term(" t ")" => BoundedFormula.rel (IsTerm.term) ![t]
  notation "BdForm(" t ")" => BoundedFormula.rel (IsBdform.bdform) ![t]

  abbrev ℒ := Language.peanoarithmetic

  section Coding
    variable {k : ℕ}
    def Func_enc : peanoarithmetic.Functions k → ℕ
    | .zero      => Nat.pair 0 0 + 1
    | .zeroₛ     => Nat.pair 0 1 + 1

    | .succ      => Nat.pair 1 0 + 1
    | .succₛ     => Nat.pair 1 1 + 1
    | .negₛ      => Nat.pair 1 2 + 1
    | .allₛ      => Nat.pair 1 3 + 1
    | .exₛ       => Nat.pair 1 4 + 1

    | .add       => Nat.pair 2 0 + 1
    | .mult      => Nat.pair 2 1 + 1
    | .addₛ      => Nat.pair 2 2 + 1
    | .multₛ     => Nat.pair 2 3 + 1
    | .andₛ      => Nat.pair 2 4 + 1
    | .orₛ       => Nat.pair 2 5 + 1
    | .impₛ      => Nat.pair 2 6 + 1
    | .eqₛ       => Nat.pair 2 7 + 1

    def Func_dec : (n : ℕ) → Option (peanoarithmetic.Functions k)
      | 0 => none
      | e + 1 =>
        match k with
          | 0 =>
            match e.unpair.2 with
              | 0 => some (.zero)
              | 1 => some (.zeroₛ)
              | _ => none
          | 1 =>
            match e.unpair.2 with
              | 0 => some (.succ)
              | 1 => some (.succₛ)
              | 2 => some (.negₛ)
              | 3 => some (.allₛ)
              | 4 => some (.exₛ)
              | _ => none
          | 2 =>
            match e.unpair.2 with
              | 0 => some (.add)
              | 1 => some (.mult)
              | 2 => some (.addₛ)
              | 3 => some (.multₛ)
              | 4 => some (.andₛ)
              | 5 => some (.orₛ)
              | 6 => some (.impₛ)
              | 7 => some (.eqₛ)
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

variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]

namespace TermEncoding
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

namespace TermDecoding
--  def term_ofnat : ℕ → Option (Term L (ℕ ⊕ Fin 0))
--     | k =>
--       match Encodable.decodeList k with
--       | none      => none
--       | some lst  =>
--         match Term.listDecode lst with
--         | []      => none
--         | t :: _  => some t    -- first decoded term
  def term_ofnat (k : ℕ) : Option (Term L (ℕ ⊕ Fin 0)) :=
    Encodable.decodeList k >>= fun lst =>
      (Term.listDecode lst).head?

  def sentence_term_ofnat : ℕ → Option (Term L (Empty ⊕ Fin 0))
    | k =>
      match Encodable.decodeList k with
      | none      => none
      | some lst  =>
        match Term.listDecode lst with
        | []      => none
        | t :: _  => some t

  def formula_ofnat_general (k : ℕ) : Option (Σ n, BoundedFormula L ℕ n) :=
    match Encodable.decodeList k with
    | none     => none
    | some lst =>
      match BoundedFormula.listDecode (α := ℕ) lst with
      | []     => none
      | x :: _ => some x

  def formula_ofnat (k : ℕ) : Option (BoundedFormula L ℕ n) :=
    match formula_ofnat_general k with
    | some ⟨m, φ⟩ =>
        if h : m = n then some (h ▸ φ) else none
    | none => none

  def sent_ofnat (k : ℕ) : Option (BoundedFormula L Empty 0) :=
    match Encodable.decodeList k with
    | none      => none
    | some lst  =>
      match BoundedFormula.listDecode (α := Empty) lst with
      | []              => none
      | ⟨n, φ⟩ :: _     =>
          if h : n = 0 then some (h ▸ φ) else none

end TermDecoding

open TermEncoding

#check ⌜(∀' ∼(null =' S(&0)))⌝

#check (∀' ∼(null =' S(&0)))
#check (∀' Var(&0) : BoundedFormula ℒ ℕ 0)
#check (∀' Term(&0 ⬝∧ &0) : BoundedFormula ℒ ℕ 0)
#check S(S(null))
#check (null + peanoarithmetic.null)

#eval ((S(null) + S(S(null)) : Term peanoarithmetic ℕ))
#eval (peanoarithmetic.null + peanoarithmetic.null : Term peanoarithmetic ℕ)

namespace BoundedFormula
  variable {L : Language}{α : Type}{n : ℕ}

  def land (f₁ f₂: BoundedFormula L α n) :=
    ∼(f₁ ⟹ ∼f₂)
  scoped notation f₁ "∧'" f₂ => land f₁ f₂
  def lor (f₁ f₂ : BoundedFormula L α n) :=
    ((∼f₁) ⟹ f₂)
  scoped notation f₁ "∨'" f₂ => lor f₁ f₂
end BoundedFormula

end Language.peanoarithmetic
end FirstOrder
