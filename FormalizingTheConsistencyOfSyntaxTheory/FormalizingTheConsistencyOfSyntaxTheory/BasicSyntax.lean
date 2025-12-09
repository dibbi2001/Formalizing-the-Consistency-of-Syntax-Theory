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
namespace Language
namespace Lo
inductive LoFunc : ℕ → Type _ where
  | zero : LoFunc 0
  | succ : LoFunc 1
  | add : LoFunc 2
  | mult : LoFunc 2
  deriving DecidableEq

def Language.Lo : Language :=
  { Functions := LoFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

def funToStr {n}: LoFunc n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "×"
instance {n : ℕ}: ToString (Language.Lo.Functions n) := ⟨funToStr⟩

-- Syntax
instance : Zero (Term Language.Lo α) where
  zero := Constants.term .zero

-- some nice definitions
def null : Term Language.Lo α :=
  Constants.term .zero

def numeral : ℕ → Term Language.Lo ℕ
  | .zero => null
  | .succ n => Term.func LoFunc.succ (λ _ => numeral n)

-- Syntax
class Succ (α : Type u) where
  succ : α → α

instance : Succ (Term Language.Lo α) where
  succ := Functions.apply₁ .succ

instance : Add (Term Language.Lo α) where
  add := Functions.apply₂ .add

instance : Mul (Term Language.Lo α) where
  mul := Functions.apply₂ .mult

section Coding
  variable {k : ℕ}
  def Func_enc : Language.Lo.Functions k → ℕ
    | .zero => Nat.pair 0 0 + 1
    | .succ => Nat.pair 1 0 + 1
    | .add => Nat.pair 2 0 + 1
    | .mult => Nat.pair 2 1 + 1

  def Func_dec : (n : ℕ) → Option (Language.Lo.Functions k)
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

  lemma Func_enc_dec : ∀ f : Language.Lo.Functions k, Func_dec (Func_enc f) = some f := by
    intro f
    cases f <;> simp [Func_enc, Func_dec]

  instance enc_f : Encodable (Language.Lo.Functions k) where
    encode := Func_enc
    decode := Func_dec
    encodek := Func_enc_dec

end Coding
end Lo

namespace Ls
inductive LsFunc : ℕ → Type _ where
  | zeroₛ : LsFunc 0
  | succₛ : LsFunc 1
  | addₛ : LsFunc 2
  | multₛ : LsFunc 2
  | negₛ : LsFunc 1
  | andₛ : LsFunc 2
  | orₛ : LsFunc 2
  | impₛ : LsFunc 2
  | allₛ : LsFunc 1
  | exₛ : LsFunc 1
  deriving DecidableEq

inductive LsRel : ℕ → Type _ where
  | varₛ : LsRel 1
  | termₛ : LsRel 1
  | constₛ : LsRel 1
  | bdformₛ : LsRel 1
  deriving DecidableEq

def Language.Ls : Language :=
  { Functions := LsFunc
    Relations := LsRel }

def funToStr {n}: LsFunc n → String
  | .zeroₛ => "0ₛ"
  | .succₛ => "Sₛ"
  | .addₛ => "+ₛ"
  | .multₛ => "×ₛ"
  | .negₛ => "𝑛𝑒𝑔ₛ"
  | .andₛ => "𝑐𝑜𝑛𝑗ₛ"
  | .orₛ => "𝑑𝑖𝑠𝑗ₛ"
  | .impₛ => "𝑐𝑜𝑛𝑑ₛ"
  | .allₛ => "𝑎𝑙𝑙ₛ"
  | .exₛ => "𝑒𝑥ₛ"
instance {n : ℕ}: ToString (Language.Ls.Functions n) := ⟨funToStr⟩

def relToStr {n} : Language.Ls.Relations n → String
  | .varₛ => "𝑣𝑎𝑟ₛ"
  | .termₛ => "𝑡𝑒𝑟𝑚ₛ"
  | .constₛ => "𝑐𝑜𝑛𝑠𝑡ₛ"
  | .bdformₛ => "𝑏𝑑𝑓𝑜𝑟𝑚ₛ"
instance {n} : ToString (Language.Ls.Relations n) := ⟨relToStr⟩

-- Syntax
instance : Zero (Term Language.Ls α) where
  zero := Constants.term .zeroₛ

-- some nice definitions
def nullₛ : Term Language.Ls α :=
  Constants.term .zeroₛ

def numeralₛ : ℕ → Term Language.Ls ℕ
  | .zero => nullₛ
  | .succ n => Term.func LsFunc.succₛ (λ _ => numeralₛ n)

-- Syntax
class Succ (α : Type u) where
  succ : α → α

instance : Succ (Term Language.Ls α) where
  succ := Functions.apply₁ .succₛ

instance : Add (Term Language.Ls α) where
  add := Functions.apply₂ .addₛ

instance : Mul (Term Language.Ls α) where
  mul := Functions.apply₂ .multₛ

instance : Neg (Term Language.Ls α) where
  neg := Functions.apply₁ .negₛ

instance : Min (Term Language.Ls α) where
  min := Functions.apply₂ .andₛ

instance : Max (Term Language.Ls α) where
  max := Functions.apply₂ .orₛ

class Imp (α : Type u) where
  imp : α → α → α

class Univ (α : Type u) where
  all : α → α

class Ex (α : Type u) where
  ex : α → α

instance : Imp (Term Language.Ls α) where
  imp := Functions.apply₂ .impₛ

instance : Univ (Term Language.Ls α) where
  all := Functions.apply₁ .allₛ

instance : Ex (Term Language.Ls α) where
  ex := Functions.apply₁ .exₛ

class IsVar (α : Type u) where
  var : α

class IsConst (α : Type u) where
  const : α

class IsTerm (α : Type u) where
  term : α

class IsBdform (α : Type u) where
  bdform : α

instance : IsVar (LsRel 1) where
  var := LsRel.varₛ

instance : IsConst (LsRel 1) where
  const := LsRel.constₛ

instance : IsTerm (LsRel 1) where
  term := LsRel.termₛ

instance : IsBdform (LsRel 1) where
  bdform := LsRel.bdformₛ

notation "Sₛ(" n ")" => Succ.succ n
notation n "+ₛ" m => Add.add n m
notation n "×ₛ" m => Mul.mul n m
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

abbrev ℒₛ := Language.Ls

section Coding
  variable {k : ℕ}
  def Func_enc : Language.Ls.Functions k → ℕ
    | .zeroₛ => Nat.pair 0 0 + 1
    | .succₛ => Nat.pair 1 0 + 1
    | .negₛ => Nat.pair 1 1 + 1
    | .allₛ => Nat.pair 1 2 + 1
    | .exₛ => Nat.pair 1 3 + 1
    | .addₛ => Nat.pair 2 0 + 1
    | .multₛ => Nat.pair 2 1 + 1
    | .andₛ => Nat.pair 2 2 + 1
    | .orₛ => Nat.pair 2 3 + 1
    | .impₛ => Nat.pair 2 4 + 1

  def Func_dec : (n : ℕ) → Option (Language.Ls.Functions k)
    | 0 => none
    | e + 1 =>
      match k with
        | 0 =>
          match e.unpair.2 with
            | 0 => some (.zeroₛ)
            | _ => none
        | 1 =>
          match e.unpair.2 with
            | 0 => some (.succₛ)
            | 1 => some (.negₛ)
            | 2 => some (.allₛ)
            | 3 => some (.exₛ)
            | _ => none
        | 2 =>
          match e.unpair.2 with
            | 0 => some (.addₛ)
            | 1 => some (.multₛ)
            | 2 => some (.andₛ)
            | 3 => some (.orₛ)
            | 4 => some (.impₛ)
            | _ => none
        | _ => none

  lemma Func_enc_dec : ∀ f : Language.Ls.Functions k, Func_dec (Func_enc f) = some f := by
    intro f
    cases f <;> simp [Func_enc, Func_dec]

  instance enc_f : Encodable (Language.Ls.Functions k) where
    encode := Func_enc
    decode := Func_dec
    encodek := Func_enc_dec

  def Rel_enc : Language.Ls.Relations k → ℕ
    | .varₛ => Nat.pair 1 0 + 1
    | .termₛ => Nat.pair 1 1 + 1
    | .constₛ => Nat.pair 1 2 + 1
    | .bdformₛ => Nat.pair 1 3 + 1


  def Rel_dec : (n : ℕ) → Option (Language.Ls.Relations k)
    | 0 => none
    | e + 1 =>
      match k with
        | 1 =>
          match e.unpair.2 with
            | 0 => some .varₛ
            | 1 => some .termₛ
            | 2 => some .constₛ
            | 3 => some .bdformₛ
            | _ => none
        | _ => none

  lemma Rel_enc_dec : ∀ f : Language.Ls.Relations k, Rel_dec (Rel_enc f) = some f := by
    intro f
    cases f <;> simp [Rel_enc, Rel_dec]

  instance enc_r : Encodable (Language.Ls.Relations k) where
    encode := Rel_enc
    decode := Rel_dec
    encodek := Rel_enc_dec

end Coding

-- open TermEncoding

-- #check ⌜(∀' ∼(nullₛ =' Sₛ(&0)))⌝

#check (∀' ∼(nullₛ =' Sₛ(&0)))
#check Sₛ(Sₛ(nullₛ))
#check (nullₛ + Language.Ls.nullₛ)


#eval ((Sₛ(nullₛ) + Sₛ(Sₛ(nullₛ)) : Term Language.Ls ℕ))
#eval (Language.Ls.nullₛ + Language.Ls.nullₛ : Term Language.Ls ℕ)

end Ls

namespace L
open Lo
open Ls

def Language.L : Language :=
{ Functions := fun k => Sum (Language.Lo.Functions k) (Language.Ls.Functions k),
  Relations := fun k => Sum (Language.Lo.Relations k) (Language.Ls.Relations k) }

end L

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

  notation "⌜" t "⌝" => Language.Ls.numeralₛ (term_tonat t)
  notation "⌜" t "⌝" => Language.Ls.numeralₛ (sentence_term_tonat t)
  notation "⌜" φ "⌝" => Language.Ls.numeralₛ (formula_tonat φ)

end TermEncoding

namespace TermDecoding
 def term_ofnat : ℕ → Option (Term L (ℕ ⊕ Fin 0))
    | k =>
      match Encodable.decodeList k with
      | none      => none
      | some lst  =>
        match Term.listDecode lst with
        | []      => none
        | t :: _  => some t    -- first decoded term

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

namespace BoundedFormula
  variable {L : Language}{α : Type}{n : ℕ}

  def land (f₁ f₂: BoundedFormula L α n) :=
    ∼(f₁ ⟹ ∼f₂)
  scoped notation f₁ "∧'" f₂ => land f₁ f₂
  def lor (f₁ f₂ : BoundedFormula L α n) :=
    ((∼f₁) ⟹ f₂)
  scoped notation f₁ "∨'" f₂ => lor f₁ f₂
end BoundedFormula
