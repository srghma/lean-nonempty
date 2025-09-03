import Lean.Elab.Term

structure NonEmptyString where
  toString : String
  property : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq

instance : ToString NonEmptyString where
  toString s := s.toString

instance : Inhabited NonEmptyString where
  default := ⟨"DEFAULT NonEmptyString", by simp⟩

namespace NonEmptyString

abbrev fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none

abbrev fromString! (s : String) : NonEmptyString :=
  match NonEmptyString.fromString? s with
  | some nes => nes
  | none => panic! "Expected non-empty string, got: '{s}'"

abbrev fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨⟨cs⟩, by
    intro contra
    apply h
    rw [String.ext_iff] at contra
    exact contra⟩

abbrev fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.mk cs)

abbrev fromLChar! (cs : List Char) : NonEmptyString :=
  match NonEmptyString.fromLChar? cs with
  | some nes => nes
  | none => panic! "Expected non-empty string, got: '{cs}'"

end NonEmptyString

instance : ToString NonEmptyString where
  toString := NonEmptyString.toString

section
open Lean Meta Elab

private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  -- Eq.refl.{1} is used because we're dealing with Type 0 (not Prop)
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

instance : ToExpr NonEmptyString where
  toTypeExpr := mkConst ``NonEmptyString
  toExpr nes :=
    let sExpr := toExpr nes.toString
    let emptyStrExpr := toExpr ""
    let propIsEqEmpty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) sExpr emptyStrExpr
    let instDecEqEmptyExpr := mkApp2 (mkConst ``instDecidableEqString) sExpr emptyStrExpr
    let propIsNonEmpty := mkApp (mkConst ``Not) propIsEqEmpty
    let instDecNeEmptyExpr := mkApp2 (mkConst ``instDecidableNot) propIsEqEmpty instDecEqEmptyExpr
    let finalProofExpr := mkDecidableProof propIsNonEmpty instDecNeEmptyExpr
    mkApp2 (mkConst ``NonEmptyString.mk) sExpr finalProofExpr

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (of_decide_eq_true (Eq.refl true)) : NonEmptyString) )

elab "nes_elab!" s:str : term => do
  let strVal := s.getString
  match NonEmptyString.fromString? strVal with
  | some nesVal => return (toExpr nesVal)
  | none => throwErrorAt s "String literal cannot be empty for nes!"

end section

example := nes!"world"
example := nes_elab!"world"

#guard (nes!"hello" = nes_elab!"hello")
