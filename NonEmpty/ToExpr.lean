module
public import Lean
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.StringTrimmed
public import NonEmpty.StringTrimmedSlice
public import NonEmpty.ArrayCorrectByConstruction
public import NonEmpty.Array

open Lean Meta Elab

@[expose] public section

def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

@[default_instance]
instance instToExprNonEmptyString : ToExpr NonEmpty.String.NonEmptyString where
  toTypeExpr := mkConst ``NonEmpty.String.NonEmptyString
  toExpr
    | ⟨s, _⟩ =>
      let sExpr := toExpr s
      let emptyStrExpr := toExpr ""

      let propIsEqEmpty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) sExpr emptyStrExpr
      let instDecEqEmptyExpr := mkApp2 (mkConst ``instDecidableEqString) sExpr emptyStrExpr
      let propIsNonEmpty := mkApp (mkConst ``Not) propIsEqEmpty
      let instDecNeEmptyExpr := mkApp2 (mkConst ``instDecidableNot) propIsEqEmpty instDecEqEmptyExpr

      let finalProofExpr := mkDecidableProof propIsNonEmpty instDecNeEmptyExpr

      mkApp2 (mkConst ``NonEmpty.String.NonEmptyString.mk) sExpr finalProofExpr

@[default_instance]
instance instToExprNonEmptyList {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmpty.List.NonEmptyList α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun
      | ⟨x :: xs, _⟩ =>
        let xExpr := toExpr x
        let xsExpr := toExpr xs
        mkApp3 (mkConst ``NonEmpty.List.NonEmptyList.cons' [level]) type xExpr xsExpr
      | ⟨[], proof⟩ => False.elim (Nat.not_lt_zero 0 proof),
    toTypeExpr := mkApp (mkConst ``NonEmpty.List.NonEmptyList [level]) type }

@[default_instance]
instance instToExprNonEmptyArray {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmpty.Array.NonEmptyArray α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun
      | ⟨arr, proof⟩ =>
        if h : arr.size > 0 then
          have h0 : 0 < arr.size := h
          let hd := arr[0]'h0
          let tl := arr.extract 1 arr.size
          mkApp3 (mkConst ``NonEmpty.Array.NonEmptyArray.cons' [level]) type (toExpr hd) (toExpr tl)
        else
          False.elim (Nat.not_lt_zero 0 (by rw [show arr.size = 0 from Nat.le_zero.mp (Nat.not_lt.mp h)] at proof; exact proof)),
    toTypeExpr := mkApp (mkConst ``NonEmpty.Array.NonEmptyArray [level]) type }

@[default_instance]
instance instToExprNonEmptyArrayCBC {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmpty.ArrayCorrectByConstruction.NonEmptyArray α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun
      | ⟨hd, tl⟩ =>
        mkApp3 (mkConst ``NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.mk [level]) type (toExpr hd) (toExpr tl),
    toTypeExpr := mkApp (mkConst ``NonEmpty.ArrayCorrectByConstruction.NonEmptyArray [level]) type }

-- NonEmptyStringSlice, NonEmptyStringTrimmed, NonEmptyStringTrimmedSlice

@[default_instance]
instance instToExprNonEmptyStringTrimmed : ToExpr NonEmpty.StringTrimmed.NonEmptyStringTrimmed where
  toTypeExpr := mkConst ``NonEmpty.StringTrimmed.NonEmptyStringTrimmed
  toExpr
    | ⟨nes, _, _⟩ =>
      let nesExpr := toExpr nes
      let sVal := nes.toString
      let sExpr := toExpr sVal
      let emptyBoolExpr := toExpr false

      let startsWithExpr := mkApp2 (mkConst ``String.startsWith) sExpr (mkConst ``Char.isWhitespace)
      let propStartIsEqFalse := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) startsWithExpr emptyBoolExpr
      let instDecEqStartExpr := mkApp2 (mkConst ``instDecidableEqBool) startsWithExpr emptyBoolExpr
      let proofStartExpr := mkDecidableProof propStartIsEqFalse instDecEqStartExpr

      let endsWithExpr := mkApp2 (mkConst ``String.endsWith) sExpr (mkConst ``Char.isWhitespace)
      let propEndIsEqFalse := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) endsWithExpr emptyBoolExpr
      let instDecEqEndExpr := mkApp2 (mkConst ``instDecidableEqBool) endsWithExpr emptyBoolExpr
      let proofEndExpr := mkDecidableProof propEndIsEqFalse instDecEqEndExpr

      mkApp3 (mkConst ``NonEmpty.StringTrimmed.NonEmptyStringTrimmed.mk) nesExpr proofStartExpr proofEndExpr
