module
public import Lean.ToExpr
import Lean
public import NonEmpty.StringTrimmed.Basic
import NonEmpty.String.ToExpr
public import NonEmpty.Utils.Decidable

open Lean Meta Elab

@[expose] public section

@[default_instance]
instance instToExprNonEmptyStringTrimmed : ToExpr NonEmpty.StringTrimmed.NonEmptyStringTrimmed where
  toTypeExpr := mkConst ``NonEmpty.StringTrimmed.NonEmptyStringTrimmed
  toExpr
    | ⟨nes, _, _⟩ =>
      let nesExpr := instToExprNonEmptyString.toExpr nes
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
