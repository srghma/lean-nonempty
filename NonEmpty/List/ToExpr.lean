module
public import Lean.ToExpr
import Lean
public import NonEmpty.List.Basic

open Lean Meta Elab

@[expose] public section

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
