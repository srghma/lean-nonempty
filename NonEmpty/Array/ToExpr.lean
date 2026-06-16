module
public import Lean.ToExpr
import Lean
public import NonEmpty.Array.Basic

open Lean Meta Elab

@[expose] public section

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
