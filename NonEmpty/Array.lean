import Lean.Elab.Term
-- import Batteries.Data.Array.Basic
-- import Hammer

structure NonEmptyArray (α : Type u) where
  toArray : Array α
  property : toArray.size > 0
  deriving Hashable, Ord, Repr, DecidableEq

instance [BEq α] : BEq (NonEmptyArray α) where
  beq a b := a.toArray == b.toArray

instance [ToString α] : ToString (NonEmptyArray α) where
  toString a := "#!" ++ toString a.toArray

instance [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := ⟨#[default], by exact Nat.zero_lt_succ _⟩

namespace NonEmptyArray

abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs, h⟩ else none

abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match NonEmptyArray.fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty list"

abbrev head (xs : NonEmptyArray α) : α :=
  xs.toArray[0]'xs.property

abbrev tail (xs : NonEmptyArray α) : Array α :=
  xs.toArray[1:]

abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨#[a] ++ xs.toArray, by grind only [List.length_cons, = Vector.toArray_empty, → Array.eq_empty_of_append_eq_empty, Array.size_append, List.size_toArray]⟩

abbrev cons' (a : α) (xs : Array α) : NonEmptyArray α :=
  ⟨#[a] ++ xs, by grind only [List.length_cons, = Vector.toArray_empty, → Array.eq_empty_of_append_eq_empty, Array.size_append,
  List.size_toArray]⟩

abbrev singleton (a : α) : NonEmptyArray α := ⟨#[a], by grind only [List.length_cons, List.size_toArray]⟩

abbrev size (xs : NonEmptyArray α) : Nat := xs.toArray.size

abbrev get (xs : NonEmptyArray α) (i : Fin xs.toArray.size) : α :=
  xs.toArray[i]'i.isLt

abbrev get? (xs : NonEmptyArray α) (i : Nat) : Option α :=
  xs.toArray[i]?

abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β := ⟨xs.toArray.map f, by
  simp_all only [Array.size_map]
  exact xs.property
⟩

abbrev append (nel1 : NonEmptyArray α) (nel2 : NonEmptyArray α) : NonEmptyArray α := ⟨nel1.toArray ++ nel2.toArray, by
  simp only [Array.size_append]
  exact Nat.add_pos_left nel1.property nel2.toArray.size
⟩

abbrev mapM [Monad m] [Inhabited β] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  return (NonEmptyArray.fromArray! (← as.toArray.mapM f))

end NonEmptyArray

section

open Lean Macro Parser Term Elab Term

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmptyArray α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun xs =>
      let arrayExpr := toExpr xs.toArray
      let proofExpr := mkApp2 (mkConst ``Nat.zero_lt_of_ne_zero)
        (mkNatLit xs.toArray.size)
        (mkApp (mkConst ``Array.ne_empty_of_size_pos) arrayExpr)
      mkApp3 (mkConst ``NonEmptyArray.mk [level]) type arrayExpr proofExpr,
    toTypeExpr := mkApp (mkConst ``NonEmptyArray [level]) type }

-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![ $elems,* ]) => do
    let terms := elems.getElems
    if terms.isEmpty then
      Macro.throwError "#! literal must contain at least one element"
    else
      ``(NonEmptyArray.mk #[$elems,*] (by simp))

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard (#![1, 2, 3]).head = 1
#guard (#![1, 2, 3]).tail = #[2, 3]
#guard (#![1, 2, 3]).size = 3

end
