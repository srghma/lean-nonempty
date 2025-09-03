-- import Batteries.Data.List.Basic
import Lean.Elab.Term

structure NonEmptyList (α : Type u) where
  toList : List α
  -- property : toList ≠ [] -- if `toList.length > 0` wont it calculate length even if not needed?
  property : toList.length > 0
  deriving Hashable, Ord, Repr, DecidableEq

instance [BEq α] : BEq (NonEmptyList α) where
  beq a b := a.toList == b.toList

instance [ToString α] : ToString (NonEmptyList α) where
  toString a := "!" ++ toString a.toList

instance [Inhabited α] : Inhabited (NonEmptyList α) where
  -- default := ⟨[default], List.cons_ne_nil default []⟩
  default := ⟨[default], by exact Nat.zero_lt_succ _⟩

namespace NonEmptyList

abbrev fromList? (l : List α) : Option (NonEmptyList α) :=
  match h_l_struct : l with
  | [] => none
  | _ :: _ => some ⟨l, by simp only [h_l_struct, List.length_cons, gt_iff_lt, Nat.zero_lt_succ]⟩

abbrev fromList! [Inhabited α] (xs : List α) : NonEmptyList α :=
  match NonEmptyList.fromList? xs with
  | some xs => xs
  | none => panic! "Expected non-empty list"

abbrev head (xs : NonEmptyList α) : α :=
  xs.toList[0]'xs.property
  -- match h_proof : xs.toList with
  -- | [] => False.elim (xs.property h_proof)
  -- | firstElement :: _ => firstElement

abbrev tail (xs : NonEmptyList α) : List α := xs.toList.tail

abbrev cons (a : α) (xs : NonEmptyList α) : NonEmptyList α := ⟨a :: xs.toList,
  Nat.zero_lt_succ xs.toList.length
  -- List.cons_ne_nil a xs.toList
  ⟩

abbrev cons' (a : α) (xs : List α) : NonEmptyList α := ⟨a :: xs,
  Nat.zero_lt_succ xs.length
  -- List.cons_ne_nil a xs
⟩

abbrev singleton (a : α) : NonEmptyList α := ⟨[a], by
  simp only [List.length_cons, List.length_nil, Nat.zero_add, gt_iff_lt, Nat.lt_add_one]
  -- simp only [ne_eq, List.cons_ne_self, not_false_eq_true]
⟩

abbrev length (xs : NonEmptyList α) : Nat := xs.toList.length

abbrev get (xs : NonEmptyList α) (i : Fin xs.length) : α := xs.toList.get i

abbrev map {β : Type} (f : α → β) (xs : NonEmptyList α) : NonEmptyList β := ⟨xs.toList.map f, by
  simp only [List.length_map, gt_iff_lt];
  -- simp only [ne_eq, List.map_eq_nil_iff]
  exact xs.property
  ⟩

abbrev append (nel1 nel2 : NonEmptyList α) : NonEmptyList α := ⟨nel1.toList ++ nel2.toList, by
  -- simp only [ne_eq, List.append_eq_nil_iff, nel1.property, false_and, not_false_eq_true]
  simp_all only [List.length_append, gt_iff_lt]
  exact Nat.add_pos_left nel1.property nel2.toList.length
⟩

-- needs batteries
-- abbrev inits [Inhabited α] (xs : NonEmptyList α) : NonEmptyList (NonEmptyList α) :=
--   let allInits := xs.toList.inits.drop 1  -- drop the initial empty list
--   fromList! (allInits.map fromList!)

-- theorem mapM_length {m : Type 0 → Type 0} [Monad m] {α : Type 0} {β : Type 0}
--     (f : α → m β) (as : List α) :
--     Functor.map (fun xs => xs.length) (List.mapM f as) = Pure.pure (List.length as) := by

abbrev mapM [Monad m] [Inhabited β] (f : α → m β) (as : NonEmptyList α) : m (NonEmptyList β) :=
  return NonEmptyList.fromList! (← as.toList.mapM f)

end NonEmptyList

section

open Lean Macro Parser Term Elab Term

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmptyList α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun xs =>
      let listExpr := toExpr xs.toList
      let proofExpr := mkApp (mkConst ``Nat.zero_lt_succ) (mkNatLit (xs.toList.length - 1))
      mkApp3 (mkConst ``NonEmptyList.mk [level]) type listExpr proofExpr,
  -- { toExpr := fun xs =>
  --     match h : xs.toList with
  --     | x :: xs =>
  --       let xExpr := toExpr x
  --       let xsExpr := toExpr xs
  --       let listExpr := mkApp3 (mkConst ``List.cons [level]) type xExpr xsExpr
  --       let proofExpr := mkApp3 (mkConst ``List.cons_ne_nil [level]) type xExpr xsExpr
  --       mkApp3 (mkConst ``NonEmptyList.mk [level]) type listExpr proofExpr
  --     | [] => False.elim (xs.property h),
    toTypeExpr := mkApp (mkConst ``NonEmptyList [level]) type }

-- Macro for creating non-empty list literals
syntax "![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(![ $elems,* ]) => do
    let terms := elems.getElems
    if terms.isEmpty then
      Macro.throwError "nel! literal must contain at least one element"
    else
      ``(NonEmptyList.mk [$elems,*] (by simp))

example : NonEmptyList Nat := ![1, 2, 3]
example : NonEmptyList String := !["hello", "world"]
example : NonEmptyList Nat := ![10]

#guard ![1, 2, 3].head = 1 -- Should output 1
#guard ![1, 2, 3].tail = [2, 3] -- Should output [2, 3]
#guard ![1, 2, 3].length = 3 -- Should output 3

end
