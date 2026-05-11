module

public section
namespace NonEmpty.Array

structure NonEmptyArray (α : Type u) where
  toArray : Array α
  isNonEmpty : toArray.size > 0
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
  xs.toArray[0]'xs.isNonEmpty

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
  exact xs.isNonEmpty
⟩

abbrev append (nel1 : NonEmptyArray α) (nel2 : NonEmptyArray α) : NonEmptyArray α := ⟨nel1.toArray ++ nel2.toArray, by
  simp only [Array.size_append]
  exact Nat.add_pos_left nel1.isNonEmpty nel2.toArray.size
⟩

abbrev mapM [Monad m] [Inhabited β] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  return (NonEmptyArray.fromArray! (← as.toArray.mapM f))

end NonEmptyArray

section


-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![ $elems,* ]) => do
    let terms := elems.getElems
    if terms.isEmpty then
      Lean.Macro.throwError "#! literal must contain at least one element"
    else
      ``(NonEmptyArray.mk #[$elems,*] (by decide))

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard (#![1, 2, 3]).head = 1
#guard (#![1, 2, 3]).tail = #[2, 3]
#guard (#![1, 2, 3]).size = 3

end
