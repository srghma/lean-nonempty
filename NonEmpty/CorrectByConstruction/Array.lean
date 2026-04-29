module

public section

namespace NonEmpty.CorrectByConstruction.Array

structure NonEmptyArray (α : Type u) where
  head : α
  tail : Array α
  deriving Hashable, Ord, Repr, DecidableEq

instance [BEq α] : BEq (NonEmptyArray α) where
  beq a b := a.head == b.head && a.tail == b.tail

instance [ToString α] : ToString (NonEmptyArray α) where
  toString a := "#!" ++ toString (#[a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := ⟨default, #[]⟩

namespace NonEmptyArray

def toArray (xs : NonEmptyArray α) : Array α :=
  #[xs.head] ++ xs.tail

abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs[0]'h, xs[1:]⟩ else none

abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match NonEmptyArray.fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty list"

abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨a, #[xs.head] ++ xs.tail⟩

abbrev cons' (a : α) (xs : Array α) : NonEmptyArray α :=
  ⟨a, xs⟩

abbrev singleton (a : α) : NonEmptyArray α := ⟨a, #[]⟩

abbrev size (xs : NonEmptyArray α) : Nat := 1 + xs.tail.size

def get (xs : NonEmptyArray α) (i : Fin (1 + xs.tail.size)) : α :=
  match i with
  | ⟨0,     _⟩ => xs.head
  | ⟨n + 1, h⟩ => xs.tail[n]' (by omega)

abbrev get? (xs : NonEmptyArray α) (i : Nat) : Option α :=
  if i == 0 then
    some xs.head
  else
    xs.tail[i - 1]?

abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f xs.head, xs.tail.map f⟩

abbrev append (nel1 : NonEmptyArray α) (nel2 : NonEmptyArray α) : NonEmptyArray α :=
  ⟨nel1.head, nel1.tail ++ (#[nel2.head] ++ nel2.tail)⟩

def mapM [Monad m] [Inhabited β] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) := do
  let h ← f as.head
  let t ← as.tail.mapM f
  return ⟨h, t⟩

end NonEmptyArray

section

-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![])                           => Lean.Macro.throwError "#! literal must contain at least one element"
  | `(#![ $head:term ])               => ``(NonEmptyArray.mk $head #[])
  | `(#![ $head:term, $tail:term,* ]) => ``(NonEmptyArray.mk $head #[$tail,*])

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard (#![1, 2, 3]).head = 1
#guard (#![1, 2, 3]).tail = #[2, 3]
#guard (#![1, 2, 3]).size = 3

end

end NonEmpty.CorrectByConstruction.Array
