module

public import Lean
public import Lean.Elab.Term

public section

structure NonEmptyString where
  toString : String
  isNonEmpty : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq

instance : ToString NonEmptyString where
  toString s := s.toString

namespace NonEmptyString

abbrev fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none

abbrev fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨String.ofList cs, by simp_all⟩

abbrev fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.ofList cs)

end NonEmptyString

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (by decide) : NonEmptyString) )

#guard (nes!"world").toString == "world"

end
