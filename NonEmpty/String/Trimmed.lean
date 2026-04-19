import NonEmpty.String.Trimmed.Theorems

open String

/-! ### NonEmptyStringTrimmed -/

structure NonEmptyStringTrimmed where
  toString : String
  hasNoWhitespaceAtStart : toString.startsWith Char.isWhitespace = false
  hasNoWhitespaceAtEnd : toString.endsWith Char.isWhitespace = false
  isNonEmpty : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq

instance : ToString NonEmptyStringTrimmed where
  toString s := s.toString

namespace NonEmptyStringTrimmed

/-- Trim a string and return it as `NonEmptyStringTrimmed` if it's non-empty. -/
def fromString? (s : String) : Option NonEmptyStringTrimmed :=
  let tSlice := s.trimAscii
  let t := tSlice.toString
  if hne : t = "" then
    none
  else
    if h1 : t.startsWith Char.isWhitespace = false then
      if h2 : t.endsWith Char.isWhitespace = false then
        some ⟨t, h1, h2, hne⟩
      else none
    else none

abbrev fromLChar? (cs : List Char) : Option NonEmptyStringTrimmed := fromString? (String.ofList cs)

end NonEmptyStringTrimmed

/-! ### Macro -/

section
open Lean Meta Elab

macro "nest!" s:str : term => do
  let strVal := s.getString.trimAscii.toString
  if strVal.isEmpty then
    Macro.throwErrorAt s "String literal cannot be empty after trimming for nest!"
  else
    let trimmedLit := Syntax.mkStrLit strVal
    ``( (NonEmptyStringTrimmed.mk $trimmedLit (by native_decide) (by native_decide) (by decide) : NonEmptyStringTrimmed) )

end section

#guard (nest!"  world  ").toString == "world"
example : (nest!"  world  ").toString.startsWith Char.isWhitespace = false := (nest!"  world  ").hasNoWhitespaceAtStart
example : (nest!"  world  ").toString.endsWith Char.isWhitespace = false := (nest!"  world  ").hasNoWhitespaceAtEnd
example : (nest!"  world  ").toString ≠ "" := (nest!"  world  ").isNonEmpty
