import Lean
import Aesop
import NonEmpty.String.Trimmed.Theorems

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
  let t := s.trimAscii.toString
  if hne : t = "" then
    none
  else
    some ⟨t,
      trimAscii_toString_startsWith_whitespace_false s,
      trimAscii_toString_endsWith_whitespace_false s,
      hne⟩

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
