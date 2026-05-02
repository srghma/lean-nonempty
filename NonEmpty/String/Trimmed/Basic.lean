module

public import NonEmpty.String
import all NonEmpty.String
public import NonEmpty.String.Trimmed.Theorems
import all NonEmpty.String.Trimmed.Theorems
open NonEmpty.String

public section
namespace NonEmpty.String.Trimmed

structure NonEmptyStringTrimmed extends NonEmptyString where
  hasNoWhitespaceAtStart : toString.startsWith Char.isWhitespace = false
  hasNoWhitespaceAtEnd : toString.endsWith Char.isWhitespace = false

instance : ToString NonEmptyStringTrimmed where
  toString s := s.toNonEmptyString.toString

instance : Coe NonEmptyStringTrimmed String where
  coe s := s.toNonEmptyString.toString

instance : Coe NonEmptyStringTrimmed NonEmptyString where
  coe s := s.toNonEmptyString

instance : Inhabited NonEmptyStringTrimmed where
  default := NonEmptyStringTrimmed.mk (NonEmptyString.mk "Inhabited NonEmptyStringTrimmed" (by decide)) (by decide) (by native_decide)

namespace NonEmptyStringTrimmed

/-- Trim a string and return it as `NonEmptyStringTrimmed` if it's non-empty. -/
def fromString? (s : String) : Option NonEmptyStringTrimmed :=
  let t := s.trimAscii.toString
  if hne : t = "" then
    none
  else
    some {
      toString := t,
      isNonEmpty := hne,
      hasNoWhitespaceAtStart := trimAscii_toString_startsWith_whitespace_false s,
      hasNoWhitespaceAtEnd := trimAscii_toString_endsWith_whitespace_false s
    }

/-- Pre-trimmed non-empty string. -/
def fromNonEmptyString? (nes : NonEmptyString) : Option NonEmptyStringTrimmed :=
  fromString? nes.toString

/-- Trim a string and return it. Panics if the result is empty. -/
def fromString! (s : String) : NonEmptyStringTrimmed :=
  match fromString? s with
  | some nest => nest
  | none => panic! s!"NonEmptyStringTrimmed.fromString!: trimmed string is empty for input '{s}'"

abbrev fromLChar? (cs : List Char) : Option NonEmptyStringTrimmed := fromString? (String.ofList cs)

/-- Length of the string. -/
def length (s : NonEmptyStringTrimmed) : Nat := s.toNonEmptyString.toString.length

/-- Get the character at the given position. -/
def get (s : NonEmptyStringTrimmed) (pos : String.Pos.Raw) : Char := String.Pos.Raw.get s.toNonEmptyString.toString pos

/-- The first character of the string. Guaranteed to exist and be non-whitespace. -/
def front (s : NonEmptyStringTrimmed) : Char :=
  s.toNonEmptyString.toString.front

/-- The last character of the string. Guaranteed to exist and be non-whitespace. -/
def back (s : NonEmptyStringTrimmed) : Char :=
  s.toNonEmptyString.toString.back

/--
Concatenate two trimmed strings.
Since both strings have no whitespace at their boundaries, the result is also trimmed.
-/
instance : HAppend NonEmptyStringTrimmed NonEmptyStringTrimmed NonEmptyStringTrimmed where
  hAppend s1 s2 :=
    { toString := s1.toNonEmptyString.toString ++ s2.toNonEmptyString.toString,
      isNonEmpty := by
        intro h
        have := String.append_eq_empty_iff.1 h
        exact s1.toNonEmptyString.isNonEmpty this.1,
      hasNoWhitespaceAtStart := by
        rw [startsWith_append_of_nonempty s1.toNonEmptyString.isNonEmpty]
        exact s1.hasNoWhitespaceAtStart,
      hasNoWhitespaceAtEnd := by
        rw [endsWith_append_of_nonempty s2.toNonEmptyString.isNonEmpty]
        exact s2.hasNoWhitespaceAtEnd
    }

end NonEmptyStringTrimmed

/-! ### Macro -/

/--
A macro to create a `NonEmptyStringTrimmed` at compile time.
Trims the input string literal and fails if it becomes empty.
-/
macro "nest_trim!" s:str : term => do
  let strVal := s.getString.trimAscii.toString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty after trimming for nest!"
  else
    let trimmedLit := Lean.Syntax.mkStrLit strVal
    ``( NonEmptyStringTrimmed.mk
          (NonEmptyString.mk $trimmedLit (of_decide_eq_true rfl))
          (by native_decide)
          (by native_decide) )

#guard (nest_trim!"  world  ").toString == "world"

macro "nest!" s:str : term => do
  let strVal := s.getString
  if strVal == "" then
    Lean.Macro.throwErrorAt s "String literal cannot be empty"
  else if strVal.startsWith Char.isWhitespace then
    Lean.Macro.throwErrorAt s "There are whitespace at start"
  else if strVal.endsWith Char.isWhitespace then
    Lean.Macro.throwErrorAt s "There are whitespace at end"
  else
    let strLit := Lean.Syntax.mkStrLit strVal
    ``( NonEmptyStringTrimmed.mk
          (NonEmptyString.mk $strLit (of_decide_eq_true rfl))
          (by native_decide)
          (by native_decide) )


/--
error: There are whitespace at end
-/
#guard_msgs in
#guard (nest!"world ")

#guard (nest!"world").toString == "world"
#guard (nest!"a").toString == "a"

end NonEmpty.String.Trimmed
