module

public import NonEmpty.String
public meta import NonEmpty.StringSlice.Basic
public import NonEmpty.StringSlice.Basic
public import NonEmpty.StringTrimmed.Basic
public import NonEmpty.StringTrimmedSlice.Theorems

open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed
open String

public section
namespace NonEmpty.StringTrimmedSlice

structure NonEmptyStringTrimmedSlice extends NonEmptyStringSlice where
  hasNoWhitespaceAtStart : toSlice.startsWith Char.isWhitespace = false := by decide
  hasNoWhitespaceAtEnd : toSlice.endsWith Char.isWhitespace = false := by decide
  deriving Hashable, Ord --, Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

instance : BEq NonEmptyStringTrimmedSlice where
  beq a b := a.toSlice == b.toSlice

instance : ToString NonEmptyStringTrimmedSlice where
  toString s := s.toNonEmptyStringSlice.toString

instance : ReflBEq NonEmptyStringTrimmedSlice where
  rfl {a} := ReflBEq.rfl (a := a.toSlice)

instance : LT NonEmptyStringTrimmedSlice where
  lt a b := a.toSlice < b.toSlice

instance : LE NonEmptyStringTrimmedSlice where
  le a b := a.toSlice ≤ b.toSlice

instance (a b : NonEmptyStringTrimmedSlice) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toSlice < b.toSlice))

instance (a b : NonEmptyStringTrimmedSlice) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toSlice ≤ b.toSlice))

instance : Min NonEmptyStringTrimmedSlice where
  min a b := if a ≤ b then a else b

instance : Max NonEmptyStringTrimmedSlice where
  max a b := if a ≤ b then b else a

instance {m : Type u → Type v} [Monad m] : ForIn m NonEmptyStringTrimmedSlice Char where
  forIn s init f := forIn s.toNonEmptyStringSlice init f

@[inline]
def toNonEmptyStringTrimmed (s : NonEmptyStringTrimmedSlice) : NonEmptyStringTrimmed :=
  NonEmptyStringTrimmed.mk s.toNonEmptyStringSlice.toNonEmptyString
    (by
      have h1 := s.hasNoWhitespaceAtStart
      have h2 := Slice.startsWith_copy (s := s.toSlice) (pat := Char.isWhitespace)
      rw [h1] at h2
      exact h2
    )
    (by
      have h1 := s.hasNoWhitespaceAtEnd
      have h2 := Slice.endsWith_copy (s := s.toSlice) (pat := Char.isWhitespace)
      rw [h1] at h2
      exact h2
    )

@[inline]
def toNonEmptyString (s : NonEmptyStringTrimmedSlice) : NonEmpty.String.NonEmptyString :=
  s.toNonEmptyStringSlice.toNonEmptyString

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- @[inline]
-- instance : CoeOut NonEmptyStringTrimmedSlice String.Slice where
--   coe s := s.toSlice

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- @[inline]
-- instance : CoeOut NonEmptyStringTrimmedSlice NonEmptyStringSlice where
--   coe s := s.toNonEmptyStringSlice

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- @[inline]
-- instance : CoeOut NonEmptyStringTrimmedSlice String where
--   coe s := s.toString

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- @[inline]
-- instance : CoeOut NonEmptyStringTrimmedSlice NonEmptyString where
--   coe s := s.toNonEmptyString

-- TODO: if uncomment then HAppend ++ will stop working (macro called binop% which aggressively attempts to unify the operands to a single, homogeneous type before considering heterogeneous HAppend instances)
-- @[inline]
-- instance : CoeOut NonEmptyStringTrimmedSlice NonEmptyStringTrimmed where
--   coe s := toNonEmptyStringTrimmed s

instance : Inhabited NonEmptyStringTrimmedSlice where
  default := ⟨NonEmptyStringSlice.mk "a".toSlice (by native_decide), by native_decide, by native_decide⟩

namespace NonEmptyStringTrimmedSlice

/-- Trim a slice and return it as `NonEmptyStringTrimmedSlice` if it's non-empty. -/
def fromSlice? (s : String.Slice) : Option NonEmptyStringTrimmedSlice :=
  let t := s.trimAscii
  if hne : t.isEmpty = false then
    some {
      toSlice := t,
      isNonEmpty := hne,
      hasNoWhitespaceAtStart := Slice.trimAscii_startsWith_whitespace_false s,
      hasNoWhitespaceAtEnd := Slice.trimAscii_endsWith_whitespace_false s
    }
  else
    none

/-- Trim a string and return it as a slice if it's non-empty. -/
def fromString? (s : String) : Option NonEmptyStringTrimmedSlice :=
  fromSlice? s.toSlice

end NonEmptyStringTrimmedSlice
end NonEmpty.StringTrimmedSlice
