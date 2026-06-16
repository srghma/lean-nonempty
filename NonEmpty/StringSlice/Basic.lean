module

public import NonEmpty.String
import Init.Data.String.Substring
import Init.Data.String.Lemmas.IsEmpty

@[expose] public section
namespace NonEmpty.StringSlice

/--
A non-empty string slice.

Despite the historical name, this intentionally wraps `String.Slice`, not `Substring.Raw`, because
`String.Slice` is the safe API Lean is moving toward.
-/
structure NonEmptyStringSlice where
  toSlice : String.Slice
  isNonEmpty : toSlice.isEmpty = false

instance : CoeOut NonEmptyStringSlice String.Slice where
  coe s := s.toSlice

instance : ToString NonEmptyStringSlice where
  toString s := s.toSlice.copy

instance : BEq NonEmptyStringSlice where
  beq a b := a.toSlice == b.toSlice

instance : Hashable NonEmptyStringSlice where
  hash s := hash s.toSlice

instance : LT NonEmptyStringSlice where
  lt a b := a.toSlice < b.toSlice

instance : Ord NonEmptyStringSlice where
  compare a b := compare a.toSlice b.toSlice

namespace NonEmptyStringSlice

@[inline] def fromSlice? (s : String.Slice) : Option NonEmptyStringSlice :=
  if h : s.isEmpty = false then some ⟨s, h⟩ else none

@[inline] def fromString? (s : String) : Option NonEmptyStringSlice :=
  fromSlice? s.toSlice

@[inline] def fromSubstringRaw? (s : Substring.Raw) : Option NonEmptyStringSlice :=
  s.toSlice?.bind fromSlice?

@[inline] def toString (s : NonEmptyStringSlice) : String :=
  s.toSlice.copy

@[inline] def toSubstringRaw (s : NonEmptyStringSlice) : Substring.Raw :=
  Substring.Raw.ofSlice s.toSlice

@[inline] def toNonEmptyString (s : NonEmptyStringSlice) : NonEmpty.String.NonEmptyString :=
  NonEmpty.String.NonEmptyString.mk s.toString (by
    simpa only [toString, ne_eq, String.Slice.copy_eq_empty_iff, Bool.not_eq_true] using
      (String.Slice.copy_ne_empty_iff).2 s.isNonEmpty)

@[simp] theorem toString_ne_empty (s : NonEmptyStringSlice) : s.toString ≠ "" := by
  simpa only [toString, ne_eq, String.Slice.copy_eq_empty_iff, Bool.not_eq_true] using
    (String.Slice.copy_ne_empty_iff).2 s.isNonEmpty

@[inline] def front (s : NonEmptyStringSlice) : Char :=
  s.toSlice.front

@[inline] def back (s : NonEmptyStringSlice) : Char :=
  s.toSlice.back

instance : HAppend String.Slice NonEmptyStringSlice NonEmptyStringSlice where
  hAppend s1 s2 := ⟨(s1.copy ++ s2.toString).toSlice, by simp only [String.isEmpty_toSlice,
    String.isEmpty_eq_false_iff, ne_eq, String.append_eq_empty_iff, String.Slice.copy_eq_empty_iff,
    toString_ne_empty, and_false, not_false_eq_true]⟩

instance : HAppend NonEmptyStringSlice String.Slice NonEmptyStringSlice where
  hAppend s1 s2 := ⟨(s1.toString ++ s2.copy).toSlice, by simp only [String.isEmpty_toSlice,
    String.isEmpty_eq_false_iff, ne_eq, String.append_eq_empty_iff, toString_ne_empty,
    String.Slice.copy_eq_empty_iff, false_and, not_false_eq_true]⟩

instance : HAppend NonEmptyStringSlice NonEmptyStringSlice NonEmptyStringSlice where
  hAppend s1 s2 := ⟨(s1.toString ++ s2.toString).toSlice, by simp only [String.isEmpty_toSlice,
    String.isEmpty_eq_false_iff, ne_eq, String.append_eq_empty_iff, toString_ne_empty, and_self,
    not_false_eq_true]⟩

-- ============================================================
-- Coercions (downgraders)
-- ============================================================

/-- Coerce a `NonEmptyStringSlice` to a `NonEmptyString` (via `.toNonEmptyString`).
    Transitively, `NonEmptyStringSlice → NonEmptyString → String` is also available. -/
@[inline]
instance : CoeOut NonEmptyStringSlice NonEmpty.String.NonEmptyString where
  coe s := s.toNonEmptyString

end NonEmptyStringSlice

end NonEmpty.StringSlice
