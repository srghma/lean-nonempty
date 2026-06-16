module

public import NonEmpty.List
public import NonEmpty.String
public import NonEmpty.StringSlice
public import NonEmpty.StringTrimmed

/-!
# Cross-module coercions

This file defines `CoeOut` instances that require importing more than one NonEmpty module.
Import this file (or `NonEmpty` which re-exports it) to get automatic coercions between
the NonEmpty types.
-/


open NonEmpty.List
open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed

section

/-- Coerce `NonEmptyList NonEmptyString` to `NonEmptyList String` (map-downgrader). -/
@[inline]
instance : CoeOut (NonEmptyList NonEmptyString) (NonEmptyList String) where
  coe xs := xs.map (·.toString)

/-- Coerce `List NonEmptyString` to `List String` (map-downgrader). -/
@[inline]
instance : CoeOut (List NonEmptyString) (List String) where
  coe xs := xs.map (·.toString)

/-- Coerce `NonEmptyStringTrimmed` to `NonEmptyStringSlice`.
    The trimmed string is always non-empty. -/
@[inline]
instance : CoeOut NonEmptyStringTrimmed NonEmptyStringSlice where
  coe s := ⟨s.toString.toSlice, by
    have h : s.toString ≠ "" := s.toNonEmptyString.isNonEmpty
    simpa only [String.isEmpty_toSlice, String.isEmpty_eq_false_iff, ne_eq] using h
  ⟩

end
