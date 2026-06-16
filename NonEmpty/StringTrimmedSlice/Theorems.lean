module

public import NonEmpty.StringTrimmed.Theorems
import all Lean
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import all Init.Omega
import all Init.Data.String.Lemmas.TakeDrop
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Lemmas.IsEmpty

open String

public section

/-- `trimAscii` on a slice removes leading whitespace, so the result does not start with whitespace. -/
theorem Slice.trimAscii_startsWith_whitespace_false (s : Slice) :
    s.trimAscii.startsWith Char.isWhitespace = false := by
  simp only [Slice.trimAscii, Slice.trimAsciiEnd, Slice.trimAsciiStart, Slice.dropEndWhile, Slice.dropWhile]
  apply startsWith_sliceTo
  exact Slice.startsWith_dropWhile

/-- `trimAscii` on a slice removes trailing whitespace, so the result does not end with whitespace. -/
theorem Slice.trimAscii_endsWith_whitespace_false (s : Slice) :
    s.trimAscii.endsWith Char.isWhitespace = false := by
  simp only [Slice.trimAscii, Slice.trimAsciiEnd, Slice.trimAsciiStart]
  exact Slice.endsWith_dropEndWhile

