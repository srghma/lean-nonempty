-- module

-- import all Init.Data.String.TakeDrop
-- import Init.Data.String.Slice
-- import all Init.Data.String.Basic
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import Init.Omega
import Init.Data.String.Lemmas.TakeDrop
import Init.Data.String.Lemmas.Pattern.Pred
import Aesop
import Canonical

open String Slice

set_option allowUnsafeReducibility true

/-! ### Stability under Trimming -/

theorem Slice.startsWith_dropEndWhile_of_startsWith_false (s : Slice) (p q : Char → Bool) (h : s.startsWith p = false) :
    (s.dropEndWhile q).startsWith p = false := by
  rw [Slice.startsWith_bool_eq_false_iff_get] at h ⊢
  intro hne
  have hne' : s.startPos ≠ s.endPos := by
    intro heq
    have h' : s.skipSuffixWhile q = s.startPos := by
      rw [heq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Slice.Pattern.Model.Pos.revSkipWhile_eq_self]
      simp [String.Slice.Pattern.Model.CharPred.revMatchesAt_iff, Slice.Pattern.Model.CharPred.revMatchesAt_iff, heq]
    exact hne (Slice.Pos.ext (by simp [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, h']))
  have : (s.dropEndWhile q).startPos.get hne = s.startPos.get hne' := by
    rw [Slice.Pos.get, Slice.Pos.get]
    simp_all [Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, Slice.sliceTo, Slice.startPos, ne_eq]
    rfl
  rw [this]
  exact h hne'

theorem Slice.endsWith_dropWhile_of_endsWith_false (s : Slice) (p q : Char → Bool) (h : s.endsWith p = false) :
    (s.dropWhile q).endsWith p = false := by
  rw [Slice.endsWith_bool_eq_false_iff_get] at h ⊢
  intro hne
  have hne' : s.endPos ≠ s.startPos := by
    intro heq
    have h' : s.skipPrefixWhile q = s.endPos := by
      rw [heq, Slice.skipPrefixWhile_eq_skipWhile_startPos, Slice.Pattern.Model.Pos.skipWhile_eq_self]
      simp [String.Slice.Pattern.Model.CharPred.matchesAt_iff, Slice.Pattern.Model.CharPred.matchesAt_iff, heq]
    exact hne (Slice.Pos.ext (by simp [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, h']))
  have : ((s.dropWhile q).endPos.prev hne).get (by simp) = (s.endPos.prev hne').get (by simp) := by
    simp_all only [ne_eq, not_false_eq_true, Slice.Pos.get, Slice.Pos.get, Slice.dropWhile, Slice.sliceFrom, Slice.endPos, Slice.rawEndPos, Slice.Pos.prev, String.Pos.prev, Slice.Pos.offset, String.Pos.offset, Slice.utf8ByteSize_eq, Pos.Raw.byteIdx_offsetBy, Nat.add_sub_cancel', Nat.sub_add_cancel]
    rw []
    congr 1
    · simp_all only [Pos.offset_str, Pos.Raw.byteIdx_offsetBy]
      canonical
    · rfl
  simp [this]
  exact h hne'
--
-- /-! ### Main Theorems -/
--
-- attribute [local reducible] String.trimAscii String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd String.Slice.toString
--
-- theorem trimAscii_toString_startsWith_whitespace_false (s : String) :
--     s.trimAscii.toString.startsWith Char.isWhitespace = false := by
--   simp [startsWith_copy, Slice.startsWith_dropEndWhile_of_startsWith_false]
--
-- theorem trimAscii_toString_endsWith_whitespace_false (s : String) :
--     s.trimAscii.toString.endsWith Char.isWhitespace = false := by
--   simp [endsWith_copy]
