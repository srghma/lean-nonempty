module

import all Lean
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import all Init.Omega
import all Init.Data.String.Lemmas.TakeDrop
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Lemmas.IsEmpty

open String
public section
theorem Slice.startsWith_dropEndWhile_of_startsWith_false (s : Slice) (p q : Char → Bool) (h : s.startsWith p = false) :
    (s.dropEndWhile q).startsWith p = false := by
  rw [Slice.startsWith_bool_eq_false_iff_get] at h ⊢
  intro hne
  have hne' : s.startPos ≠ s.endPos := by
    intro heq
    have h' : s.skipSuffixWhile q = s.startPos := by
      rw [heq, Slice.skipSuffixWhile_eq_revSkipWhile_endPos, Slice.Pattern.Model.Pos.revSkipWhile_eq_self]
      simp only [Slice.Pattern.Model.CharPred.revMatchesAt_iff, heq, ne_eq, not_true_eq_false,
        not_exists, Bool.not_eq_true, forall_false]
    exact hne (Slice.Pos.ext (by simp only [Slice.offset_startPos, Slice.offset_endPos,
      Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile, h', Slice.rawEndPos_sliceTo]))
  have : (s.dropEndWhile q).startPos.get hne = s.startPos.get hne' := by
    rw [Slice.Pos.get, Slice.Pos.get]
    simp_all only [Slice.startPos, ne_eq, Slice.dropEndWhile_eq_sliceTo_skipSuffixWhile,
      Slice.sliceTo, Pos.Raw.byteIdx_zero, Nat.add_zero]
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
      simp only [Slice.Pattern.Model.CharPred.matchesAt_iff, heq, ne_eq, not_true_eq_false,
        not_exists, Bool.not_eq_true, forall_false]
    exact hne (Slice.Pos.ext (by simp only [Slice.offset_endPos,
      Slice.dropWhile_eq_sliceFrom_skipPrefixWhile, h', Slice.offset_startPos, Pos.Raw.eq_zero_iff,
      Slice.byteIdx_rawEndPos, Slice.utf8ByteSize_sliceFrom, Nat.sub_self]))
  have : ((s.dropWhile q).endPos.prev hne).get (by simp only [ne_eq, Slice.Pos.prev_ne_endPos,
    not_false_eq_true]) = (s.endPos.prev hne').get (by simp only [ne_eq, Slice.Pos.prev_ne_endPos,
      not_false_eq_true]) := by
    generalize h_trimmed : s.dropWhile q = trimmed at hne ⊢
    rw [Slice.dropWhile_eq_sliceFrom_skipPrefixWhile] at h_trimmed
    subst trimmed
    rw [Slice.Pos.get_eq_get_ofSliceFrom]
    congr 1
    rw [Slice.Pos.ofSliceFrom_prev]
    congr 1
    rw [Slice.Pos.ofSliceFrom_endPos]
  rw [this]
  exact h hne'

/-! ### Characterization of startsWith/endsWith for Char → Bool predicates -/

/-- `startsWith` for a char predicate checks if the first character satisfies the predicate. -/
theorem startsWith_charPred (p : Char → Bool) (s : Slice) :
    s.startsWith p =
    if h : s.startPos = s.endPos then false
    else p (s.startPos.get h) := by
  rfl

/-- `endsWith` for a char predicate checks if the last character satisfies the predicate. -/
theorem endsWith_charPred (p : Char → Bool) (s : Slice) :
    s.endsWith p =
    if h : s.endPos = s.startPos then false
    else p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos) := by
  rfl

/-! ### Characterization of skipPrefix?/skipSuffix? for Char → Bool predicates -/

/-- `skipPrefix?` for a char predicate: returns `some (next pos)` if first char matches,
    `none` otherwise. -/
theorem skipPrefix_charPred (p : Char → Bool) (s : Slice) :
    Slice.Pattern.ForwardPattern.skipPrefix? p s =
    if h : s.startPos = s.endPos then none
    else if p (s.startPos.get h) then some (s.startPos.next h)
    else none := by
  rfl

/-- `skipSuffix?` for a char predicate: returns `some (prev pos)` if last char matches,
    `none` otherwise. -/
theorem skipSuffix_charPred (p : Char → Bool) (s : Slice) :
    Slice.Pattern.BackwardPattern.skipSuffix? p s =
    if h : s.endPos = s.startPos then none
    else if p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos) then some (s.endPos.prev h)
    else none := by
  rfl

/-! ### Key connection: skipPrefix? = none ↔ startsWith = false for char predicates -/

theorem startsWith_false_of_skipPrefix_none {p : Char → Bool} {s : Slice}
    (h : Slice.Pattern.ForwardPattern.skipPrefix? p s = none) :
    s.startsWith p = false := by
  rw [startsWith_charPred, skipPrefix_charPred] at *
  split at h <;> simp_all

theorem endsWith_false_of_skipSuffix_none {p : Char → Bool} {s : Slice}
    (h : Slice.Pattern.BackwardPattern.skipSuffix? p s = none) :
    s.endsWith p = false := by
  rw [endsWith_charPred, skipSuffix_charPred] at *
  split at h <;> simp_all

/-! ### Bridge lemma: Slice.toString preserves startsWith/endsWith -/

theorem copy_toSlice_empty_iff (s : Slice) :
    (s.copy.toSlice.startPos = s.copy.toSlice.endPos) ↔ (s.startPos = s.endPos) := by
  simp only [Slice.startPos_eq_endPos_iff, String.isEmpty_toSlice, Slice.isEmpty_copy]

theorem copy_toSlice_empty_iff' (s : Slice) :
    (s.copy.toSlice.endPos = s.copy.toSlice.startPos) ↔ (s.endPos = s.startPos) := by
  constructor
  · intro h; exact (copy_toSlice_empty_iff s).mp h.symm |>.symm
  · intro h; exact ((copy_toSlice_empty_iff s).mpr h.symm).symm

/-- `Slice.toString` preserves `startsWith` for char predicates. -/
theorem Slice.startsWith_toString {p : Char → Bool} (s : Slice) :
    s.toString.startsWith p = s.startsWith p := by
  change s.copy.toSlice.startsWith p = s.startsWith p
  exact Slice.startsWith_copy

/-! ### Helper: ofSliceFrom/ofSliceTo preserve strict ordering -/

private theorem Slice.Pos.ofSliceFrom_lt_of_lt {s : Slice} {curr : s.Pos}
    {a b : (s.sliceFrom curr).Pos} (hab : a < b) :
    Slice.Pos.ofSliceFrom a < Slice.Pos.ofSliceFrom b := by
  rw [Slice.Pos.lt_iff] at hab ⊢
  simp only [Slice.Pos.ofSliceFrom]
  rw [Pos.Raw.lt_iff] at hab ⊢
  simp only [Pos.Raw.offsetBy]
  omega

private theorem Slice.Pos.ofSliceTo_lt_of_lt {s : Slice} {curr : s.Pos}
    {a b : (s.sliceTo curr).Pos} (hab : a < b) :
    Slice.Pos.ofSliceTo a < Slice.Pos.ofSliceTo b := by
  rw [Slice.Pos.ofSliceTo_lt_ofSliceTo_iff]; exact hab

theorem Slice.endsWith_toString {p : Char → Bool} (s : Slice) :
    s.toString.endsWith p = s.endsWith p := by
  change s.copy.toSlice.endsWith p = s.endsWith p
  exact Slice.endsWith_copy


/-! ### sliceTo preserves startsWith -/

/-- `sliceTo` only truncates the end, so `startsWith` is preserved. -/
theorem startsWith_sliceTo {p : Char → Bool} {s : Slice}
    (pos : s.Pos) (h : s.startsWith p = false) :
    (s.sliceTo pos).startsWith p = false := by
  rw [startsWith_charPred] at h ⊢
  match h_s : s.isEmpty with
  | true =>
    split
    · rfl
    · rename_i h_not_empty
      exfalso; apply h_not_empty
      rw [Slice.startPos_eq_endPos_iff, Slice.isEmpty_sliceTo]
      exact Slice.isEmpty_iff_forall_eq.mp h_s pos s.startPos
  | false =>
    split
    · rfl
    · rename_i h_sub
      simp only [Slice.Pos.get_eq_get_ofSliceTo, Slice.Pos.ofSliceTo_startPos]
      simp only [Slice.startPos_ne_endPos h_s, ↓reduceDIte] at h
      exact h

/-! ### Helper lemmas for monotonicity of position mappings -/

private theorem ofSliceFrom_strictMono {s : Slice} {pos : s.Pos}
    {a b : (s.sliceFrom pos).Pos} (h : a < b) :
    Slice.Pos.ofSliceFrom a < Slice.Pos.ofSliceFrom b := by
  rw [Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff]; exact h

private theorem ofSliceTo_strictMono {s : Slice} {pos : s.Pos}
    {a b : (s.sliceTo pos).Pos} (h : a < b) :
    Slice.Pos.ofSliceTo a < Slice.Pos.ofSliceTo b := by
  rw [Slice.Pos.ofSliceTo_lt_ofSliceTo_iff]; exact h



/-! ### Convenience theorems for trimAscii -/

/-- `trimAscii` removes leading whitespace, so the result does not start with whitespace. -/
theorem trimAscii_startsWith_whitespace_false (s : String) :
    s.trimAscii.startsWith Char.isWhitespace = false := by
  simp only [String.trimAscii, Slice.trimAscii, Slice.trimAsciiEnd, Slice.trimAsciiStart, Slice.dropEndWhile, Slice.dropWhile]
  apply startsWith_sliceTo
  exact Slice.startsWith_dropWhile

/-- `trimAscii` removes trailing whitespace, so the result does not end with whitespace. -/
theorem trimAscii_endsWith_whitespace_false (s : String) :
    s.trimAscii.endsWith Char.isWhitespace = false := by
  simp only [String.trimAscii, Slice.trimAscii, Slice.trimAsciiEnd, Slice.trimAsciiStart]
  exact Slice.endsWith_dropEndWhile

/-- The string obtained from `trimAscii.toString` does not start with whitespace. -/
theorem trimAscii_toString_startsWith_whitespace_false (s : String) :
    s.trimAscii.toString.startsWith Char.isWhitespace = false := by
  rw [Slice.startsWith_toString]
  exact trimAscii_startsWith_whitespace_false s

/-- The string obtained from `trimAscii.toString` does not end with whitespace. -/
theorem trimAscii_toString_endsWith_whitespace_false (s : String) :
    s.trimAscii.toString.endsWith Char.isWhitespace = false := by
  rw [Slice.endsWith_toString]
  exact trimAscii_endsWith_whitespace_false s

/-- `startsWith` for a char predicate on an appended string only depends on the first string if it's non-empty. -/
theorem startsWith_append_of_nonempty {p : Char → Bool} {s1 s2 : String} (h : s1 ≠ "") :
    (s1 ++ s2).startsWith p = s1.startsWith p := by
  rw [startsWith_bool_eq_head?, startsWith_bool_eq_head?, String.toList_append]
  have : s1.toList ≠ [] := by
    intro h_nil
    apply h; exact toList_eq_nil_iff.mp h_nil
  match h_list : s1.toList with
  | [] => exfalso; apply this; exact h_list
  | c :: cs => simp

/-- `endsWith` for a char predicate on an appended string only depends on the second string if it's non-empty. -/
theorem endsWith_append_of_nonempty {p : Char → Bool} {s1 s2 : String} (h : s2 ≠ "") :
    (s1 ++ s2).endsWith p = s2.endsWith p := by
  rw [endsWith_bool_eq_getLast?, endsWith_bool_eq_getLast?, String.toList_append]
  have : s2.toList ≠ [] := by
    intro h_nil
    apply h; exact toList_eq_nil_iff.mp h_nil
  rw [List.getLast?_append]
  match h_last : s2.toList.getLast? with
  | none => exfalso; apply this; exact List.getLast?_eq_none_iff.mp h_last
  | some c => simp
