import Lean

open String

/-! ### Custom tactic to unfold private `dropWhile.go` and `dropEndWhile.go` -/

open Lean Meta Elab Tactic in
elab "unfold_private" n:ident : tactic => do
  let s := n.getId.toString
  let name : Name := match s with
    | "dropWhile_go" => .str (.str (.str (.str (.num (.str (.str (.str (.str (.str .anonymous "_private") "Init") "Data") "String") "Slice") 0) "String") "Slice") "dropWhile") "go"
    | "dropEndWhile_go" => .str (.str (.str (.str (.num (.str (.str (.str (.str (.str .anonymous "_private") "Init") "Data") "String") "Slice") 0) "String") "Slice") "dropEndWhile") "go"
    | _ => .anonymous
  liftMetaTactic fun mvarId => do
    let target ← mvarId.getType
    let target' ← deltaExpand target (· == name)
    let mvarId' ← mvarId.replaceTargetDefEq target'
    return [mvarId']

/-! ### Characterization: startsWith/endsWith for Char → Bool via front?/back? -/

set_option maxHeartbeats 6400000 in
theorem startsWith_charPred (p : Char → Bool) (s : Slice) :
    s.startsWith p = match s.front? with | some c => p c | none => false := by
  simp only [Slice.startsWith,
    Slice.Pattern.ForwardCharPredSearcher.instForwardPatternForallCharBool,
    Slice.Pattern.ForwardPattern.defaultImplementation,
    Slice.Pattern.ForwardPattern.defaultStartsWith,
    Slice.Pattern.ForwardCharPredSearcher.instToForwardSearcherForallCharBool,
    Slice.Pattern.ToForwardSearcher.toSearcher,
    Slice.Pattern.ForwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure,
    Slice.front?, Slice.Pos.get?]
  by_cases h : s.startPos = s.endPos
  · simp only [h, dif_pos, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [h, dite_false]
    by_cases hp : p (s.startPos.get h) = true
    · simp only [hp, dite_true, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, decide_true]
    · have hp' : p (s.startPos.get h) = false := by cases h' : p (s.startPos.get h) <;> simp_all
      simp only [hp', Bool.false_eq_true, dite_false, Std.Shrink.inflate_deflate,
        Std.IterM.Step.toPure_yield]

set_option maxHeartbeats 6400000 in
theorem endsWith_charPred (p : Char → Bool) (s : Slice) :
    s.endsWith p = match s.back? with | some c => p c | none => false := by
  simp only [Slice.endsWith,
    Slice.Pattern.BackwardPattern.endsWith,
    Slice.Pattern.BackwardCharPredSearcher.instBackwardPatternForallCharBool,
    Slice.Pattern.ToBackwardSearcher.defaultImplementation,
    Slice.Pattern.ToBackwardSearcher.defaultEndsWith,
    Slice.Pattern.BackwardCharPredSearcher.instToBackwardSearcherForallCharBool,
    Slice.Pattern.ToBackwardSearcher.toSearcher,
    Slice.Pattern.BackwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure,
    Slice.back?, Slice.Pos.prev?, Slice.Pos.get?]
  by_cases h : s.endPos = s.startPos
  · simp only [h, dif_pos, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]; rfl
  · simp only [h, dite_false, Option.bind_some]
    have ne_ep : ¬ (s.endPos.prev h = s.endPos) := Slice.Pos.prev_ne_endPos
    simp only [ne_ep, dite_false]
    by_cases hp : p ((s.endPos.prev h).get ne_ep) = true
    · simp only [hp, dite_true, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, decide_true]
    · have hp' : p ((s.endPos.prev h).get ne_ep) = false := by
        cases h' : p ((s.endPos.prev h).get ne_ep) <;> simp_all
      simp only [hp', Bool.false_eq_true, dite_false, Std.Shrink.inflate_deflate,
        Std.IterM.Step.toPure_yield]

/-! ### Pattern framework: dropPrefix?/dropSuffix? ↔ startsWith/endsWith -/

set_option maxHeartbeats 6400000 in
theorem dropPrefix?_none_iff_not_startsWith (p : Char → Bool) (s : Slice) :
    Slice.Pattern.ForwardPattern.dropPrefix? p s = none ↔ s.startsWith p = false := by
  simp only [Slice.startsWith,
    Slice.Pattern.ForwardCharPredSearcher.instForwardPatternForallCharBool,
    Slice.Pattern.ForwardPattern.defaultImplementation,
    Slice.Pattern.ForwardPattern.defaultStartsWith,
    Slice.Pattern.ForwardPattern.defaultDropPrefix?,
    Slice.Pattern.ForwardCharPredSearcher.instToForwardSearcherForallCharBool,
    Slice.Pattern.ToForwardSearcher.toSearcher,
    Slice.Pattern.ForwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure]
  by_cases he : s.startPos = s.endPos
  · simp [he, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [he, dite_false]
    by_cases hp : p (s.startPos.get he) = true
    · simp [hp, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield]
    · have hp' : p (s.startPos.get he) = false := Bool.eq_false_iff.mpr (by simp [hp])
      simp [hp', Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield]

set_option maxHeartbeats 6400000 in
theorem dropSuffix?_none_iff_not_endsWith (p : Char → Bool) (s : Slice) :
    Slice.Pattern.BackwardPattern.dropSuffix? p s = none ↔ s.endsWith p = false := by
  simp only [Slice.endsWith,
    Slice.Pattern.BackwardCharPredSearcher.instBackwardPatternForallCharBool,
    Slice.Pattern.ToBackwardSearcher.defaultImplementation,
    Slice.Pattern.ToBackwardSearcher.defaultEndsWith,
    Slice.Pattern.ToBackwardSearcher.defaultDropSuffix?,
    Slice.Pattern.BackwardCharPredSearcher.instToBackwardSearcherForallCharBool,
    Slice.Pattern.ToBackwardSearcher.toSearcher,
    Slice.Pattern.BackwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure]
  by_cases he : s.endPos = s.startPos
  · simp [he, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [he, dite_false]
    by_cases hp : p ((s.endPos.prev he).get Slice.Pos.prev_ne_endPos) = true
    · simp [hp, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield]
    · have hp' : p ((s.endPos.prev he).get Slice.Pos.prev_ne_endPos) = false :=
        Bool.eq_false_iff.mpr (by simp [hp])
      simp [hp', Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield]

/-! ### Char predicate patterns always advance/retreat -/

set_option maxHeartbeats 12800000 in
theorem charPred_dropPrefix?_advances (p : Char → Bool) (s : Slice) (curr : s.Pos)
    (nextCurr : (s.sliceFrom curr).Pos)
    (h : Slice.Pattern.ForwardPattern.dropPrefix? p (s.sliceFrom curr) = some nextCurr) :
    curr < Slice.Pos.ofSliceFrom nextCurr := by
  simp only [Slice.Pattern.ForwardCharPredSearcher.instForwardPatternForallCharBool,
    Slice.Pattern.ForwardPattern.defaultImplementation,
    Slice.Pattern.ForwardPattern.defaultDropPrefix?,
    Slice.Pattern.ForwardCharPredSearcher.instToForwardSearcherForallCharBool,
    Slice.Pattern.ToForwardSearcher.toSearcher,
    Slice.Pattern.ForwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure] at h
  by_cases he : (s.sliceFrom curr).startPos = (s.sliceFrom curr).endPos
  · simp [he, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done] at h
  · simp only [he, dite_false] at h
    by_cases hp : p ((s.sliceFrom curr).startPos.get he) = true
    · simp [hp, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield] at h
      subst h
      have h1 := @Slice.Pos.lt_next (s.sliceFrom curr) (s.sliceFrom curr).startPos he
      rw [Slice.Pos.lt_iff] at h1 ⊢
      rw [Pos.Raw.lt_iff] at h1 ⊢
      simp only [Slice.Pos.ofSliceFrom, Pos.Raw.offsetBy]
      have h0 : (s.sliceFrom curr).startPos.offset.byteIdx = 0 := by
        simp [Slice.startPos, Slice.sliceFrom]
      omega
    · have hp' : p ((s.sliceFrom curr).startPos.get he) = false := Bool.eq_false_iff.mpr (by simp [hp])
      simp [hp', Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield] at h

set_option maxHeartbeats 12800000 in
theorem charPred_dropSuffix?_retreats (p : Char → Bool) (s : Slice) (curr : s.Pos)
    (nextCurr : (s.sliceTo curr).Pos)
    (h : Slice.Pattern.BackwardPattern.dropSuffix? p (s.sliceTo curr) = some nextCurr) :
    Slice.Pos.ofSliceTo nextCurr < curr := by
  simp only [Slice.Pattern.BackwardCharPredSearcher.instBackwardPatternForallCharBool,
    Slice.Pattern.ToBackwardSearcher.defaultImplementation,
    Slice.Pattern.ToBackwardSearcher.defaultDropSuffix?,
    Slice.Pattern.BackwardCharPredSearcher.instToBackwardSearcherForallCharBool,
    Slice.Pattern.ToBackwardSearcher.toSearcher,
    Slice.Pattern.BackwardCharPredSearcher.iter,
    Std.Iter.step, Std.IterM.step, Std.Iter.toIterM, Id.run,
    Std.Iterator.step, Pure.pure] at h
  by_cases he : (s.sliceTo curr).endPos = (s.sliceTo curr).startPos
  · simp [he, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done] at h
  · simp only [he, dite_false] at h
    by_cases hp : p (((s.sliceTo curr).endPos.prev he).get Slice.Pos.prev_ne_endPos) = true
    · simp [hp, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield] at h
      subst h
      have h_prev := @Slice.Pos.prev_lt (s.sliceTo curr) (s.sliceTo curr).endPos he
      rw [Slice.Pos.lt_iff] at h_prev ⊢
      rw [Pos.Raw.lt_iff] at h_prev ⊢
      simp only [Slice.Pos.ofSliceTo]
      have h_eq : (s.sliceTo curr).endPos.offset.byteIdx = curr.offset.byteIdx := by
        simp [Slice.endPos, Slice.rawEndPos]
      omega
    · have hp' : p (((s.sliceTo curr).endPos.prev he).get Slice.Pos.prev_ne_endPos) = false :=
        Bool.eq_false_iff.mpr (by simp [hp])
      simp [hp', Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield] at h

/-! ### dropWhile/dropEndWhile: main correctness properties -/

set_option maxHeartbeats 25600000 in
theorem dropWhile_not_startsWith_charPred (p : Char → Bool) (s : Slice) :
    (s.dropWhile p).startsWith p = false := by
  unfold Slice.dropWhile
  generalize s.startPos = curr
  unfold_private dropWhile_go
  induction curr using (Slice.Pos.instWellFoundedRelation (s := s)).wf.recursion with
  | _ curr ih =>
    rw [WellFounded.fix_eq]
    split
    · rename_i nextCurr h_match
      split
      · rename_i h_lt; exact ih _ h_lt
      · rename_i h_nlt
        exfalso; apply h_nlt
        exact charPred_dropPrefix?_advances p s curr nextCurr h_match
    · rename_i h_match
      exact (dropPrefix?_none_iff_not_startsWith p (s.sliceFrom curr)).mp
        (by simp [Option.eq_none_iff_forall_not_mem]; exact h_match)

set_option maxHeartbeats 25600000 in
theorem dropEndWhile_not_endsWith_charPred (p : Char → Bool) (s : Slice) :
    (s.dropEndWhile p).endsWith p = false := by
  unfold Slice.dropEndWhile
  generalize s.endPos = curr
  unfold_private dropEndWhile_go
  have hwf : WellFounded (fun (a b : s.Pos) => a < b) :=
    InvImage.wf Slice.Pos.down (Slice.Pos.instWellFoundedRelationDown).wf
  induction curr using hwf.recursion with
  | _ curr ih =>
    rw [WellFounded.fix_eq]
    split
    · rename_i nextCurr h_match
      split
      · rename_i h_lt; exact ih _ h_lt
      · rename_i h_nlt
        exfalso; apply h_nlt
        exact charPred_dropSuffix?_retreats p s curr nextCurr h_match
    · rename_i h_match
      exact (dropSuffix?_none_iff_not_endsWith p (s.sliceTo curr)).mp
        (by simp [Option.eq_none_iff_forall_not_mem]; exact h_match)

/-! ### sliceTo preserves startsWith = false -/

set_option maxHeartbeats 6400000 in
theorem startsWith_false_of_sliceTo (p : Char → Bool) (s : Slice) (pos : s.Pos)
    (h : s.startsWith p = false) :
    (s.sliceTo pos).startsWith p = false := by
  rw [startsWith_charPred] at h ⊢
  simp only [Slice.front?, Slice.Pos.get?] at h ⊢
  by_cases h1 : (s.sliceTo pos).startPos = (s.sliceTo pos).endPos
  · simp [h1]
  · simp only [h1, dite_false]
    by_cases h2 : s.startPos = s.endPos
    · exfalso; apply h1
      have h_le := pos.isValidForSlice.le_rawEndPos
      rw [Slice.Pos.ext_iff] at h2 ⊢
      simp only [Slice.startPos, Slice.endPos, Slice.rawEndPos] at h2 ⊢
      simp only [Slice.sliceTo, Slice.utf8ByteSize, Pos.Raw.byteDistance,
        Slice.Pos.str, Pos.Raw.offsetBy] at ⊢
      rw [Pos.Raw.ext_iff] at h2 ⊢
      simp only [Slice.rawEndPos, Slice.utf8ByteSize, Pos.Raw.byteDistance] at h2 h_le
      rw [Pos.Raw.le_iff] at h_le
      have h_se := s.startInclusive_le_endExclusive
      rw [String.Pos.le_iff, Pos.Raw.le_iff] at h_se
      -- The goal and h2 are about Pos.Raw equality, but omega needs Nat
      -- h2 : Pos.Raw.byteIdx 0 = endExclusive - startInclusive  (in Pos.Raw form)
      -- h_le : pos.offset.byteIdx ≤ rawEndPos.byteIdx
      -- h_se : startInclusive.byteIdx ≤ endExclusive.byteIdx
      -- Goal: Pos.Raw.byteIdx 0 = { byteIdx := start + pos - start }.byteIdx
      -- i.e., 0 = start + pos - start = pos.offset.byteIdx
      -- which is true because pos.offset.byteIdx = 0
      -- h_le (after simp) is pos.offset.byteIdx ≤ something
      -- h2 (rewritten): that something = 0
      -- so pos.offset.byteIdx = 0
      -- goal reduces to 0 = 0
      suffices pos.offset.byteIdx = 0 by simp [this]
      have h2n : s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx = 0 := by
        have := h2; exact this.symm
      have h_len : pos.offset.byteIdx ≤ s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx := by
        simpa using h_le
      omega
    · simp only [h2, dite_false] at h
      have : (s.sliceTo pos).startPos.get h1 = s.startPos.get h2 := by
        simp [Slice.Pos.get, Slice.startPos, Slice.sliceTo]
      rw [this]; exact h

/-! ### dropEndWhile preserves startsWith = false -/

set_option maxHeartbeats 25600000 in
theorem startsWith_false_of_dropEndWhile (p q : Char → Bool) (s : Slice)
    (h : s.startsWith p = false) :
    (s.dropEndWhile q).startsWith p = false := by
  unfold Slice.dropEndWhile
  generalize s.endPos = curr
  unfold_private dropEndWhile_go
  have hwf : WellFounded (fun (a b : s.Pos) => a < b) :=
    InvImage.wf Slice.Pos.down (Slice.Pos.instWellFoundedRelationDown).wf
  induction curr using hwf.recursion with
  | _ curr ih =>
    rw [WellFounded.fix_eq]
    split
    · rename_i nextCurr _
      split
      · rename_i h_lt; exact ih _ h_lt
      · exact startsWith_false_of_sliceTo p s _ h
    · exact startsWith_false_of_sliceTo p s _ h

/-! ### trimAscii: Slice-level theorems -/

theorem trimAscii_startsWith_whitespace_false (s : String) :
    s.trimAscii.startsWith Char.isWhitespace = false := by
  show s.toSlice.trimAscii.startsWith Char.isWhitespace = false
  unfold Slice.trimAscii Slice.trimAsciiStart Slice.trimAsciiEnd
  exact startsWith_false_of_dropEndWhile _ _ _
    (dropWhile_not_startsWith_charPred Char.isWhitespace s.toSlice)

theorem trimAscii_endsWith_whitespace_false (s : String) :
    s.trimAscii.endsWith Char.isWhitespace = false := by
  show s.toSlice.trimAscii.endsWith Char.isWhitespace = false
  unfold Slice.trimAscii Slice.trimAsciiStart Slice.trimAsciiEnd
  exact dropEndWhile_not_endsWith_charPred Char.isWhitespace _

/-! ### Bridge: copy preserves front?/back? -/

theorem front?_copy_toSlice (s : Slice) :
    s.copy.toSlice.front? = s.front? := by
  simp [Slice.front?]
  simp [Slice.Pos.get?]
  grind +suggestions

set_option maxHeartbeats 6400000 in
theorem rawEndPos_copy_toSlice (s : Slice) :
    s.copy.toSlice.rawEndPos = s.rawEndPos := by
  simp [Slice.rawEndPos, Slice.utf8ByteSize, String.toSlice, Slice.copy,
        Pos.Raw.byteDistance, String.rawEndPos]
  exact Slice.utf8ByteSize_copy

set_option maxHeartbeats 6400000 in
theorem getUTF8Byte_copy_toSlice (s : Slice) (p : String.Pos.Raw)
    (h1 : p < s.copy.toSlice.rawEndPos) (h2 : p < s.rawEndPos) :
    s.copy.toSlice.getUTF8Byte p h1 = s.getUTF8Byte p h2 := by
  unfold Slice.getUTF8Byte
  simp [Pos.Raw.offsetBy]
  rw [Slice.getUTF8Byte_copy]
  simp [Slice.getUTF8Byte, Pos.Raw.offsetBy]

set_option maxHeartbeats 25600000 in
theorem prevAux_go_copy_toSlice (s : Slice) (off : Nat)
    (h1 : off < s.copy.toSlice.utf8ByteSize) (h2 : off < s.utf8ByteSize) :
    Slice.Pos.prevAux.go (s := s.copy.toSlice) off h1 = Slice.Pos.prevAux.go (s := s) off h2 := by
  induction off using Nat.strongRecOn with
  | _ off ih =>
    rw [Slice.Pos.prevAux.go.eq_1 (s := s.copy.toSlice)]
    rw [Slice.Pos.prevAux.go.eq_1 (s := s)]
    have hbyte : s.copy.toSlice.getUTF8Byte { byteIdx := off } h1 = s.getUTF8Byte { byteIdx := off } h2 := by
      apply getUTF8Byte_copy_toSlice
    by_cases hfb : (s.getUTF8Byte { byteIdx := off } h2).IsUTF8FirstByte
    · have hfb' : (s.copy.toSlice.getUTF8Byte { byteIdx := off } h1).IsUTF8FirstByte := by
        rw [hbyte]; exact hfb
      simp [hfb, hfb']
    · have hfb' : ¬(s.copy.toSlice.getUTF8Byte { byteIdx := off } h1).IsUTF8FirstByte := by
        rw [hbyte]; exact hfb
      simp only [hfb, dite_false, hfb']
      match off with
      | 0 => simp
      | off' + 1 => exact ih off' (by omega) _ _

set_option maxHeartbeats 25600000 in
theorem back?_copy_toSlice (s : Slice) :
    s.copy.toSlice.back? = s.back? := by
  simp only [Slice.back?, Slice.Pos.prev?, Slice.Pos.get?]
  have hep : s.copy.toSlice.endPos = (s.endPos.copy).toSlice := by
    rw [endPos_toSlice, Slice.endPos_copy]
  have hsp : s.copy.toSlice.startPos = (s.startPos.copy).toSlice := by
    rw [startPos_toSlice, Slice.startPos_copy]
  by_cases h : s.endPos = s.startPos
  · have h' : s.copy.toSlice.endPos = s.copy.toSlice.startPos := by
      rw [hep, hsp]; congr 1; exact Slice.Pos.copy_inj.mpr h
    simp [h, h']
  · have h' : s.copy.toSlice.endPos ≠ s.copy.toSlice.startPos := by
      rw [hep, hsp]
      intro heq
      exact h (Slice.Pos.copy_inj.mp (Pos.toSlice_inj.mp heq))
    simp only [h, dite_false, h', Option.bind_some]
    have hpne : s.copy.toSlice.endPos.prev h' ≠ s.copy.toSlice.endPos :=
      Slice.Pos.prev_ne_endPos
    have hpne2 : s.endPos.prev h ≠ s.endPos :=
      Slice.Pos.prev_ne_endPos
    simp only [hpne, dite_false, hpne2]
    -- Prove the prev positions have the same offset
    have hoff : (s.copy.toSlice.endPos.prev h').offset = (s.endPos.prev h).offset := by
      simp only [Slice.Pos.prev, Slice.Pos.prevAux]
      rw [Pos.Raw.ext_iff]
      simp
      exact congrArg Pos.Raw.byteIdx (prevAux_go_copy_toSlice s _ _ _)
    -- Prove the prev positions are equal (in s.copy.toSlice)
    have pos_eq : s.copy.toSlice.endPos.prev h' = (s.endPos.prev h).copy.toSlice := by
      apply Slice.Pos.ext
      rw [hoff, Pos.offset_toSlice, Slice.Pos.offset_copy]
    -- Chain: get on copy.toSlice = get on original (via Pos.get_toSlice and Slice.Pos.get_copy)
    have hpne' : (s.endPos.prev h).copy.toSlice ≠ s.copy.toSlice.endPos :=
      pos_eq ▸ hpne
    have step1 : (s.copy.toSlice.endPos.prev h').get hpne
               = ((s.endPos.prev h).copy.toSlice).get hpne' := by
      congr 1
    rw [step1, Pos.get_toSlice, Slice.Pos.get_copy]

theorem startsWith_slice_toString (p : Char → Bool) (sl : Slice) :
    sl.toString.startsWith p = sl.startsWith p := by
  show sl.copy.toSlice.startsWith p = sl.startsWith p
  rw [startsWith_charPred p sl.copy.toSlice, front?_copy_toSlice, ← startsWith_charPred]

theorem endsWith_slice_toString (p : Char → Bool) (sl : Slice) :
    sl.toString.endsWith p = sl.endsWith p := by
  show sl.copy.toSlice.endsWith p = sl.endsWith p
  rw [endsWith_charPred p sl.copy.toSlice, back?_copy_toSlice, ← endsWith_charPred]

/-! ### Main: trimAscii's toString has no surrounding whitespace -/

theorem trimAscii_toString_startsWith_whitespace_false (s : String) :
    s.trimAscii.toString.startsWith Char.isWhitespace = false := by
  rw [startsWith_slice_toString]
  exact trimAscii_startsWith_whitespace_false s

theorem trimAscii_toString_endsWith_whitespace_false (s : String) :
    s.trimAscii.toString.endsWith Char.isWhitespace = false := by
  rw [endsWith_slice_toString]
  exact trimAscii_endsWith_whitespace_false s

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