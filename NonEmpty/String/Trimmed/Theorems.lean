import Lean

open String

/-! ### Idempotence: trimming a slice that is already trimmed is a no-op -/

theorem skipPrefixWhile_eq_startPos_of_not_startsWith {p : Char → Bool} (s : Slice) (h : s.startsWith p = false) :
    s.skipPrefixWhile p = s.startPos := by
  unfold Slice.skipPrefixWhile Slice.Pos.skipWhile
  have h_none : Slice.Pattern.ForwardPattern.skipPrefix? p (s.sliceFrom s.startPos) = none := by
    rw [Slice.sliceFrom_startPos, ← Slice.skipPrefix?_eq_forwardPatternSkipPrefix?, Slice.skipPrefix?_eq_none_iff]
    exact h
  split
  · rename_i nextCurr h_some
    rw [h_none] at h_some
    contradiction
  · rfl

theorem dropWhile_eq_self_of_not_startsWith {p : Char → Bool} (s : Slice) (h : s.startsWith p = false) :
    s.dropWhile p = s := by
  rw [Slice.dropWhile, skipPrefixWhile_eq_startPos_of_not_startsWith s h]
  rw [Slice.sliceFrom_startPos]

theorem trimAsciiStartSlice_eq_self_of_not_startsWith {s : Slice} (h : s.startsWith Char.isWhitespace = false) :
    s.trimAsciiStart = s :=
  dropWhile_eq_self_of_not_startsWith s h

theorem trimAsciiStart_eq_self_of_not_startsWith (s : String) (h : s.startsWith Char.isWhitespace = false) :
    s.trimAsciiStart = s.toSlice := by
  unfold trimAsciiStart
  rw [startsWith_eq_startsWith_toSlice] at h
  exact trimAsciiStartSlice_eq_self_of_not_startsWith h

theorem skipSuffixWhile_eq_endPos_of_not_endsWith {p : Char → Bool} (s : Slice) (h : s.endsWith p = false) :
    s.skipSuffixWhile p = s.endPos := by
  unfold Slice.skipSuffixWhile Slice.Pos.revSkipWhile
  have h_none : Slice.Pattern.BackwardPattern.skipSuffix? p (s.sliceTo s.endPos) = none := by
    rw [Slice.sliceTo_endPos, ← Slice.skipSuffix?_eq_backwardPatternSkipSuffix?, Slice.skipSuffix?_eq_none_iff]
    exact h
  split
  · rename_i nextCurr h_some
    rw [h_none] at h_some
    contradiction
  · rfl

theorem dropEndWhile_eq_self_of_not_endsWith {p : Char → Bool} (s : Slice) (h : s.endsWith p = false) :
    s.dropEndWhile p = s := by
  rw [Slice.dropEndWhile, skipSuffixWhile_eq_endPos_of_not_endsWith s h]
  rw [Slice.sliceTo_endPos]

theorem trimAsciiEndSlice_eq_self_of_not_endsWith {s : Slice} (h : s.endsWith Char.isWhitespace = false) :
    s.trimAsciiEnd = s :=
  dropEndWhile_eq_self_of_not_endsWith s h

theorem trimAsciiEnd_eq_self_of_not_endsWith (s : String) (h : s.endsWith Char.isWhitespace = false) :
    s.trimAsciiEnd = s.toSlice := by
  unfold trimAsciiEnd
  rw [endsWith_eq_endsWith_toSlice] at h
  exact trimAsciiEndSlice_eq_self_of_not_endsWith h

theorem trimAsciiSlice_eq_self_of_not_starts_ends {s : Slice} (h1 : s.startsWith Char.isWhitespace = false) (h2 : s.endsWith Char.isWhitespace = false) :
    s.trimAscii = s := by
  unfold Slice.trimAscii
  rw [trimAsciiStartSlice_eq_self_of_not_startsWith h1]
  exact trimAsciiEndSlice_eq_self_of_not_endsWith h2

theorem trimAscii_eq_self_of_not_starts_ends (s : String) (h1 : s.startsWith Char.isWhitespace = false) (h2 : s.endsWith Char.isWhitespace = false) :
    s.trimAscii = s.toSlice := by
  unfold trimAscii
  rw [startsWith_eq_startsWith_toSlice] at h1
  rw [endsWith_eq_endsWith_toSlice] at h2
  exact trimAsciiSlice_eq_self_of_not_starts_ends h1 h2

/-! ### Helper lemmas for monotonicity of position mappings -/

private theorem ofSliceFrom_strictMono {s : Slice} {pos : s.Pos}
    {a b : (s.sliceFrom pos).Pos} (h : a < b) :
    Slice.Pos.ofSliceFrom a < Slice.Pos.ofSliceFrom b := by
  have ha : (Slice.Pos.ofSliceFrom a).offset.byteIdx = pos.offset.byteIdx + a.offset.byteIdx := by
    simp [Slice.Pos.ofSliceFrom, Pos.Raw.offsetBy]
  have hb : (Slice.Pos.ofSliceFrom b).offset.byteIdx = pos.offset.byteIdx + b.offset.byteIdx := by
    simp [Slice.Pos.ofSliceFrom, Pos.Raw.offsetBy]
  rw [Slice.Pos.lt_iff, Pos.Raw.lt_iff, ha, hb]
  rw [Slice.Pos.lt_iff, Pos.Raw.lt_iff] at h
  omega

private theorem ofSliceTo_strictMono {s : Slice} {pos : s.Pos}
    {a b : (s.sliceTo pos).Pos} (h : a < b) :
    Slice.Pos.ofSliceTo a < Slice.Pos.ofSliceTo b := by
  have ha : (Slice.Pos.ofSliceTo a).offset.byteIdx = a.offset.byteIdx := by
    simp [Slice.Pos.ofSliceTo]
  have hb : (Slice.Pos.ofSliceTo b).offset.byteIdx = b.offset.byteIdx := by
    simp [Slice.Pos.ofSliceTo]
  rw [Slice.Pos.lt_iff, Pos.Raw.lt_iff, ha, hb]
  rw [Slice.Pos.lt_iff, Pos.Raw.lt_iff] at h
  exact h

/-! ### Progress lemmas: skipPrefix?/skipSuffix? always advance for Char → Bool -/

private theorem skipPrefix_charPred_progress {p : Char → Bool} {s : Slice} {pos : s.Pos}
    {nextCurr : (s.sliceFrom pos).Pos}
    (h : Slice.Pattern.ForwardPattern.skipPrefix? p (s.sliceFrom pos) = some nextCurr) :
    pos < Slice.Pos.ofSliceFrom nextCurr := by
  have eq_def : Slice.Pattern.ForwardPattern.skipPrefix? p (s.sliceFrom pos) =
    (if h : (s.sliceFrom pos).startPos = (s.sliceFrom pos).endPos then none
     else if p ((s.sliceFrom pos).startPos.get h) = true then some ((s.sliceFrom pos).startPos.next h) else none) := rfl
  rw [eq_def] at h
  split at h
  · simp at h
  · rename_i h_ne
    split at h
    · rename_i h_p
      have h_eq : nextCurr = (s.sliceFrom pos).startPos.next h_ne := Option.some.inj h.symm
      subst h_eq
      have h1 : Slice.Pos.ofSliceFrom (s.sliceFrom pos).startPos = pos := Slice.Pos.ofSliceFrom_startPos
      have h2 : (s.sliceFrom pos).startPos < (s.sliceFrom pos).startPos.next h_ne := Slice.Pos.lt_next
      calc pos = Slice.Pos.ofSliceFrom (s.sliceFrom pos).startPos := h1.symm
        _ < Slice.Pos.ofSliceFrom ((s.sliceFrom pos).startPos.next h_ne) := ofSliceFrom_strictMono h2
    · simp at h

private theorem skipSuffix_charPred_progress {p : Char → Bool} {s : Slice} {pos : s.Pos}
    {nextCurr : (s.sliceTo pos).Pos}
    (h : Slice.Pattern.BackwardPattern.skipSuffix? p (s.sliceTo pos) = some nextCurr) :
    Slice.Pos.ofSliceTo nextCurr < pos := by
  have eq_def : Slice.Pattern.BackwardPattern.skipSuffix? p (s.sliceTo pos) =
    (if h : (s.sliceTo pos).endPos = (s.sliceTo pos).startPos then none
     else if p (((s.sliceTo pos).endPos.prev h).get (Slice.Pos.prev_ne_endPos)) = true
       then some ((s.sliceTo pos).endPos.prev h) else none) := rfl
  rw [eq_def] at h
  split at h
  · simp at h
  · rename_i h_ne
    split at h
    · rename_i h_p
      have h_eq : nextCurr = (s.sliceTo pos).endPos.prev h_ne := Option.some.inj h.symm
      subst h_eq
      have h1 : Slice.Pos.ofSliceTo (s.sliceTo pos).endPos = pos := Slice.Pos.ofSliceTo_endPos
      have h2 : (s.sliceTo pos).endPos.prev h_ne < (s.sliceTo pos).endPos := Slice.Pos.prev_lt
      calc Slice.Pos.ofSliceTo ((s.sliceTo pos).endPos.prev h_ne)
          < Slice.Pos.ofSliceTo (s.sliceTo pos).endPos := ofSliceTo_strictMono h2
        _ = pos := h1
    · simp at h

/-! ### Main theorems: dropWhile removes the pattern from the start, dropEndWhile from the end -/

theorem dropWhile_startsWith_false {p : Char → Bool} (s : Slice) :
    (s.dropWhile p).startsWith p = false := by
  unfold Slice.dropWhile Slice.skipPrefixWhile
  suffices h : ∀ (pos : s.Pos), (s.sliceFrom (pos.skipWhile p)).startsWith p = false from h s.startPos
  intro pos
  induction pos using (Slice.Pos.instWellFoundedRelation (s := s)).wf.induction with
  | h pos ih =>
    rw [Slice.Pos.skipWhile.eq_def]
    cases h_eq : Slice.Pattern.ForwardPattern.skipPrefix? p (s.sliceFrom pos) with
    | none =>
      simp
      rw [Slice.startsWith, Slice.Pattern.LawfulForwardPattern.startsWith_eq]
      simp [h_eq]
    | some nextCurr =>
      simp
      split
      · rename_i h_lt
        exact ih _ h_lt
      · rename_i h_nlt
        exact absurd (skipPrefix_charPred_progress h_eq) h_nlt

theorem dropEndWhile_endsWith_false {p : Char → Bool} (s : Slice) :
    (s.dropEndWhile p).endsWith p = false := by
  unfold Slice.dropEndWhile Slice.skipSuffixWhile
  suffices h : ∀ (pos : s.Pos), (s.sliceTo (pos.revSkipWhile p)).endsWith p = false from h s.endPos
  intro pos
  -- Use Nat strong induction on the byte offset (since WF relation goes the wrong way for revSkipWhile)
  have : ∀ n, ∀ (pos : s.Pos), pos.offset.byteIdx = n → (s.sliceTo (pos.revSkipWhile p)).endsWith p = false := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro pos h_n
      rw [Slice.Pos.revSkipWhile.eq_def]
      cases h_eq : Slice.Pattern.BackwardPattern.skipSuffix? p (s.sliceTo pos) with
      | none =>
        simp
        rw [Slice.endsWith, Slice.Pattern.LawfulBackwardPattern.endsWith_eq]
        simp [h_eq]
      | some nextCurr =>
        simp
        split
        · rename_i h_lt
          have h_lt_nat : (Slice.Pos.ofSliceTo nextCurr).offset.byteIdx < n := by
            rw [← h_n]
            rw [Slice.Pos.lt_iff, Pos.Raw.lt_iff] at h_lt
            exact h_lt
          exact ih _ h_lt_nat _ rfl
        · rename_i h_nlt
          exact absurd (skipSuffix_charPred_progress h_eq) h_nlt
  exact this _ _ rfl

/-! ### sliceTo preserves startsWith -/

theorem startsWith_sliceTo {p : Char → Bool} {s : Slice}
    (pos : s.Pos) (h : s.startsWith p = false) :
    (s.sliceTo pos).startsWith p = false := by
  have eq : ∀ (t : Slice), t.startsWith p =
    (if h : t.startPos = t.endPos then false else p (t.startPos.get h)) := fun _ => rfl
  rw [eq]; split
  · rfl
  · rename_i h_ne
    rw [eq] at h; split at h
    · rename_i h_eq
      exfalso; apply h_ne
      have h1 := Slice.Pos.startPos_le pos
      have h2 := Slice.Pos.le_endPos pos
      rw [h_eq] at h1
      have h_pos : pos = s.endPos := Slice.Pos.ext (by
        rw [Slice.Pos.le_iff, Pos.Raw.le_iff] at h1 h2
        rw [Pos.Raw.ext_iff]; omega)
      subst h_pos
      rw [Slice.sliceTo_endPos]; exact h_eq
    · rename_i h_ne2
      unfold Slice.Pos.get; congr 1

/-! ### Convenience theorems for trimAsciiStart/trimAsciiEnd/trimAscii -/

theorem trimAsciiStart_startsWith_whitespace_false (s : String) :
    s.trimAsciiStart.startsWith Char.isWhitespace = false := by
  unfold String.trimAsciiStart
  exact dropWhile_startsWith_false s.toSlice

theorem trimAsciiEnd_endsWith_whitespace_false (s : String) :
    s.trimAsciiEnd.endsWith Char.isWhitespace = false := by
  unfold String.trimAsciiEnd
  exact dropEndWhile_endsWith_false s.toSlice

theorem trimAscii_startsWith_whitespace_false (s : String) :
    s.trimAscii.startsWith Char.isWhitespace = false := by
  unfold String.trimAscii Slice.trimAscii
  -- trimAscii = trimAsciiStart.trimAsciiEnd = (dropWhile ...).dropEndWhile ...
  -- = (dropWhile ...).sliceTo (...)
  -- startsWith is preserved by sliceTo
  have h := dropWhile_startsWith_false (p := Char.isWhitespace) s.toSlice
  unfold Slice.trimAsciiEnd Slice.dropEndWhile
  exact startsWith_sliceTo _ h

theorem trimAscii_endsWith_whitespace_false (s : String) :
    s.trimAscii.endsWith Char.isWhitespace = false := by
  unfold String.trimAscii Slice.trimAscii
  exact dropEndWhile_endsWith_false _
