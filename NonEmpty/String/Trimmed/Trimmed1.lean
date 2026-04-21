import Lean

open String

/-! ### Custom tactics and metaprogramming for accessing private `dropWhile.go` / `dropEndWhile.go` -/

-- Tactic to rewrite using the equation definition of the private `dropWhile.go`.
open Lean Meta Elab Tactic in
elab "rw_dropWhile_go" : tactic => do
  let eqName : Name :=
    Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr
      (Name.mkStr (Name.mkNum `_private.Init.Data.String.Slice 0)
      "String") "Slice") "dropWhile") "go") "eq_def"
  let goal ← getMainGoal
  let result ← goal.rewrite (← goal.getType) (mkConst eqName)
  let newGoalId ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal (newGoalId :: result.mvarIds)

-- Tactic to rewrite using the equation definition of the private `dropEndWhile.go`.
open Lean Meta Elab Tactic in
elab "rw_dropEndWhile_go" : tactic => do
  let eqName : Name :=
    Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr
      (Name.mkStr (Name.mkNum `_private.Init.Data.String.Slice 0)
      "String") "Slice") "dropEndWhile") "go") "eq_def"
  let goal ← getMainGoal
  let result ← goal.rewrite (← goal.getType) (mkConst eqName)
  let newGoalId ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal (newGoalId :: result.mvarIds)

-- Create public aliases for the private `dropWhile.go` and `dropEndWhile.go` functions.
-- These are definitionally equal to the private functions, allowing us to do
-- well-founded induction on them.
open Lean Meta Elab Command in
run_cmd do
  let n0 : Name := Name.mkNum `_private.Init.Data.String.Slice 0
  let ns : Name := Name.mkStr (Name.mkStr n0 "String") "Slice"
  -- dropWhile.go
  let dwGoName : Name := Name.mkStr (Name.mkStr ns "dropWhile") "go"
  liftTermElabM do
    addDecl (Declaration.defnDecl {
      name := `Slice.dropWhile_go
      levelParams := []
      type := ← inferType (mkConst dwGoName)
      value := mkConst dwGoName
      hints := .regular 0
      safety := .safe
    })
  -- dropEndWhile.go
  let dewGoName : Name := Name.mkStr (Name.mkStr ns "dropEndWhile") "go"
  liftTermElabM do
    addDecl (Declaration.defnDecl {
      name := `Slice.dropEndWhile_go
      levelParams := []
      type := ← inferType (mkConst dewGoName)
      value := mkConst dewGoName
      hints := .regular 0
      safety := .safe
    })

/-! ### Characterization of startsWith/endsWith for Char → Bool predicates -/

/-- `startsWith` for a char predicate checks if the first character satisfies the predicate. -/
theorem startsWith_charPred (p : Char → Bool) (s : Slice) :
    s.startsWith p =
    if h : s.startPos = s.endPos then false
    else p (s.startPos.get h) := by
  simp only [Slice.startsWith, Slice.Pattern.ForwardPattern.startsWith,
    Slice.Pattern.ForwardCharPredSearcher.instForwardPatternForallCharBool,
    Slice.Pattern.ForwardPattern.defaultImplementation,
    Slice.Pattern.ForwardPattern.defaultStartsWith,
    Slice.Pattern.ToForwardSearcher.toSearcher,
    Slice.Pattern.ForwardCharPredSearcher.iter]
  unfold Std.Iter.step
  simp only [Std.Iter.toIterM, Std.IterM.step, Std.Iterator.step,
    Slice.Pattern.ForwardCharPredSearcher.instIteratorIdSearchStep]
  by_cases h : s.startPos = s.endPos
  · simp only [h, dite_true]
    simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [h, dite_false]
    by_cases hp : p (s.startPos.get h)
    · simp only [hp, dite_true]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]

/-- `endsWith` for a char predicate checks if the last character satisfies the predicate. -/
theorem endsWith_charPred (p : Char → Bool) (s : Slice) :
    s.endsWith p =
    if h : s.endPos = s.startPos then false
    else p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos) := by
  simp only [Slice.endsWith, Slice.Pattern.BackwardPattern.endsWith,
    Slice.Pattern.BackwardCharPredSearcher.instBackwardPatternForallCharBool,
    Slice.Pattern.ToBackwardSearcher.defaultImplementation,
    Slice.Pattern.ToBackwardSearcher.defaultEndsWith,
    Slice.Pattern.ToBackwardSearcher.toSearcher,
    Slice.Pattern.BackwardCharPredSearcher.iter]
  unfold Std.Iter.step
  simp only [Std.Iter.toIterM, Std.IterM.step, Std.Iterator.step,
    Slice.Pattern.BackwardCharPredSearcher.instIteratorIdSearchStep]
  by_cases h : s.endPos = s.startPos
  · simp only [h, dite_true]
    simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [h, dite_false]
    by_cases hp : p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos)
    · simp only [hp, dite_true]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]

/-! ### Characterization of dropPrefix?/dropSuffix? for Char → Bool predicates -/

/-- `dropPrefix?` for a char predicate: returns `some (next pos)` if first char matches,
    `none` otherwise. -/
theorem dropPrefix_charPred (p : Char → Bool) (s : Slice) :
    Slice.Pattern.ForwardPattern.dropPrefix? p s =
    if h : s.startPos = s.endPos then none
    else if p (s.startPos.get h) then some (s.startPos.next h)
    else none := by
  simp only [Slice.Pattern.ForwardPattern.dropPrefix?,
    Slice.Pattern.ForwardCharPredSearcher.instForwardPatternForallCharBool,
    Slice.Pattern.ForwardPattern.defaultImplementation,
    Slice.Pattern.ForwardPattern.defaultDropPrefix?,
    Slice.Pattern.ToForwardSearcher.toSearcher,
    Slice.Pattern.ForwardCharPredSearcher.iter]
  unfold Std.Iter.step
  simp only [Std.Iter.toIterM, Std.IterM.step, Std.Iterator.step,
    Slice.Pattern.ForwardCharPredSearcher.instIteratorIdSearchStep]
  by_cases h : s.startPos = s.endPos
  · simp only [h, dite_true]
    simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [h, dite_false]
    by_cases hp : p (s.startPos.get h)
    · simp only [hp, dite_true]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]

/-- `dropSuffix?` for a char predicate: returns `some (prev pos)` if last char matches,
    `none` otherwise. -/
theorem dropSuffix_charPred (p : Char → Bool) (s : Slice) :
    Slice.Pattern.BackwardPattern.dropSuffix? p s =
    if h : s.endPos = s.startPos then none
    else if p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos) then some (s.endPos.prev h)
    else none := by
  simp only [Slice.Pattern.BackwardPattern.dropSuffix?,
    Slice.Pattern.BackwardCharPredSearcher.instBackwardPatternForallCharBool,
    Slice.Pattern.ToBackwardSearcher.defaultImplementation,
    Slice.Pattern.ToBackwardSearcher.defaultDropSuffix?,
    Slice.Pattern.ToBackwardSearcher.toSearcher,
    Slice.Pattern.BackwardCharPredSearcher.iter]
  unfold Std.Iter.step
  simp only [Std.Iter.toIterM, Std.IterM.step, Std.Iterator.step,
    Slice.Pattern.BackwardCharPredSearcher.instIteratorIdSearchStep]
  by_cases h : s.endPos = s.startPos
  · simp only [h, dite_true]
    simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done]
  · simp only [h, dite_false]
    by_cases hp : p ((s.endPos.prev h).get Slice.Pos.prev_ne_endPos)
    · simp only [hp, dite_true]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      simp [Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield]

/-! ### Key connection: dropPrefix? = none ↔ startsWith = false for char predicates -/

theorem startsWith_false_of_dropPrefix_none {p : Char → Bool} {s : Slice}
    (h : Slice.Pattern.ForwardPattern.dropPrefix? p s = none) :
    s.startsWith p = false := by
  rw [startsWith_charPred, dropPrefix_charPred] at *
  split at h <;> simp_all

theorem endsWith_false_of_dropSuffix_none {p : Char → Bool} {s : Slice}
    (h : Slice.Pattern.BackwardPattern.dropSuffix? p s = none) :
    s.endsWith p = false := by
  rw [endsWith_charPred, dropSuffix_charPred] at *
  split at h <;> simp_all

/-! ### Bridge lemma: Slice.toString preserves startsWith/endsWith -/

theorem copy_toSlice_empty_iff (s : Slice) :
    (s.copy.toSlice.startPos = s.copy.toSlice.endPos) ↔ (s.startPos = s.endPos) := by
  simp only [Slice.Pos.ext_iff, Slice.startPos, Slice.endPos, Slice.rawEndPos, Pos.Raw.ext_iff,
    Slice.utf8ByteSize, Pos.Raw.byteDistance, String.toSlice, Slice.copy,
    String.startPos, String.endPos, String.rawEndPos]
  rw [show (extract s.startInclusive s.endExclusive).utf8ByteSize =
    s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx from Slice.utf8ByteSize_copy]
  simp

theorem copy_toSlice_empty_iff' (s : Slice) :
    (s.copy.toSlice.endPos = s.copy.toSlice.startPos) ↔ (s.endPos = s.startPos) := by
  constructor
  · intro h; exact (copy_toSlice_empty_iff s).mp h.symm |>.symm
  · intro h; exact ((copy_toSlice_empty_iff s).mpr h.symm).symm

/-- `Slice.toString` preserves `startsWith` for char predicates. -/
theorem Slice.startsWith_toString {p : Char → Bool} (s : Slice) :
    s.toString.startsWith p = s.startsWith p := by
  show s.copy.toSlice.startsWith p = s.startsWith p
  rw [startsWith_charPred p s.copy.toSlice, startsWith_charPred p s]
  by_cases h : s.startPos = s.endPos
  · simp [h, (copy_toSlice_empty_iff s).mpr h]
  · have h' : ¬(s.copy.toSlice.startPos = s.copy.toSlice.endPos) :=
      mt (copy_toSlice_empty_iff s).mp h
    simp only [h, h', dite_false]
    congr 1
    have h_pos : s.copy.toSlice.startPos = s.startPos.copy.toSlice := by
      apply Slice.Pos.ext; simp [Slice.startPos, Pos.toSlice, Slice.Pos.copy]
    simp only [h_pos]
    rw [Pos.get_toSlice, Slice.Pos.get_copy]

/-! ### Helper lemmas for endsWith_toString -/

private theorem copy_utf8ByteSize (s : Slice) : s.copy.utf8ByteSize = s.utf8ByteSize := by
  rw [Slice.utf8ByteSize_copy]; simp [Slice.utf8ByteSize, Pos.Raw.byteDistance]

private theorem getUTF8Byte_copy_toSlice_eq (s : Slice) (off : Nat)
    (h1 : off < s.copy.toSlice.utf8ByteSize) (h2 : off < s.utf8ByteSize) :
    s.copy.toSlice.getUTF8Byte ⟨off⟩ h1 = s.getUTF8Byte ⟨off⟩ h2 := by
  have step1 : s.copy.toSlice.getUTF8Byte ⟨off⟩ h1 = String.getUTF8Byte s.copy ⟨off⟩ (by
    simp [String.rawEndPos, Slice.utf8ByteSize, String.toSlice,
      Pos.Raw.byteDistance, String.startPos, String.endPos, Slice.utf8ByteSize_copy] at h1 ⊢
    exact h1) := by
    simp [Slice.getUTF8Byte, String.getUTF8Byte, String.toSlice, Pos.Raw.offsetBy]
  rw [step1]; exact Slice.getUTF8Byte_copy

private theorem prevAux_go_eq (s : Slice) (off1 off2 : Nat) (heq : off1 = off2)
    (h1 : off1 < s.copy.toSlice.utf8ByteSize) (h2 : off2 < s.utf8ByteSize) :
    @Slice.Pos.prevAux.go s.copy.toSlice off1 h1 = @Slice.Pos.prevAux.go s off2 h2 := by
  subst heq
  induction off1 using Nat.strongRecOn with
  | _ off ih =>
    rw [@Slice.Pos.prevAux.go.eq_def s.copy.toSlice, @Slice.Pos.prevAux.go.eq_def s]
    have hbyte := getUTF8Byte_copy_toSlice_eq s off h1 h2
    simp only [hbyte]; split; · rfl
    · cases off with | zero => rfl | succ n => exact ih n (by omega) (by omega) (by omega)

private theorem prev_endPos_offset_eq (s : Slice)
    (h1 : s.copy.toSlice.endPos ≠ s.copy.toSlice.startPos) (h2 : s.endPos ≠ s.startPos) :
    (s.copy.toSlice.endPos.prev h1).offset = (s.endPos.prev h2).offset := by
  show s.copy.toSlice.endPos.prevAux h1 = s.endPos.prevAux h2
  simp only [Slice.Pos.prevAux]
  apply prevAux_go_eq
  simp [Slice.endPos, Slice.rawEndPos, Slice.utf8ByteSize, String.toSlice, Pos.Raw.byteDistance,
    String.startPos, String.endPos, String.rawEndPos, Slice.utf8ByteSize_copy]

private theorem Slice_Pos_get_eq_of_offset_eq {s : Slice} {p1 p2 : s.Pos}
    (h_off : p1.offset = p2.offset) (h1 : p1 ≠ s.endPos) (h2 : p2 ≠ s.endPos) :
    p1.get h1 = p2.get h2 := by
  simp [Slice.Pos.get, h_off]

private theorem get_copy_toSlice_eq_get (s : Slice)
    (p1 : s.copy.toSlice.Pos) (p2 : s.Pos) (h_off : p1.offset = p2.offset)
    (h1 : p1 ≠ s.copy.toSlice.endPos) (h2 : p2 ≠ s.endPos) :
    p1.get h1 = p2.get h2 := by
  have h_copy_toSlice_offset : p2.copy.toSlice.offset = p1.offset := by
    simp [Pos.toSlice, Slice.Pos.copy, h_off]
  have h_copy_toSlice_ne : p2.copy.toSlice ≠ s.copy.toSlice.endPos := by
    intro heq
    exact h1 (Slice.Pos.ext (by rw [← h_copy_toSlice_offset]; exact (Slice.Pos.ext_iff.mp heq)))
  have h_copy_ne : p2.copy ≠ s.copy.endPos := by
    intro heq; exact h2 (Slice.Pos.ext (by
      have := Pos.ext_iff.mp heq
      simp only [Slice.Pos.copy, String.endPos, String.rawEndPos, Slice.copy] at this
      simp only [Slice.endPos, Slice.rawEndPos]
      rw [Pos.Raw.ext_iff]; rw [Pos.Raw.ext_iff] at this
      simp at this ⊢; rw [this]; exact copy_utf8ByteSize s))
  calc p1.get h1
      = p2.copy.toSlice.get h_copy_toSlice_ne :=
          (Slice_Pos_get_eq_of_offset_eq h_copy_toSlice_offset h_copy_toSlice_ne h1).symm
    _ = p2.copy.get h_copy_ne := Pos.get_toSlice
    _ = p2.get _ := Slice.Pos.get_copy h_copy_ne

/-- `Slice.toString` preserves `endsWith` for char predicates. -/
theorem Slice.endsWith_toString {p : Char → Bool} (s : Slice) :
    s.toString.endsWith p = s.endsWith p := by
  show s.copy.toSlice.endsWith p = s.endsWith p
  rw [endsWith_charPred p s.copy.toSlice, endsWith_charPred p s]
  by_cases h : s.endPos = s.startPos
  · simp [h, (copy_toSlice_empty_iff' s).mpr h]
  · have h' : ¬(s.copy.toSlice.endPos = s.copy.toSlice.startPos) :=
      mt (copy_toSlice_empty_iff' s).mp h
    simp only [h, h', dite_false]
    congr 1
    exact get_copy_toSlice_eq_get s _ _ (prev_endPos_offset_eq s h' h) _ _

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
  rw [Slice.Pos.lt_iff] at hab ⊢
  simp only [Slice.Pos.ofSliceTo]
  exact hab

/-! ### Main theorems: dropWhile/dropEndWhile remove the pattern from the start/end

These are proved by well-founded induction on the public alias of the private `go` functions.
Since the public aliases are definitionally equal to the private functions, `unfold` exposes
the private `go`, and `rw_dropWhile_go`/`rw_dropEndWhile_go` can then unfold one step. -/

/-- After `dropWhile p`, the result no longer starts with `p`. -/
theorem dropWhile_go_startsWith_false {p : Char → Bool} (s : Slice) (curr : s.Pos) :
    (Slice.dropWhile_go s p curr).startsWith p = false := by
  unfold Slice.dropWhile_go
  rw_dropWhile_go
  split
  case h_1 nextCurr h_some =>
    split
    case isTrue h_lt =>
      exact dropWhile_go_startsWith_false s (Slice.Pos.ofSliceFrom nextCurr)
    case isFalse h_nlt =>
      exfalso; apply h_nlt
      rw [dropPrefix_charPred] at h_some
      split at h_some
      · simp at h_some
      · split at h_some
        · simp only [Option.some.injEq] at h_some; rw [← h_some]
          calc curr = Slice.Pos.ofSliceFrom (s.sliceFrom curr).startPos :=
                Slice.Pos.ofSliceFrom_startPos.symm
            _ < Slice.Pos.ofSliceFrom ((s.sliceFrom curr).startPos.next _) :=
                Slice.Pos.ofSliceFrom_lt_of_lt Slice.Pos.lt_next
        · simp at h_some
  case h_2 h_none =>
    apply startsWith_false_of_dropPrefix_none
    cases hd : Slice.Pattern.ForwardPattern.dropPrefix? p (s.sliceFrom curr) with
    | none => rfl
    | some v => exfalso; exact h_none v hd
termination_by curr

/-- After `dropEndWhile p`, the result no longer ends with `p`. -/
theorem dropEndWhile_go_endsWith_false {p : Char → Bool} (s : Slice) (curr : s.Pos) :
    (Slice.dropEndWhile_go s p curr).endsWith p = false := by
  unfold Slice.dropEndWhile_go
  rw_dropEndWhile_go
  split
  case h_1 nextCurr h_some =>
    split
    case isTrue h_lt =>
      exact dropEndWhile_go_endsWith_false s (Slice.Pos.ofSliceTo nextCurr)
    case isFalse h_nlt =>
      exfalso; apply h_nlt
      rw [dropSuffix_charPred] at h_some
      split at h_some
      · simp at h_some
      · split at h_some
        · simp only [Option.some.injEq] at h_some; rw [← h_some]
          calc Slice.Pos.ofSliceTo ((s.sliceTo curr).endPos.prev _) <
                Slice.Pos.ofSliceTo (s.sliceTo curr).endPos :=
                  Slice.Pos.ofSliceTo_lt_of_lt Slice.Pos.prev_lt
            _ = curr := by
                simp [Slice.Pos.ofSliceTo, Slice.endPos, Slice.sliceTo,
                  Slice.rawEndPos, Slice.utf8ByteSize, Pos.Raw.byteDistance]
        · simp at h_some
  case h_2 h_none =>
    apply endsWith_false_of_dropSuffix_none
    cases hd : Slice.Pattern.BackwardPattern.dropSuffix? p (s.sliceTo curr) with
    | none => rfl
    | some v => exfalso; exact h_none v hd
termination_by curr.down

/-! ### sliceTo preserves startsWith -/

/-- `sliceTo` only truncates the end, so `startsWith` is preserved. -/
theorem startsWith_sliceTo {p : Char → Bool} {s : Slice}
    (pos : s.Pos) (h : s.startsWith p = false) :
    (s.sliceTo pos).startsWith p = false := by
  rw [startsWith_charPred] at h ⊢
  split at h
  · rename_i h_empty
    split
    · rfl
    · rename_i h_sliceTo_nonempty
      exfalso; apply h_sliceTo_nonempty
      apply Slice.Pos.ext
      simp only [Slice.startPos, Slice.endPos, Slice.rawEndPos, Slice.sliceTo,
        Slice.utf8ByteSize, Pos.Raw.byteDistance, Pos.Raw.ext_iff]
      have h_le := pos.isValidForSlice.le_rawEndPos
      rw [Slice.Pos.ext_iff] at h_empty
      simp [Slice.startPos, Slice.endPos, Slice.rawEndPos, Pos.Raw.ext_iff,
        Slice.utf8ByteSize, Pos.Raw.byteDistance] at h_empty
      simp [Pos.Raw.le_iff, Slice.rawEndPos, Slice.utf8ByteSize, Pos.Raw.byteDistance] at h_le
      simp [Slice.Pos.str, Pos.Raw.offsetBy]
      omega
  · simp_all only [Slice.Pos.get, Slice.startPos, Slice.sliceTo]
    split <;> rfl

/-! ### dropEndWhile preserves startsWith -/

/-- `dropEndWhile_go` preserves `startsWith q = false` for any predicate `q`,
    because it only truncates from the end (returns `sliceTo`). -/
theorem dropEndWhile_go_preserves_startsWith {p q : Char → Bool} (s : Slice) (curr : s.Pos)
    (h : s.startsWith q = false) :
    (Slice.dropEndWhile_go s p curr).startsWith q = false := by
  unfold Slice.dropEndWhile_go
  rw_dropEndWhile_go
  split
  case h_1 nextCurr h_some =>
    split
    case isTrue h_lt =>
      exact dropEndWhile_go_preserves_startsWith s (Slice.Pos.ofSliceTo nextCurr) h
    case isFalse => exact startsWith_sliceTo curr h
  case h_2 => exact startsWith_sliceTo curr h
termination_by curr.down

/-! ### Convenience theorems for trimAscii -/

/-- `trimAscii` removes leading whitespace, so the result does not start with whitespace. -/
theorem trimAscii_startsWith_whitespace_false (s : String) :
    s.trimAscii.startsWith Char.isWhitespace = false := by
  unfold String.trimAscii Slice.trimAscii Slice.trimAsciiEnd Slice.trimAsciiStart
  show (Slice.dropEndWhile_go _ _ _).startsWith _ = false
  apply dropEndWhile_go_preserves_startsWith
  show (Slice.dropWhile_go _ _ _).startsWith _ = false
  exact dropWhile_go_startsWith_false _ _

/-- `trimAscii` removes trailing whitespace, so the result does not end with whitespace. -/
theorem trimAscii_endsWith_whitespace_false (s : String) :
    s.trimAscii.endsWith Char.isWhitespace = false := by
  unfold String.trimAscii Slice.trimAscii
  show (Slice.dropEndWhile_go _ _ _).endsWith _ = false
  exact dropEndWhile_go_endsWith_false _ _

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

/-- Trim a string and return it as `NonEmptyStringTrimmed` if it's non-empty.

Uses `trimAscii_toString_startsWith_whitespace_false` and
`trimAscii_toString_endsWith_whitespace_false` to avoid redundant
`startsWith`/`endsWith` checks after trimming. -/
def fromString? (s : String) : Option NonEmptyStringTrimmed :=
  let t := s.trimAscii.toString
  if hne : t = "" then
    none
  else
    some ⟨t, trimAscii_toString_startsWith_whitespace_false s,
             trimAscii_toString_endsWith_whitespace_false s, hne⟩

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
