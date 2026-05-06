module

public section
namespace NonEmpty.String

structure NonEmptyString where
  toString : String
  isNonEmpty : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq

instance : Coe NonEmptyString String where
  coe s := s.toString

instance : ToString NonEmptyString where
  toString s := s.toString

namespace NonEmptyString

abbrev fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none

abbrev fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨String.ofList cs, by simp_all only [ne_eq, String.ofList_eq_empty_iff, not_false_eq_true]⟩

abbrev fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.ofList cs)

@[simp] theorem toString_ne_empty (s : NonEmptyString) : s.toString ≠ "" := s.isNonEmpty

instance : HAppend String NonEmptyString NonEmptyString where
  hAppend s1 s2 := ⟨s1 ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_false, not_false_eq_true]⟩

instance : HAppend NonEmptyString String NonEmptyString where
  hAppend s1 s2 := ⟨s1.toString ++ s2, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, false_and, not_false_eq_true]⟩

instance : HAppend NonEmptyString NonEmptyString NonEmptyString where
  hAppend s1 s2 := ⟨s1.toString ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_self, not_false_eq_true]⟩

end NonEmptyString

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (by decide) : NonEmptyString) )

#guard (nes!"world").toString == "world"

end NonEmpty.String
