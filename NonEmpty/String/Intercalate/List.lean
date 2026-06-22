module

public import NonEmpty.String.Basic
public import NonEmpty.List.Basic

@[expose] public section

namespace NonEmpty.String

open NonEmpty.List

def intercalateList (s : String) (xs : NonEmpty.List.NonEmptyList NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
