module

public import NonEmpty.String.Basic
public import NonEmpty.Array.Basic

@[expose] public section

namespace NonEmpty.String

open NonEmpty.Array

def intercalateArray (s : String) (xs : NonEmptyArray NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
