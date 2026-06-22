module

import NonEmpty.String.Basic
import NonEmpty.List.Basic

namespace NonEmpty.String

def intercalateList (s : String) (xs : NonEmpty.List.NonEmptyList NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
