module

import NonEmpty.String.Basic
import NonEmpty.Array.Basic

namespace NonEmpty.String

def intercalateArray (s : String) (xs : NonEmpty.Array.NonEmptyArray NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
