module

import NonEmpty.String.Basic
import NonEmpty.ArrayCorrectByConstruction.Basic

namespace NonEmpty.String

def intercalateArrayCBC (s : String) (xs : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
