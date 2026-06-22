module

import NonEmpty.String.Basic
import NonEmpty.ListCorrectByConstruction.Basic

namespace NonEmpty.String

def intercalateListCBC (s : String) (xs : NonEmpty.ListCorrectByConstruction.NonEmptyList NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => HAppend.hAppend (HAppend.hAppend acc s) x) xs.head
