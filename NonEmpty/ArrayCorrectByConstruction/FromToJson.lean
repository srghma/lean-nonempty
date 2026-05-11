module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.ArrayCorrectByConstruction.Basic

public section

namespace NonEmpty.ArrayCorrectByConstruction

instance [Lean.ToJson α] : Lean.ToJson (NonEmptyArray α) where
  toJson xs := Lean.toJson (xs.toArr)

instance [Lean.FromJson α] : Lean.FromJson (NonEmptyArray α) where
  fromJson? j := do
    let arr ← Lean.fromJson? j
    match NonEmptyArray.fromArray? arr with
    | some res => Except.ok res
    | none => throw "expected non-empty array"

end NonEmpty.ArrayCorrectByConstruction

end
