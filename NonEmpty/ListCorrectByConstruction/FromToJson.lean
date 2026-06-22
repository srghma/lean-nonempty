module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.ListCorrectByConstruction.Basic

public section

namespace NonEmpty.ListCorrectByConstruction

instance [Lean.ToJson α] : Lean.ToJson (NonEmptyList α) where
  toJson xs := Lean.toJson (xs.toList)

instance [Lean.FromJson α] : Lean.FromJson (NonEmptyList α) where
  fromJson? j := do
    let arr ← Lean.fromJson? j
    match NonEmptyList.fromList? arr with
    | some res => Except.ok res
    | none => throw "expected non-empty array"

end NonEmpty.ListCorrectByConstruction

end
