module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.List.Basic

public section

namespace NonEmpty.List

instance [Lean.ToJson α] : Lean.ToJson (NonEmptyList α) where
  toJson a := Lean.toJson a.toList

instance [Lean.FromJson α] : Lean.FromJson (NonEmptyList α) where
  fromJson? j := do
    let a ← Lean.fromJson? j
    match NonEmptyList.fromList? a with
    | some res => Except.ok res
    | none => throw "expected non-empty list"

end NonEmpty.List

end
