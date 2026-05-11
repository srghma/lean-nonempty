module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.Array.Basic

public section

namespace NonEmpty.Array

instance [Lean.ToJson α] : Lean.ToJson (NonEmptyArray α) where
  toJson a := Lean.toJson a.toArray

instance [Lean.FromJson α] : Lean.FromJson (NonEmptyArray α) where
  fromJson? j := do
    let a ← Lean.fromJson? j
    match NonEmptyArray.fromArray? a with
    | some res => Except.ok res
    | none => throw "expected non-empty array"

end NonEmpty.Array

end
