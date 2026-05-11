module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.String.Basic

public section

namespace NonEmpty.String

instance : Lean.ToJson NonEmptyString where
  toJson s := Lean.toJson s.toString

instance : Lean.FromJson NonEmptyString where
  fromJson? j := do
    let s ← Lean.fromJson? j
    match NonEmptyString.fromString? s with
    | some res => Except.ok res
    | none => throw "expected non-empty string"

end NonEmpty.String

end
