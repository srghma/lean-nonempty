module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.StringSlice.Basic

public section

namespace NonEmpty.StringSlice

instance : Lean.ToJson NonEmptyStringSlice where
  toJson s := Lean.toJson s.toString

instance : Lean.FromJson NonEmptyStringSlice where
  fromJson? j := do
    let s ← Lean.fromJson? j
    match NonEmptyStringSlice.fromString? s with
    | some res => Except.ok res
    | none => throw "expected non-empty string slice"

end NonEmpty.StringSlice

end
