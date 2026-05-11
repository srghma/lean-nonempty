module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import NonEmpty.StringTrimmed.Basic

public section

namespace NonEmpty.StringTrimmed

instance : Lean.ToJson NonEmptyStringTrimmed where
  toJson s := Lean.toJson s.toString

instance : Lean.FromJson NonEmptyStringTrimmed where
  fromJson? j := do
    let s ← Lean.fromJson? j
    match NonEmptyStringTrimmed.fromString? s with
    | some res => Except.ok res
    | none => throw "expected non-empty trimmed string"

end NonEmpty.StringTrimmed

end
