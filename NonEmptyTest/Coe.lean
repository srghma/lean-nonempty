module

import all NonEmpty.List
import all NonEmpty.Array
import all NonEmpty.ArrayCorrectByConstruction
import all NonEmpty.String
import all NonEmpty.StringSlice
import all NonEmpty.StringTrimmed
import all NonEmpty.DowngradeMap
public meta import NonEmpty.List.Basic
public meta import NonEmpty.Array.Basic
public meta import NonEmpty.ArrayCorrectByConstruction.Basic
public meta import NonEmpty.String.Basic
public meta import NonEmpty.StringSlice.Basic
public meta import NonEmpty.StringTrimmed.Basic

/-!
# Coercion (Downgrader) Tests

Tests that all `CoeOut` instances introduced across the NonEmpty library
synthesise correctly.  The key point is that **no explicit conversion function
calls** are required — Lean inserts the coercions automatically.
-/

open NonEmpty.List
open NonEmpty.Array
open NonEmpty.ArrayCorrectByConstruction
open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed

-- ============================================================
-- Abbreviations
-- ============================================================

private abbrev L      := List
private abbrev NEL    := NonEmptyList
private abbrev LS     := List String
private abbrev NELS   := NonEmptyList String
private abbrev LNES   := List NonEmptyString
private abbrev NELNES := NonEmptyList NonEmptyString

private abbrev A      := Array
private abbrev NEA    := NonEmpty.Array.NonEmptyArray
private abbrev NEACBC := NonEmpty.ArrayCorrectByConstruction.NonEmptyArray

private abbrev S      := String
private abbrev NES    := NonEmptyString
private abbrev NESS   := NonEmptyStringSlice
private abbrev NEST   := NonEmptyStringTrimmed

-- ============================================================
-- NonEmptyList → List
-- ============================================================

section NonEmptyListCoe

def nels_val : NELS := !["hello", "world"]
def lnes_val : LNES := [nes!"hello", nes!"world"]
def nelnes_val : NELNES := ![nes!"hello", nes!"world"]

-- LNES -> LS
#guard (lnes_val : LS) = ["hello", "world"]

-- NELS -> LS
#guard (nels_val : LS) = ["hello", "world"]

-- NELNES -> LS
#guard (nelnes_val : LS) = ["hello", "world"]

-- NELNES -> LNES
#guard (nelnes_val : LNES) = [nes!"hello", nes!"world"]

-- NELNES -> NELS
#guard (nelnes_val : NELS).toList = ["hello", "world"]

end NonEmptyListCoe

-- ============================================================
-- NonEmpty.Array.NonEmptyArray → Array
-- ============================================================

section NonEmptyArrayCoe

def nea_val : NEA Nat := #![10, 20, 30]

#guard (nea_val : A Nat) = #[10, 20, 30]

end NonEmptyArrayCoe

-- ============================================================
-- NonEmpty.ArrayCorrectByConstruction.NonEmptyArray → Array
-- ============================================================

section NonEmptyArrayCBCCoe

def nea_cbc_val : NEACBC Nat := #![1, 2, 3]

#guard (nea_cbc_val : A Nat) = #[1, 2, 3]

end NonEmptyArrayCBCCoe

-- ============================================================
-- NonEmptyString → String  (existing, sanity check)
-- ============================================================

section NonEmptyStringCoe

def nes_val : NES := nes!"lean"

#guard (nes_val : S) = "lean"

end NonEmptyStringCoe

-- ============================================================
-- NonEmptyStringSlice → NonEmptyString → String
-- ============================================================

section NonEmptyStringSliceCoe

def ness_val : NESS :=
  match NonEmptyStringSlice.fromString? "hello" with
  | some s => s
  | none   => NonEmptyStringSlice.mk "x".toSlice (by simp)

-- Coerce slice → NonEmptyString
#guard (ness_val : NES).toString = "hello"

-- Coerce slice → String (transitive via CoeTC)
#guard (ness_val : S) = "hello"

end NonEmptyStringSliceCoe

-- ============================================================
-- NonEmptyStringTrimmed → NonEmptyStringSlice → NonEmptyString → String
-- ============================================================

section NonEmptyStringTrimmedCoe

def nest_val : NEST := nest_trim!"  trimmed  "

-- Coerce trimmed → slice (new CoeOut in NonEmpty.Coe)
#guard (nest_val : NESS).toString = "trimmed"

-- Coerce trimmed → NonEmptyString (existing CoeOut)
#guard (nest_val : NES).toString = "trimmed"

-- Coerce trimmed → String (existing CoeOut)
#guard (nest_val : S) = "trimmed"

end NonEmptyStringTrimmedCoe

-- TODO: though List NonEmptyString and List String are the exact same data structure at runtime, the `map` is still executed. Fix bc it should be a no-op.
-- set_option trace.compiler.ir.result true
-- def testMap (xs : NonEmpty.List.NonEmptyList NonEmptyString) : NonEmpty.List.NonEmptyList String :=
--   ↑xs
