module

import all NonEmpty.List
import all NonEmpty.Array
import all NonEmpty.ArrayCorrectByConstruction
import all NonEmpty.String
import all NonEmpty.StringSlice
import all NonEmpty.StringTrimmed
import all NonEmpty.Coe
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
-- Abbreviations (mirroring the user's example)
-- ============================================================

private abbrev L      := List
private abbrev NEL    := NonEmptyList
private abbrev LS     := List String
private abbrev NELS   := NonEmptyList String
private abbrev LNES   := List NonEmptyString
private abbrev NELNES := NonEmptyList NonEmptyString

-- ============================================================
-- NonEmptyList → List
-- ============================================================

section NonEmptyListCoe

def nels_val : NELS := !["hello", "world"]
def lnes_val : LNES := [nes!"hello", nes!"world"]
def nelnes_val : NELNES := ![nes!"hello", nes!"world"]

/-- LNES -> LS -/
def test_LNES_to_LS : LS := lnes_val
#guard test_LNES_to_LS = ["hello", "world"]

/-- NELS -> LS -/
def test_NELS_to_LS : LS := nels_val
#guard test_NELS_to_LS = ["hello", "world"]

/-- NELNES -> LS -/
def test_NELNES_to_LS : LS := nelnes_val
#guard test_NELNES_to_LS = ["hello", "world"]

/-- NELNES -> LNES -/
def test_NELNES_to_LNES : LNES := nelnes_val
#guard test_NELNES_to_LNES = [nes!"hello", nes!"world"]

/-- NELNES -> NELS -/
def test_NELNES_to_NELS : NELS := nelnes_val
#guard test_NELNES_to_NELS.toList = ["hello", "world"]

end NonEmptyListCoe

-- ============================================================
-- NonEmpty.Array.NonEmptyArray → Array
-- ============================================================

section NonEmptyArrayCoe

def nea : NonEmpty.Array.NonEmptyArray Nat := #![10, 20, 30]
def arr_from_nea : Array Nat := nea
#guard arr_from_nea = #[10, 20, 30]

end NonEmptyArrayCoe

-- ============================================================
-- NonEmpty.ArrayCorrectByConstruction.NonEmptyArray → Array
-- ============================================================

section NonEmptyArrayCBCCoe

def nea_cbc : NonEmpty.ArrayCorrectByConstruction.NonEmptyArray Nat := #![1, 2, 3]
def arr_from_nea_cbc : Array Nat := nea_cbc
#guard arr_from_nea_cbc = #[1, 2, 3]

end NonEmptyArrayCBCCoe

-- ============================================================
-- NonEmptyString → String  (existing, sanity check)
-- ============================================================

section NonEmptyStringCoe

def nes_val : NonEmptyString := nes!"lean"
def str_from_nes : String := nes_val
#guard str_from_nes = "lean"

end NonEmptyStringCoe

-- ============================================================
-- NonEmptyStringSlice → NonEmptyString → String
-- ============================================================

section NonEmptyStringSliceCoe

def nesl : NonEmptyStringSlice :=
  match NonEmptyStringSlice.fromString? "hello" with
  | some s => s
  | none   => NonEmptyStringSlice.mk "x".toSlice (by simp)

/-- Coerce slice → NonEmptyString -/
def nes_from_nesl : NonEmptyString := nesl
#guard nes_from_nesl.toString = "hello"

/-- Coerce slice → String (transitive via CoeTC) -/
def str_from_nesl : String := (nesl : NonEmptyString)
#guard str_from_nesl = "hello"

end NonEmptyStringSliceCoe

-- ============================================================
-- NonEmptyStringTrimmed → NonEmptyStringSlice → NonEmptyString → String
-- ============================================================

section NonEmptyStringTrimmedCoe

def nest_val : NonEmptyStringTrimmed := nest_trim!"  trimmed  "

/-- Coerce trimmed → slice (new CoeOut in NonEmpty.Coe) -/
def nesl_from_nest : NonEmptyStringSlice := nest_val
#guard nesl_from_nest.toString = "trimmed"

/-- Coerce trimmed → NonEmptyString (existing CoeOut) -/
def nes_from_nest : NonEmptyString := nest_val
#guard nes_from_nest.toString = "trimmed"

/-- Coerce trimmed → String (existing CoeOut) -/
def str_from_nest : String := nest_val
#guard str_from_nest = "trimmed"

end NonEmptyStringTrimmedCoe
