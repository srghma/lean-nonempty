module

import all NonEmpty.Array
import all NonEmpty.List
import all NonEmpty.String
import all NonEmpty.String.Trimmed
import all NonEmpty.CorrectByConstruction.Array
public meta import NonEmpty.CorrectByConstruction.Array.Basic

section
open NonEmpty.String
open NonEmpty.String.Trimmed
open NonEmpty.Array
open NonEmpty.List

/-!
This file tests the examples shown in `README.md`.
-/

-- === NonEmptyArray ===
def ex1 : NonEmptyArray Nat := #![1, 2, 3]

#guard ex1.head = 1
#guard ex1.tail = #[2, 3]
#guard ex1.size = 3


-- === NonEmptyList ===
def ex2 : NonEmptyList String := !["hello", "world"]

#guard ex2.head = "hello"
#guard ex2.tail = ["world"]
#guard ex2.length = 2


-- === NonEmptyString ===
def ex3 : NonEmptyString := nes!"lean"

#guard ex3.toString = "lean"


-- === NonEmptyStringTrimmed ===
def ex4 : NonEmptyStringTrimmed := nest_trim!"  trimmed  "

#guard ex4.toString == "trimmed"
-- The macro should have already trimmed the string
#guard ex4.toString.startsWith Char.isWhitespace == false
#guard ex4.toString.endsWith Char.isWhitespace == false

end section

section

open NonEmpty.CorrectByConstruction.Array

def a : NonEmptyArray Nat := #![1, 2, 3]
def b : NonEmptyArray Nat := #![10]

-- Test head and tail
#guard a.head = 1
#guard a.tail = #[2, 3]
#guard b.head = 10
#guard b.tail = #[]

-- Test size
#guard a.size = 3
#guard b.size = 1

-- Test cons
def c := NonEmptyArray.cons 0 a
#guard c.head = 0
#guard c.tail = #[1, 2, 3]

-- Test singleton
def d := NonEmptyArray.singleton 5
#guard d.head = 5
#guard d.tail = #[]

-- Test map
def e := a.map (fun x => x + 1)
#guard e.head = 2
#guard e.tail = #[3, 4]

-- Test append
def f := a.append b
#guard f.head = 1
#guard f.tail = #[2, 3, 10]
