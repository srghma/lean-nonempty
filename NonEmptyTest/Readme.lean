import NonEmpty.Array
import NonEmpty.List
import NonEmpty.String

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
