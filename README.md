# NonEmpty

A Lean 4 library providing **non-empty variants** of standard data structures:

- `NonEmptyArray α` 📦
- `NonEmptyList α` 📜
- `NonEmptyString` 📝
- `NonEmptyStringTrimmed` ✂️

These types enforce non-emptiness **at the type level**, giving you better safety guarantees and eliminating a whole class of runtime errors.

---

## Features ✨

- **Two implementation strategies**:
  - **Subtype-based**: Drop-in wrappers around Lean’s `Array`, `List`, and `String` that carry a proof of non-emptiness.
  - **Correct-by-Construction**: A specialized `NonEmptyArray` implementation that guarantees non-emptiness by its structural definition (`head` and `tail`).

- Proof-carrying guarantees: you cannot construct an empty `NonEmptyArray`, `NonEmptyList`, or `NonEmptyString`.

- Convenient constructors:

  - `#![...]` for `NonEmptyArray` 📦
  - `![...]` for `NonEmptyList` 📜
  - `nes!"..."` for `NonEmptyString` 📝
  - `nest_trim!"..."` for `NonEmptyStringTrimmed` (trims whitespace) ✂️
  - `nest!"..."` for `NonEmptyStringTrimmed` (requires already trimmed) ✂️

- Standard operations: `head`, `tail`, `cons`, `map`, `append`, etc.

- Safe conversion functions: `fromArray?`, `fromList?`, `fromString?`.

---

## Installation ⚡

Add this to your `lakefile.toml` dependencies:

```toml
[[require]]
name = "NonEmpty"
git = "https://github.com/srghma/lean-nonempty"
rev = "main"
# or if local
# path = "/full/path/to/lean-nonempty"
```

or to `lakefile.lean`

```lean
require NonEmpty from git "https://github.com/srghma/lean-nonempty.git" @ "main"
-- or if local
-- require NonEmpty from path "/full/path/to/lean-nonempty"
```

Then import in your project:

```lean
import NonEmpty.Array
import NonEmpty.List
import NonEmpty.String
import NonEmpty.String.Trimmed
```

---

## Usage 🚀
### NonEmptyArray 📦

```lean
import NonEmpty.Array
open NonEmpty.Array

def ex1 : NonEmptyArray Nat := #![1, 2, 3]

#guard ex1.head = 1
#guard ex1.tail = #[2, 3]
#guard ex1.size = 3

-- cons
def ex2 := ex1.cons 0
#guard ex2.head = 0
#guard ex2.tail = #[1, 2, 3]

-- map
def ex3 := ex1.map (· * 2)
#guard ex3 = #![2, 4, 6]
```

Safe conversion from a standard array:

```lean
#eval NonEmptyArray.fromArray? #[1, 2, 3]  -- some #![1,2,3]
#eval NonEmptyArray.fromArray? #[]         -- none
```

---

### NonEmptyArray (Correct-by-Construction) 🏗️

This version of `NonEmptyArray` is defined structurally (as a head and a tail), making it natively non-empty without needing an explicit proof.

```lean
import NonEmpty.CorrectByConstruction.Array
open NonEmpty.CorrectByConstruction.Array

def exCbC : NonEmptyArray Nat := #![1, 2, 3]

#guard exCbC.head = 1
#guard exCbC.tail = #[2, 3]

-- Structural cons
def exCbC2 := NonEmptyArray.cons 0 exCbC
#guard exCbC2.head = 0
#guard exCbC2.tail = #[1, 2, 3]
```

---
### NonEmptyList 📜

```lean
import NonEmpty.List
open NonEmpty.List

def exList : NonEmptyList String := !["a", "b", "c"]

#guard exList.head = "a"
#guard exList.tail = ["b", "c"]

-- append
def exList2 := exList.append !["d"]
#guard exList2.tail = ["b", "c", "d"]
```

Safe conversion:

```lean
#eval NonEmptyList.fromList? ["x", "y"]  -- some !["x", "y"]
#eval NonEmptyList.fromList? []          -- none
```

---

### NonEmptyString 📝

```lean
import NonEmpty.String
open NonEmpty.String

def exStr : NonEmptyString := nes!"Hello"

#guard exStr.head = 'H'
#guard exStr.tail = "ello"

-- append
def exStr2 := exStr.append (nes!" World")
#guard exStr2.toString = "Hello World"
```

Safe conversion:

```lean
#eval NonEmptyString.fromString? "Hi"  -- some nes!"Hi"
#eval NonEmptyString.fromString? ""    -- none
```

---

### NonEmptyStringTrimmed ✂️

```lean
import NonEmpty.String.Trimmed
open NonEmpty.String.Trimmed

-- Automatically trims whitespace
def exTrim : NonEmptyStringTrimmed := nest_trim!"  Hello World  "

#guard exTrim.toString == "Hello World"

-- Requires string to be trimmed already
def exTrimStrict : NonEmptyStringTrimmed := nest!"Hello"

#guard exTrimStrict.toString == "Hello"
```

Safe conversion:

```lean
#eval NonEmptyStringTrimmed.fromString? "  Hi  "  -- some nest_trim!"Hi"
#eval NonEmptyStringTrimmed.fromString? "   "     -- none
```

---

## Why use NonEmpty? 💡

- Eliminate runtime errors caused by empty collections.
- Make your invariants explicit in types.
- Safer code with fewer runtime checks.

---

## Contributing 🤝

Contributions are welcome! Please open an issue or pull request on GitHub.

---

## License 🛡️

This project is licensed under the **Apache License 2.0**.
