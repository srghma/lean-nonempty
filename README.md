# NonEmpty

A Lean 4 library providing **non-empty variants** of standard data structures:

- `NonEmptyArray α` 📦
- `NonEmptyList α` 📜
- `NonEmptyString` 📝

These types enforce non-emptiness **at the type level**, giving you better safety guarantees and eliminating a whole class of runtime errors.

---

## Features ✨

- Drop-in wrappers around Lean’s `Array`, `List`, and `String`.

- Proof-carrying guarantees: you cannot construct an empty `NonEmptyArray`, `NonEmptyList`, or `NonEmptyString`.

- Convenient constructors:

  - `#![...]` for `NonEmptyArray` 📦
  - `![...]` for `NonEmptyList` 📜
  - `nes!"..."` for `NonEmptyString` 📝

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
```

---

## Usage 🚀

### NonEmptyArray 📦

```lean
import NonEmpty.Array

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

### NonEmptyList 📜

```lean
import NonEmpty.List

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
