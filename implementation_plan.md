# Plan: Fill Sorries and Prove Trimming Properties

This plan covers the proof of the "now trimmed" properties for string trimming and their application to the `NonEmptyStringTrimmed` type.

## Proposed Changes

### [MODIFY] [Theorems.lean](file:///home/srghma/projects/lean-nonempty/NonEmpty/String/Trimmed/Theorems.lean)

Prove the properties of `dropWhile` and `dropEndWhile`:

- `startsWith_dropWhile_false`: `(s.dropWhile p).startsWith p = false`
- `endsWith_dropEndWhile_false`: `(s.dropEndWhile p).endsWith p = false`
- `trimAsciiStart_startsWith_whitespace_false`: `(s.trimAsciiStart).startsWith Char.isWhitespace = false`
- `trimAsciiEnd_endsWith_whitespace_false`: `(s.trimAsciiEnd).endsWith Char.isWhitespace = false`
- `trimAscii_startsWith_whitespace_false`: `s.trimAscii.startsWith Char.isWhitespace = false`
- `trimAscii_endsWith_whitespace_false`: `s.trimAscii.endsWith Char.isWhitespace = false`

### [MODIFY] [Trimmed.lean](file:///home/srghma/projects/lean-nonempty/NonEmpty/String/Trimmed.lean)

- [ ] Import `NonEmpty.String.Trimmed.Theorems`.
- [ ] Fix the `fromString?` `sorries` using the theorems above.
- [ ] Re-add the formatting/predicates that were removed if they are needed for the user's project flow.
- [ ] Ensure `toString.startsWith` properties are correctly satisfied by the `Slice` property proofs (using `startsWith_eq_startsWith_toSlice`).

## Verification Plan

### Automated Tests
- Verify theorems in `Theorems.lean` using Lean's compiler.
- Check that `fromString?` compiles without `sorry`.
- Test `nest!` with strings like `"  world  "`.
