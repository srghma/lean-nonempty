module

import all NonEmpty.StringTrimmedSlice
public meta import NonEmpty.StringTrimmedSlice.Basic
open NonEmpty.StringTrimmedSlice
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed
open NonEmpty.String

namespace NonEmptyTest.StringTrimmedSlice

def testValidString : NonEmptyStringTrimmedSlice :=
  (NonEmptyStringTrimmedSlice.fromString? "hello").get!

#guard testValidString.toSlice.toString == "hello"

def testWhitespaceLeft : Option NonEmptyStringTrimmedSlice :=
  NonEmptyStringTrimmedSlice.fromString? " hello"

#guard testWhitespaceLeft.get!.toSlice.toString == "hello"

def testWhitespaceRight : Option NonEmptyStringTrimmedSlice :=
  NonEmptyStringTrimmedSlice.fromString? "hello "

#guard testWhitespaceRight.get!.toSlice.toString == "hello"

def testEmpty : Option NonEmptyStringTrimmedSlice :=
  NonEmptyStringTrimmedSlice.fromString? ""

#guard testEmpty.isNone

-- Coercion tests
def testCoeSlice (s : NonEmptyStringTrimmedSlice) : String.Slice := s
def testCoeNonEmptyStringSlice (s : NonEmptyStringTrimmedSlice) : NonEmptyStringSlice := s
def testCoeString (s : NonEmptyStringTrimmedSlice) : String := s
def testCoeNonEmptyString (s : NonEmptyStringTrimmedSlice) : NonEmptyString := s
def testCoeNonEmptyStringTrimmed (s : NonEmptyStringTrimmedSlice) : NonEmptyStringTrimmed := s

end NonEmptyTest.StringTrimmedSlice
