module

public import NonEmpty.String
public import NonEmpty.StringSlice
public import NonEmpty.StringTrimmed
public import NonEmpty.StringTrimmedSlice

public section
namespace NonEmpty.Aliases

abbrev S := String
abbrev NES := NonEmpty.String.NonEmptyString
abbrev NESS := NonEmpty.StringSlice.NonEmptyStringSlice
abbrev NEST := NonEmpty.StringTrimmed.NonEmptyStringTrimmed
abbrev NESTS := NonEmpty.StringTrimmedSlice.NonEmptyStringTrimmedSlice

end NonEmpty.Aliases
