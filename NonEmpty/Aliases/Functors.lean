module

public import NonEmpty.List.Basic
public import NonEmpty.Array.Basic
public import NonEmpty.ArrayCorrectByConstruction.Basic
public import NonEmpty.ListCorrectByConstruction.Basic

public section
namespace NonEmpty.Aliases

abbrev L := List
abbrev A := Array
abbrev NEL := NonEmpty.List.NonEmptyList
abbrev NEA := NonEmpty.Array.NonEmptyArray
abbrev NELCBC := NonEmpty.ListCorrectByConstruction.NonEmptyList
abbrev NEACBC := NonEmpty.ArrayCorrectByConstruction.NonEmptyArray

end NonEmpty.Aliases
