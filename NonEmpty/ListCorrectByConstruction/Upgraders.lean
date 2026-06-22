module

public import NonEmpty.ListCorrectByConstruction.Basic
public import NonEmpty.String
public import NonEmpty.StringSlice
public import NonEmpty.StringTrimmed
public import NonEmpty.StringTrimmedSlice
public import NonEmpty.Aliases.FunctorsAndScalars

open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed
open NonEmpty.StringTrimmedSlice
open NonEmpty.Aliases

public section
namespace NonEmpty.ListCorrectByConstruction

-- ==============================================================================
-- 1. Upgrades that don't lose any info (just change shape)
-- ==============================================================================

@[inline] def «L_->NELCBC_» {α} : L α → Option (NELCBC α) := NonEmptyList.fromList?

@[inline] def «L/NES->NELCBC/S» : «L/NES» → Option «NELCBC/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))
@[inline] def «L/NESS->NELCBC/S» : «L/NESS» → Option «NELCBC/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))
@[inline] def «L/NEST->NELCBC/S» : «L/NEST» → Option «NELCBC/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))

-- ==============================================================================
-- 2. Lax Upgrades (FilterMap) - drop elements that fail the check
-- ==============================================================================

namespace FilterMap

  -- To NES
  @[inline] def «L/S->L/NES» : «L/S» → «L/NES» := (·.filterMap NonEmptyString.fromString?)
  @[inline] def «L/S->NELCBC/NES» : «L/S» → Option «NELCBC/NES» := λ xs => NonEmptyList.fromList? («L/S->L/NES» xs)
  @[inline] def «NELCBC/S->L/NES» : «NELCBC/S» → «L/NES» := («L/S->L/NES» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NES» : «NELCBC/S» → Option «NELCBC/NES» := λ xs => NonEmptyList.fromList? («L/S->L/NES» xs.toList)

  -- To NESS
  @[inline] def «L/S->L/NESS» : «L/S» → «L/NESS» := (·.filterMap NonEmptyStringSlice.fromString?)
  @[inline] def «L/S->NELCBC/NESS» : «L/S» → Option «NELCBC/NESS» := λ xs => NonEmptyList.fromList? («L/S->L/NESS» xs)
  @[inline] def «NELCBC/S->L/NESS» : «NELCBC/S» → «L/NESS» := («L/S->L/NESS» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NESS» : «NELCBC/S» → Option «NELCBC/NESS» := λ xs => NonEmptyList.fromList? («L/S->L/NESS» xs.toList)

  -- To NEST
  @[inline] def «L/S->L/NEST» : «L/S» → «L/NEST» := (·.filterMap NonEmptyStringTrimmed.fromString?)
  @[inline] def «L/S->NELCBC/NEST» : «L/S» → Option «NELCBC/NEST» := λ xs => NonEmptyList.fromList? («L/S->L/NEST» xs)
  @[inline] def «NELCBC/S->L/NEST» : «NELCBC/S» → «L/NEST» := («L/S->L/NEST» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NEST» : «NELCBC/S» → Option «NELCBC/NEST» := λ xs => NonEmptyList.fromList? («L/S->L/NEST» xs.toList)

  -- To NESTS
  @[inline] def «L/S->L/NESTS» : «L/S» → «L/NESTS» := (·.filterMap NonEmptyStringTrimmedSlice.fromString?)
  @[inline] def «L/S->NELCBC/NESTS» : «L/S» → Option «NELCBC/NESTS» := λ xs => NonEmptyList.fromList? («L/S->L/NESTS» xs)
  @[inline] def «NELCBC/S->L/NESTS» : «NELCBC/S» → «L/NESTS» := («L/S->L/NESTS» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NESTS» : «NELCBC/S» → Option «NELCBC/NESTS» := λ xs => NonEmptyList.fromList? («L/S->L/NESTS» xs.toList)

end FilterMap

-- ==============================================================================
-- 3. Strict Upgrades (Traverse) - fail completely if any element fails the check
-- ==============================================================================

namespace Traverse

  -- To NES
  @[inline] def «L/S->L/NES» : «L/S» → Option «L/NES» := List.mapM NonEmptyString.fromString?
  @[inline] def «L/S->NELCBC/NES» : «L/S» → Option «NELCBC/NES» := NonEmptyList.fromList? <=< «L/S->L/NES»
  @[inline] def «NELCBC/S->L/NES» : «NELCBC/S» → Option «L/NES» := («L/S->L/NES» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NES» : «NELCBC/S» → Option «NELCBC/NES» := («L/S->NELCBC/NES» ·.toList)

  -- To NESS
  @[inline] def «L/S->L/NESS» : «L/S» → Option «L/NESS» := List.mapM NonEmptyStringSlice.fromString?
  @[inline] def «L/S->NELCBC/NESS» : «L/S» → Option «NELCBC/NESS» := NonEmptyList.fromList? <=< «L/S->L/NESS»
  @[inline] def «NELCBC/S->L/NESS» : «NELCBC/S» → Option «L/NESS» := («L/S->L/NESS» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NESS» : «NELCBC/S» → Option «NELCBC/NESS» := («L/S->NELCBC/NESS» ·.toList)

  -- To NEST
  @[inline] def «L/S->L/NEST» : «L/S» → Option «L/NEST» := List.mapM NonEmptyStringTrimmed.fromString?
  @[inline] def «L/S->NELCBC/NEST» : «L/S» → Option «NELCBC/NEST» := NonEmptyList.fromList? <=< «L/S->L/NEST»
  @[inline] def «NELCBC/S->L/NEST» : «NELCBC/S» → Option «L/NEST» := («L/S->L/NEST» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NEST» : «NELCBC/S» → Option «NELCBC/NEST» := («L/S->NELCBC/NEST» ·.toList)

  -- To NESTS
  @[inline] def «L/S->L/NESTS» : «L/S» → Option «L/NESTS» := List.mapM NonEmptyStringTrimmedSlice.fromString?
  @[inline] def «L/S->NELCBC/NESTS» : «L/S» → Option «NELCBC/NESTS» := NonEmptyList.fromList? <=< «L/S->L/NESTS»
  @[inline] def «NELCBC/S->L/NESTS» : «NELCBC/S» → Option «L/NESTS» := («L/S->L/NESTS» ·.toList)
  @[inline] def «NELCBC/S->NELCBC/NESTS» : «NELCBC/S» → Option «NELCBC/NESTS» := («L/S->NELCBC/NESTS» ·.toList)

end Traverse

end NonEmpty.ListCorrectByConstruction
