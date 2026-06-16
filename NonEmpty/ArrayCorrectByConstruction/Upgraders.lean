module

public import NonEmpty.ArrayCorrectByConstruction.Basic
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
namespace NonEmpty.ArrayCorrectByConstruction

-- ==============================================================================
-- 1. Upgrades that don't lose any info (just change shape)
-- ==============================================================================

@[inline] def «A_->NEACBC_» {α} : A α → Option (NEACBC α) := NonEmptyArray.fromArray?

@[inline] def «A/NES->NEACBC/S» : «A/NES» → Option «NEACBC/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))
@[inline] def «A/NESS->NEACBC/S» : «A/NESS» → Option «NEACBC/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))
@[inline] def «A/NEST->NEACBC/S» : «A/NEST» → Option «NEACBC/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))

-- ==============================================================================
-- 2. Lax Upgrades (FilterMap) - drop elements that fail the check
-- ==============================================================================

namespace FilterMap

  -- To NES
  @[inline] def «A/S->A/NES» : «A/S» → «A/NES» := (·.filterMap NonEmptyString.fromString?)
  @[inline] def «A/S->NEACBC/NES» : «A/S» → Option «NEACBC/NES» := λ xs => NonEmptyArray.fromArray? («A/S->A/NES» xs)
  @[inline] def «NEACBC/S->A/NES» : «NEACBC/S» → «A/NES» := («A/S->A/NES» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NES» : «NEACBC/S» → Option «NEACBC/NES» := λ xs => NonEmptyArray.fromArray? («A/S->A/NES» xs.toArr)

  -- To NESS
  @[inline] def «A/S->A/NESS» : «A/S» → «A/NESS» := (·.filterMap NonEmptyStringSlice.fromString?)
  @[inline] def «A/S->NEACBC/NESS» : «A/S» → Option «NEACBC/NESS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESS» xs)
  @[inline] def «NEACBC/S->A/NESS» : «NEACBC/S» → «A/NESS» := («A/S->A/NESS» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NESS» : «NEACBC/S» → Option «NEACBC/NESS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESS» xs.toArr)

  -- To NEST
  @[inline] def «A/S->A/NEST» : «A/S» → «A/NEST» := (·.filterMap NonEmptyStringTrimmed.fromString?)
  @[inline] def «A/S->NEACBC/NEST» : «A/S» → Option «NEACBC/NEST» := λ xs => NonEmptyArray.fromArray? («A/S->A/NEST» xs)
  @[inline] def «NEACBC/S->A/NEST» : «NEACBC/S» → «A/NEST» := («A/S->A/NEST» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NEST» : «NEACBC/S» → Option «NEACBC/NEST» := λ xs => NonEmptyArray.fromArray? («A/S->A/NEST» xs.toArr)

  -- To NESTS
  @[inline] def «A/S->A/NESTS» : «A/S» → «A/NESTS» := (·.filterMap NonEmptyStringTrimmedSlice.fromString?)
  @[inline] def «A/S->NEACBC/NESTS» : «A/S» → Option «NEACBC/NESTS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESTS» xs)
  @[inline] def «NEACBC/S->A/NESTS» : «NEACBC/S» → «A/NESTS» := («A/S->A/NESTS» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NESTS» : «NEACBC/S» → Option «NEACBC/NESTS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESTS» xs.toArr)

end FilterMap

-- ==============================================================================
-- 3. Strict Upgrades (Traverse) - fail completely if any element fails the check
-- ==============================================================================

namespace Traverse

  -- To NES
  @[inline] def «A/S->A/NES» : «A/S» → Option «A/NES» := Array.mapM NonEmptyString.fromString?
  @[inline] def «A/S->NEACBC/NES» : «A/S» → Option «NEACBC/NES» := NonEmptyArray.fromArray? <=< «A/S->A/NES»
  @[inline] def «NEACBC/S->A/NES» : «NEACBC/S» → Option «A/NES» := («A/S->A/NES» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NES» : «NEACBC/S» → Option «NEACBC/NES» := («A/S->NEACBC/NES» ·.toArr)

  -- To NESS
  @[inline] def «A/S->A/NESS» : «A/S» → Option «A/NESS» := Array.mapM NonEmptyStringSlice.fromString?
  @[inline] def «A/S->NEACBC/NESS» : «A/S» → Option «NEACBC/NESS» := NonEmptyArray.fromArray? <=< «A/S->A/NESS»
  @[inline] def «NEACBC/S->A/NESS» : «NEACBC/S» → Option «A/NESS» := («A/S->A/NESS» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NESS» : «NEACBC/S» → Option «NEACBC/NESS» := («A/S->NEACBC/NESS» ·.toArr)

  -- To NEST
  @[inline] def «A/S->A/NEST» : «A/S» → Option «A/NEST» := Array.mapM NonEmptyStringTrimmed.fromString?
  @[inline] def «A/S->NEACBC/NEST» : «A/S» → Option «NEACBC/NEST» := NonEmptyArray.fromArray? <=< «A/S->A/NEST»
  @[inline] def «NEACBC/S->A/NEST» : «NEACBC/S» → Option «A/NEST» := («A/S->A/NEST» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NEST» : «NEACBC/S» → Option «NEACBC/NEST» := («A/S->NEACBC/NEST» ·.toArr)

  -- To NESTS
  @[inline] def «A/S->A/NESTS» : «A/S» → Option «A/NESTS» := Array.mapM NonEmptyStringTrimmedSlice.fromString?
  @[inline] def «A/S->NEACBC/NESTS» : «A/S» → Option «NEACBC/NESTS» := NonEmptyArray.fromArray? <=< «A/S->A/NESTS»
  @[inline] def «NEACBC/S->A/NESTS» : «NEACBC/S» → Option «A/NESTS» := («A/S->A/NESTS» ·.toArr)
  @[inline] def «NEACBC/S->NEACBC/NESTS» : «NEACBC/S» → Option «NEACBC/NESTS» := («A/S->NEACBC/NESTS» ·.toArr)

end Traverse

end NonEmpty.ArrayCorrectByConstruction
