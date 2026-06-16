module

public import NonEmpty.Array
public import NonEmpty.String
public import NonEmpty.StringSlice
public import NonEmpty.StringTrimmed
public import NonEmpty.Aliases.FunctorsAndScalars

open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed
open NonEmpty.Aliases

public section
namespace NonEmpty.Array

-- ==============================================================================
-- 1. Upgrades that don't lose any info (just change shape)
-- ==============================================================================

@[inline] def «A_->NEA_» {α} : A α → Option (NEA α) := NonEmptyArray.fromArray?

@[inline] def «A/NES->NEA/S» : «A/NES» → Option «NEA/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))
@[inline] def «A/NESS->NEA/S» : «A/NESS» → Option «NEA/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))
@[inline] def «A/NEST->NEA/S» : «A/NEST» → Option «NEA/S» := λ xs => NonEmptyArray.fromArray? (xs.map (·.toString))

-- ==============================================================================
-- 2. Lax Upgrades (FilterMap) - drop elements that fail the check
-- ==============================================================================

namespace FilterMap

  -- To NES
  @[inline] def «A/S->A/NES» : «A/S» → «A/NES» := (·.filterMap NonEmptyString.fromString?)
  @[inline] def «A/S->NEA/NES» : «A/S» → Option «NEA/NES» := λ xs => NonEmptyArray.fromArray? («A/S->A/NES» xs)
  @[inline] def «NEA/S->A/NES» : «NEA/S» → «A/NES» := («A/S->A/NES» ·.toArray)
  @[inline] def «NEA/S->NEA/NES» : «NEA/S» → Option «NEA/NES» := λ xs => NonEmptyArray.fromArray? («A/S->A/NES» xs.toArray)

  -- To NESS
  @[inline] def «A/S->A/NESS» : «A/S» → «A/NESS» := (·.filterMap NonEmptyStringSlice.fromString?)
  @[inline] def «A/S->NEA/NESS» : «A/S» → Option «NEA/NESS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESS» xs)
  @[inline] def «NEA/S->A/NESS» : «NEA/S» → «A/NESS» := («A/S->A/NESS» ·.toArray)
  @[inline] def «NEA/S->NEA/NESS» : «NEA/S» → Option «NEA/NESS» := λ xs => NonEmptyArray.fromArray? («A/S->A/NESS» xs.toArray)

  -- To NEST
  @[inline] def «A/S->A/NEST» : «A/S» → «A/NEST» := (·.filterMap NonEmptyStringTrimmed.fromString?)
  @[inline] def «A/S->NEA/NEST» : «A/S» → Option «NEA/NEST» := λ xs => NonEmptyArray.fromArray? («A/S->A/NEST» xs)
  @[inline] def «NEA/S->A/NEST» : «NEA/S» → «A/NEST» := («A/S->A/NEST» ·.toArray)
  @[inline] def «NEA/S->NEA/NEST» : «NEA/S» → Option «NEA/NEST» := λ xs => NonEmptyArray.fromArray? («A/S->A/NEST» xs.toArray)

end FilterMap

-- ==============================================================================
-- 3. Strict Upgrades (Traverse) - fail completely if any element fails the check
-- ==============================================================================

namespace Traverse

  -- To NES
  @[inline] def «A/S->A/NES» : «A/S» → Option «A/NES» := Array.mapM NonEmptyString.fromString?
  @[inline] def «A/S->NEA/NES» : «A/S» → Option «NEA/NES» := NonEmptyArray.fromArray? <=< «A/S->A/NES»
  @[inline] def «NEA/S->A/NES» : «NEA/S» → Option «A/NES» := («A/S->A/NES» ·.toArray)
  @[inline] def «NEA/S->NEA/NES» : «NEA/S» → Option «NEA/NES» := («A/S->NEA/NES» ·.toArray)

  -- To NESS
  @[inline] def «A/S->A/NESS» : «A/S» → Option «A/NESS» := Array.mapM NonEmptyStringSlice.fromString?
  @[inline] def «A/S->NEA/NESS» : «A/S» → Option «NEA/NESS» := NonEmptyArray.fromArray? <=< «A/S->A/NESS»
  @[inline] def «NEA/S->A/NESS» : «NEA/S» → Option «A/NESS» := («A/S->A/NESS» ·.toArray)
  @[inline] def «NEA/S->NEA/NESS» : «NEA/S» → Option «NEA/NESS» := («A/S->NEA/NESS» ·.toArray)

  -- To NEST
  @[inline] def «A/S->A/NEST» : «A/S» → Option «A/NEST» := Array.mapM NonEmptyStringTrimmed.fromString?
  @[inline] def «A/S->NEA/NEST» : «A/S» → Option «NEA/NEST» := NonEmptyArray.fromArray? <=< «A/S->A/NEST»
  @[inline] def «NEA/S->A/NEST» : «NEA/S» → Option «A/NEST» := («A/S->A/NEST» ·.toArray)
  @[inline] def «NEA/S->NEA/NEST» : «NEA/S» → Option «NEA/NEST» := («A/S->NEA/NEST» ·.toArray)

end Traverse

end NonEmpty.Array
