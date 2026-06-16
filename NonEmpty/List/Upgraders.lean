module

public import NonEmpty.List
public import NonEmpty.String
public import NonEmpty.StringSlice
public import NonEmpty.StringTrimmed
public import NonEmpty.Aliases.FunctorsAndScalars

open NonEmpty.String
open NonEmpty.StringSlice
open NonEmpty.StringTrimmed
open NonEmpty.Aliases

public section
namespace NonEmpty.List

-- ==============================================================================
-- 1. Upgrades that don't lose any info (just change shape)
-- ==============================================================================

@[inline] def «L_->NEL_» {α} : L α → Option (NEL α) := NonEmptyList.fromList?

@[inline] def «L/NES->NEL/S» : «L/NES» → Option «NEL/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))
@[inline] def «L/NESS->NEL/S» : «L/NESS» → Option «NEL/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))
@[inline] def «L/NEST->NEL/S» : «L/NEST» → Option «NEL/S» := λ xs => NonEmptyList.fromList? (xs.map (·.toString))

-- ==============================================================================
-- 2. Lax Upgrades (FilterMap) - drop elements that fail the check
-- ==============================================================================

namespace FilterMap

  -- To NES
  @[inline] def «L/S->L/NES» : «L/S» → «L/NES» := (·.filterMap NonEmptyString.fromString?)
  @[inline] def «L/S->NEL/NES» : «L/S» → Option «NEL/NES» := λ xs => NonEmptyList.fromList? («L/S->L/NES» xs)
  @[inline] def «NEL/S->L/NES» : «NEL/S» → «L/NES» := («L/S->L/NES» ·.toList)
  @[inline] def «NEL/S->NEL/NES» : «NEL/S» → Option «NEL/NES» := λ xs => NonEmptyList.fromList? («L/S->L/NES» xs.toList)

  -- To NESS
  @[inline] def «L/S->L/NESS» : «L/S» → «L/NESS» := (·.filterMap NonEmptyStringSlice.fromString?)
  @[inline] def «L/S->NEL/NESS» : «L/S» → Option «NEL/NESS» := λ xs => NonEmptyList.fromList? («L/S->L/NESS» xs)
  @[inline] def «NEL/S->L/NESS» : «NEL/S» → «L/NESS» := («L/S->L/NESS» ·.toList)
  @[inline] def «NEL/S->NEL/NESS» : «NEL/S» → Option «NEL/NESS» := λ xs => NonEmptyList.fromList? («L/S->L/NESS» xs.toList)

  -- To NEST
  @[inline] def «L/S->L/NEST» : «L/S» → «L/NEST» := (·.filterMap NonEmptyStringTrimmed.fromString?)
  @[inline] def «L/S->NEL/NEST» : «L/S» → Option «NEL/NEST» := λ xs => NonEmptyList.fromList? («L/S->L/NEST» xs)
  @[inline] def «NEL/S->L/NEST» : «NEL/S» → «L/NEST» := («L/S->L/NEST» ·.toList)
  @[inline] def «NEL/S->NEL/NEST» : «NEL/S» → Option «NEL/NEST» := λ xs => NonEmptyList.fromList? («L/S->L/NEST» xs.toList)

end FilterMap

-- ==============================================================================
-- 3. Strict Upgrades (Traverse) - fail completely if any element fails the check
-- ==============================================================================

namespace Traverse

  -- To NES
  @[inline] def «L/S->L/NES» : «L/S» → Option «L/NES» := List.mapM NonEmptyString.fromString?
  @[inline] def «L/S->NEL/NES» : «L/S» → Option «NEL/NES» := NonEmptyList.fromList? <=< «L/S->L/NES»
  @[inline] def «NEL/S->L/NES» : «NEL/S» → Option «L/NES» := («L/S->L/NES» ·.toList)
  @[inline] def «NEL/S->NEL/NES» : «NEL/S» → Option «NEL/NES» := («L/S->NEL/NES» ·.toList)

  -- To NESS
  @[inline] def «L/S->L/NESS» : «L/S» → Option «L/NESS» := List.mapM NonEmptyStringSlice.fromString?
  @[inline] def «L/S->NEL/NESS» : «L/S» → Option «NEL/NESS» := NonEmptyList.fromList? <=< «L/S->L/NESS»
  @[inline] def «NEL/S->L/NESS» : «NEL/S» → Option «L/NESS» := («L/S->L/NESS» ·.toList)
  @[inline] def «NEL/S->NEL/NESS» : «NEL/S» → Option «NEL/NESS» := («L/S->NEL/NESS» ·.toList)

  -- To NEST
  @[inline] def «L/S->L/NEST» : «L/S» → Option «L/NEST» := List.mapM NonEmptyStringTrimmed.fromString?
  @[inline] def «L/S->NEL/NEST» : «L/S» → Option «NEL/NEST» := NonEmptyList.fromList? <=< «L/S->L/NEST»
  @[inline] def «NEL/S->L/NEST» : «NEL/S» → Option «L/NEST» := («L/S->L/NEST» ·.toList)
  @[inline] def «NEL/S->NEL/NEST» : «NEL/S» → Option «NEL/NEST» := («L/S->NEL/NEST» ·.toList)

end Traverse

end NonEmpty.List
