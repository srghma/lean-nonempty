module

public import NonEmpty.List.Basic
public import NonEmpty.Array.Basic
public import NonEmpty.ArrayCorrectByConstruction.Basic

public import NonEmpty.Aliases.FunctorsAndScalars

public section
namespace NonEmpty.Conversions

open NonEmpty.Aliases

-- ==============================================================================
-- Base Conversions
-- ==============================================================================

@[inline] def «L->A» {α} : L α → A α := List.toArray
@[inline] def «A->L» {α} : A α → L α := Array.toList

-- ==============================================================================
-- Top Triangle Conversions
-- ==============================================================================

@[inline] def «NEL->NEA» {α} (xs : NEL α) : NEA α :=
  ⟨xs.toList.toArray, by
    have h := xs.isNonEmpty
    -- Array.size (List.toArray xs) is exactly xs.length
    exact h
  ⟩

@[inline] def «NEA->NEL» {α} (xs : NEA α) : NEL α :=
  ⟨xs.toArray.toList, by
    have h := xs.isNonEmpty
    -- List.length (Array.toList xs) is exactly xs.size
    exact h
  ⟩

@[inline] def «NEA->NEACBC» {α} (xs : NEA α) : NEACBC α :=
  NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.fromArray xs.toArray xs.isNonEmpty

@[inline] def «NEACBC->NEA» {α} (xs : NEACBC α) : NEA α :=
  ⟨xs.toArr, by
    have : xs.toArr.size = xs.size := NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.size_toArr xs
    have : xs.size > 0 := by
      simp only [NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.size]
      omega
    omega
  ⟩

@[inline] def «NEL->NEACBC» {α} (xs : NEL α) : NEACBC α :=
  «NEA->NEACBC» («NEL->NEA» xs)

@[inline] def «NEACBC->NEL» {α} (xs : NEACBC α) : NEL α :=
  «NEA->NEL» («NEACBC->NEA» xs)

end NonEmpty.Conversions
