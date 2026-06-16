module

/-!
# Safe Map Downgraders

This module defines the `DowngradeMap` typeclass.
It enables automatic transitive coercions over Functor-like containers,
ensuring that if a safe coercion `α → β` exists, `F α → F β` works implicitly.
-/

public section
namespace NonEmpty

/-- A typeclass for containers that support mapping coercions (downgrades) safely. -/
class DowngradeMap (F : Type u → Type v) where
  map {α β : Type u} : (α → β) → F α → F β

/-- Automatically derive `CoeOut (F α) (F β)` if `F` supports `DowngradeMap` and `α` coerces to `β`. -/
@[inline]
instance [DowngradeMap F] [CoeOut α β] : CoeOut (F α) (F β) where
  coe xs := DowngradeMap.map CoeOut.coe xs

-- Standard library downgraders
@[inline]
instance : DowngradeMap List where
  map := List.map

@[inline]
instance : DowngradeMap Array where
  map := Array.map

end NonEmpty
