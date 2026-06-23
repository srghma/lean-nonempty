module

import Lean
import NonEmpty.Array.Basic
import NonEmpty.ArrayUtil

open NonEmpty.Array

theorem List.length_flatMap_pos {α β} (xs : List α) (f : α → List β) (h1 : xs.length > 0) (h2 : ∀ x ∈ xs, (f x).length > 0) : (xs.flatMap f).length > 0 := by
  induction xs with
  | nil => revert h1; simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, gt_iff_lt]
    have h3 := h2 head (by simp)
    exact Nat.add_pos_left h3 _

@[ext] theorem NonEmptyArray.ext (a b : NonEmptyArray α) (h : a.toArray = b.toArray) : a = b := by
  cases a; cases b; congr

def NonEmptyArray.flatten (xs : NonEmptyArray (NonEmptyArray α)) : NonEmptyArray α :=
  ⟨xs.toArray.flatMap (fun a => a.toArray), by
    have H : (xs.toArray.flatMap (fun a => a.toArray)).toList = xs.toArray.toList.flatMap (fun a => a.toArray.toList) := by rw [Array.toList_flatMap]
    have H2 : (xs.toArray.flatMap (fun a => a.toArray)).size = (xs.toArray.flatMap (fun a => a.toArray)).toList.length := Array.size_eq_length_toList
    rw [H2, H]
    apply List.length_flatMap_pos
    · rw [← Array.size_eq_length_toList]; exact xs.isNonEmpty
    · intro x hx
      rw [← Array.size_eq_length_toList]
      exact x.isNonEmpty
  ⟩

def NonEmptyArray.bind (xs : NonEmptyArray α) (f : α → NonEmptyArray β) : NonEmptyArray β :=
  NonEmptyArray.flatten (xs.map f)

instance : Functor NonEmptyArray where map := NonEmptyArray.map
instance : Pure NonEmptyArray where pure := NonEmptyArray.singleton
instance : Seq NonEmptyArray where seq f x := NonEmptyArray.bind f (fun f' => NonEmptyArray.map f' (x ()))
instance : SeqLeft NonEmptyArray where seqLeft a b := NonEmptyArray.bind a (fun a' => NonEmptyArray.map (fun _ => a') (b ()))
instance : SeqRight NonEmptyArray where seqRight a b := NonEmptyArray.bind a (fun _ => b ())

instance : Applicative NonEmptyArray where
  pure := NonEmptyArray.singleton
  seq f x := NonEmptyArray.bind f (fun f' => NonEmptyArray.map f' (x ()))
  seqLeft a b := NonEmptyArray.bind a (fun a' => NonEmptyArray.map (fun _ => a') (b ()))
  seqRight a b := NonEmptyArray.bind a (fun _ => b ())

instance : Monad NonEmptyArray where bind := NonEmptyArray.bind

@[simp] theorem NonEmptyArray.toArray_map (xs : NonEmptyArray α) (f : α → β) : (xs.map f).toArray = xs.toArray.map f := rfl
@[simp] theorem NonEmptyArray.toArray_flatten (xs : NonEmptyArray (NonEmptyArray α)) : (NonEmptyArray.flatten xs).toArray = xs.toArray.flatMap (fun a => a.toArray) := rfl
@[simp] theorem NonEmptyArray.toArray_bind (xs : NonEmptyArray α) (f : α → NonEmptyArray β) : (NonEmptyArray.bind xs f).toArray = xs.toArray.flatMap (fun a => (f a).toArray) := by
  change (NonEmptyArray.flatten (xs.map f)).toArray = _
  simp only [NonEmptyArray.toArray_flatten, Array.flatMap_map]

@[simp] theorem NonEmptyArray.toArray_pure (x : α) : (pure x : NonEmptyArray α).toArray = #[x] := rfl

instance : LawfulFunctor NonEmptyArray where
  map_const := rfl
  id_map x := by apply NonEmptyArray.ext; simp only [Functor.map, NonEmptyArray.toArray_map, Array.map_id_fun, id_eq]
  comp_map g h x := by apply NonEmptyArray.ext; simp only [Functor.map, NonEmptyArray.toArray_map,
    Array.map_map]

-- Useful helper lemmas (add these near the toArray_* simp set)
@[simp] theorem NonEmptyArray.toArray_singleton (x : α) :
    (NonEmptyArray.singleton x).toArray = #[x] := rfl

-- ============================================================
-- Missing Array bridge lemmas (add before the instances)
-- ============================================================

-- Array.flatMap composed with Array.map
-- (Array.flatMap_map may not exist; this bridges via toList)
theorem Array.flatMap_flatMap' (xs : Array α)
    (f : α → Array β) (g : β → Array γ) :
    (xs.flatMap f).flatMap g = xs.flatMap (fun a => (f a).flatMap g) := by
  grind => instantiate only [flatMap_assoc]

theorem Array.singleton_flatMap' (x : α) (f : α → Array β) :
    (#[x] : Array α).flatMap f = f x := by
  simp only [List.flatMap_toArray, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    toArray_toList]

-- seqLeft canonical form: (fun a _ => a) <$> x <*> y
-- After unfolding <$> and <*> for NonEmptyArray, both sides equal:
-- x.toArray.flatMap (fun a => y.toArray.map (fun _ => a))
theorem Array.flatMap_const_map (xs ys : Array α) :
    xs.flatMap (fun a => ys.map (fun _ => a)) =
    (xs.flatMap (fun a => ys.map (fun _ => a))) := rfl

private theorem Array.toList_injective {α} {a b : Array α} (h : a.toList = b.toList) : a = b := by
  rwa [← Array.toList_inj]

-- ============================================================
-- LawfulApplicative
-- ============================================================

instance : LawfulApplicative NonEmptyArray where
  seqLeft_eq x y := by
    apply NonEmptyArray.ext
    -- LHS: seqLeft x y = bind x (fun a' => map (fun _ => a') (y ()))
    -- RHS: (fun a _ => a) <$> x <*> y
    --    = bind (map (fun a _ => a) x) (fun f => map f y)
    --    = bind x (fun a => map (fun _ => a) y)
    -- Both sides reduce to x.toArray.flatMap (fun a => y.toArray.map (fun _ => a))
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map,
               NonEmptyArray.toArray_bind]
    rw [Array.flatMap_map]
    -- Now both sides should be x.flatMap (fun a => y.map (fun _ => a))
    rfl
  seqRight_eq x y := by
    apply NonEmptyArray.ext
    -- LHS: seqRight x y = bind x (fun _ => y)
    -- RHS: (fun _ b => b) <$> x <*> y = bind (map (fun _ b => b) x) (fun f => map f y)
    --    = bind x (fun _ => map id y) = bind x (fun _ => y)
    simp only [SeqRight.seqRight, Seq.seq, Functor.map,
               NonEmptyArray.toArray_bind]
    rw [Array.flatMap_map]
    simp [Array.map_id_fun]
  pure_seq g x := by
    apply NonEmptyArray.ext
    simp only [Pure.pure, Seq.seq, NonEmptyArray.toArray_bind, Array.flatMap_singleton]
    rfl

  map_pure f x := by
    apply NonEmptyArray.ext
    simp only [Functor.map, NonEmptyArray.toArray_map, NonEmptyArray.toArray_pure,
               Array.map_singleton]

  seq_pure f x := by
    apply NonEmptyArray.ext
    simp only [Seq.seq, NonEmptyArray.toArray_bind, NonEmptyArray.toArray_pure]
    simp only [List.map_toArray, List.map_cons, List.map_nil,
      NonEmpty.ArrayUtil.flatMap_singleton_eq_map]
    rfl

  seq_assoc x g h := by
    apply NonEmptyArray.ext
    -- h <*> (g <*> x) = bind h (fun h' => map h' (bind g (fun g' => map g' x)))
    -- (comp <$> h <*> g <*> x)
    -- Both sides equal h.flatMap (fun h' => g.flatMap (fun g' => x.map (h' ∘ g')))
    simp only [Seq.seq, Functor.map, NonEmptyArray.toArray_bind]
    simp only [Array.flatMap_map, Array.map_flatMap]
    rw [Array.flatMap_flatMap']
    congr 1; ext h'
    simp_all only [Array.map_map, Array.size_flatMap, Array.size_map]
    rfl
    simp_all only [Array.map_map]
    grind only [Array.flatMap_map]

-- ============================================================
-- LawfulMonad
-- ============================================================

instance : LawfulMonad NonEmptyArray where
  bind_pure_comp f x := by
    apply NonEmptyArray.ext
    simp only [bind, NonEmptyArray.bind, NonEmptyArray.toArray_flatten,
               NonEmptyArray.toArray_map, Functor.map, Pure.pure]
    grind => instantiate only [Array.flatMap_map, Array.map_eq_flatMap]

  bind_map f x := by apply NonEmptyArray.ext; rfl

  bind_assoc x f g := by
    apply NonEmptyArray.ext
    simp only [bind, NonEmptyArray.bind, NonEmptyArray.toArray_flatten]
    apply Array.toList_injective
    simp [Array.toList_flatMap, Array.toList_map]
    simp only [List.flatMap_map, List.flatMap_assoc]
    congr
    funext a
    simp only [NonEmptyArray.toArray_flatten, Array.toList_flatMap, Array.toList_map]
    simp only [List.flatMap_map]

  pure_bind x f := by
    apply NonEmptyArray.ext
    simp only [bind, NonEmptyArray.bind]
    simp only [NonEmptyArray.toArray_flatten, NonEmptyArray.toArray_pure, List.map_toArray,
      List.map_cons, List.map_nil, List.flatMap_toArray, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Array.toArray_toList]
