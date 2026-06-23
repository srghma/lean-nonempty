module

import Lean
import NonEmpty.List.Basic

open NonEmpty.List

-- ============================================================
-- Core Monadic Definitions
-- ============================================================

theorem List.length_flatMap_pos {α β} (xs : List α) (f : α → List β) (h1 : xs.length > 0) (h2 : ∀ x ∈ xs, (f x).length > 0) : (xs.flatMap f).length > 0 := by
  induction xs with
  | nil => revert h1; simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, gt_iff_lt]
    have h3 := h2 head (by simp)
    exact Nat.add_pos_left h3 _

@[ext] theorem NonEmptyList.ext (a b : NonEmptyList α) (h : a.toList = b.toList) : a = b := by
  cases a; cases b; congr

def NonEmptyList.flatten (xs : NonEmptyList (NonEmptyList α)) : NonEmptyList α :=
  ⟨xs.toList.flatMap (fun a => a.toList), by
    apply List.length_flatMap_pos
    · exact xs.isNonEmpty
    · intro x hx
      exact x.isNonEmpty
  ⟩

def NonEmptyList.bind (xs : NonEmptyList α) (f : α → NonEmptyList β) : NonEmptyList β :=
  NonEmptyList.flatten (xs.map f)

instance : Functor NonEmptyList where map := NonEmptyList.map
instance : Pure NonEmptyList where pure := NonEmptyList.singleton
instance : Seq NonEmptyList where seq f x := NonEmptyList.bind f (fun f' => NonEmptyList.map f' (x ()))
instance : SeqLeft NonEmptyList where seqLeft a b := NonEmptyList.bind a (fun a' => NonEmptyList.map (fun _ => a') (b ()))
instance : SeqRight NonEmptyList where seqRight a b := NonEmptyList.bind a (fun _ => b ())

instance : Applicative NonEmptyList where
  pure := NonEmptyList.singleton
  seq f x := NonEmptyList.bind f (fun f' => NonEmptyList.map f' (x ()))
  seqLeft a b := NonEmptyList.bind a (fun a' => NonEmptyList.map (fun _ => a') (b ()))
  seqRight a b := NonEmptyList.bind a (fun _ => b ())

instance : Monad NonEmptyList where bind := NonEmptyList.bind

-- ============================================================
-- Simplification Lemmas
-- ============================================================

@[simp] theorem NonEmptyList.toList_map (xs : NonEmptyList α) (f : α → β) :
    (xs.map f).toList = xs.toList.map f := rfl

@[simp] theorem NonEmptyList.toList_flatten (xs : NonEmptyList (NonEmptyList α)) :
    (NonEmptyList.flatten xs).toList = xs.toList.flatMap (fun a => a.toList) := rfl

@[simp] theorem NonEmptyList.toList_bind (xs : NonEmptyList α) (f : α → NonEmptyList β) :
    (NonEmptyList.bind xs f).toList = xs.toList.flatMap (fun a => (f a).toList) := by
  change (NonEmptyList.flatten (xs.map f)).toList = _
  simp only [NonEmptyList.toList_flatten, List.flatMap_map]

@[simp] theorem NonEmptyList.toList_pure (x : α) :
    (pure x : NonEmptyList α).toList = [x] := rfl

@[simp] theorem NonEmptyList.toList_singleton (x : α) :
    (NonEmptyList.singleton x).toList = [x] := rfl

-- ============================================================
-- LawfulFunctor
-- ============================================================

instance : LawfulFunctor NonEmptyList where
  map_const := rfl
  id_map x := by apply NonEmptyList.ext; simp only [Functor.map, NonEmptyList.toList_map, List.map_id_fun, id_eq]
  comp_map g h x := by apply NonEmptyList.ext; simp only [Functor.map, NonEmptyList.toList_map, List.map_map]

-- ============================================================
-- LawfulApplicative
-- ============================================================
-- Bridge lemmas for List (parallel to Array ones)
theorem List.flatMap_flatMap' (xs : List α)
    (f : α → List β) (g : β → List γ) :
    (xs.flatMap f).flatMap g = xs.flatMap (fun a => (f a).flatMap g) := by
  simp [List.flatMap_assoc]

theorem List.singleton_flatMap' (x : α) (f : α → List β) :
    ([x] : List α).flatMap f = f x := by
  simp


instance : LawfulApplicative NonEmptyList where
  seqLeft_eq x y := by
    apply NonEmptyList.ext
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map, NonEmptyList.toList_bind]
    rw [List.flatMap_map]
    rfl

  seqRight_eq x y := by
    apply NonEmptyList.ext
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, NonEmptyList.toList_bind]
    rw [List.flatMap_map]
    simp [List.map_id_fun]

  pure_seq g x := by
    apply NonEmptyList.ext
    simp only [Pure.pure, Seq.seq, NonEmptyList.toList_bind]
    exact List.singleton_flatMap' g (fun f => x.toList.map f)

  map_pure f x := by
    apply NonEmptyList.ext
    simp only [Functor.map, NonEmptyList.toList_map, NonEmptyList.toList_pure]
    simp_all only [List.map_cons, List.map_nil]

  seq_pure f x := by
    apply NonEmptyList.ext
    simp only [Seq.seq, NonEmptyList.toList_bind, NonEmptyList.toList_pure, Functor.map,
               NonEmptyList.toList_map]
    induction f.toList with
    | nil => simp
    | cons h t ih => simp_all only [List.map_cons, List.map_nil, List.flatMap_cons, List.cons_append, List.nil_append]

  seq_assoc x g h := by
    apply NonEmptyList.ext
    simp only [Seq.seq, Functor.map, NonEmptyList.toList_bind]
    simp only [List.flatMap_map, List.map_flatMap]
    rw [List.flatMap_flatMap']
    congr 1; ext h'
    simp [List.flatMap_map, List.map_map]

instance : LawfulMonad NonEmptyList where
  bind_pure_comp f x := by
    apply NonEmptyList.ext
    simp only [bind, NonEmptyList.bind, NonEmptyList.toList_flatten, NonEmptyList.toList_map,
               Functor.map, Pure.pure]
    induction x.toList with
    | nil => simp
    | cons h t ih => simp [ih]

  bind_map f x := by apply NonEmptyList.ext; rfl

  bind_assoc x f g := by
    apply NonEmptyList.ext
    simp only [bind, NonEmptyList.bind, NonEmptyList.toList_flatten, List.flatMap_map]
    rw [List.flatMap_flatMap']

  pure_bind x f := by
    apply NonEmptyList.ext
    simp only [bind, NonEmptyList.bind, NonEmptyList.toList_flatten, Pure.pure]
    exact List.singleton_flatMap' x (fun a => (f a).toList)
