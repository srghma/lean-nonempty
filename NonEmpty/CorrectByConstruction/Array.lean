module
import Aesop
import Init.Data.Array.Lemmas

public section

-- why this is needed? for https://github.com/leanprover/lean4/issues/4964#issuecomment-4337841019
namespace NonEmpty.CorrectByConstruction.Array

@[ext]
structure NonEmptyArray (α : Type u) where
  head : α
  tail : Array α
  deriving Hashable, Ord, Repr, BEq, DecidableEq

instance [ToString α] : ToString (NonEmptyArray α) where
  toString a := "#!" ++ toString (#[a.head] ++ a.tail)

instance [Inhabited α] : Inhabited (NonEmptyArray α) where
  default := ⟨default, #[]⟩

namespace NonEmptyArray

@[simp] def toArray (xs : NonEmptyArray α) : Array α :=
  #[xs.head] ++ xs.tail

abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs[0]'h, xs[1:]⟩ else none

abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match NonEmptyArray.fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty array"

@[simp] abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨a, #[xs.head] ++ xs.tail⟩

@[simp] abbrev size (xs : NonEmptyArray α) : Nat := 1 + xs.tail.size

def get (xs : NonEmptyArray α) (i : Fin (1 + xs.tail.size)) : α :=
  match i with
  | ⟨0,     _⟩ => xs.head
  | ⟨n + 1, h⟩ => xs.tail[n]' (by omega)

abbrev get? (xs : NonEmptyArray α) (i : Nat) : Option α :=
  if i == 0 then some xs.head else xs.tail[i - 1]?

@[simp] abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyArray (NonEmptyArray α)) : NonEmptyArray α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ (t.map toArray).flatten⟩

def foldl {β : Type} (f : β → α → β) (init : β) (xs : NonEmptyArray α) : β :=
  xs.tail.foldl f (f init xs.head)

def mapM [Applicative m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  (NonEmptyArray.mk · ·) <$> f as.head <*> as.tail.foldl (fun macc x => (·.push ·) <$> macc <*> f x) (pure #[])

end NonEmptyArray


instance : Functor NonEmptyArray where
  map := NonEmptyArray.map

instance : LawfulFunctor NonEmptyArray where
  id_map x := by ext <;> simp_all only [Functor.map, id_eq, Array.map_id_fun, id_eq]
  comp_map f g x := by ext <;> simp_all only [Functor.map, Function.comp_apply, _root_.Array.map_map]
  map_const := rfl

instance : Applicative NonEmptyArray where
  pure a := ⟨a, #[]⟩
  seq f x := NonEmptyArray.flatten (Functor.map (fun g => Functor.map g (x ())) f)

namespace NonEmptyArray

-- Helps prove seq_pure and seq_assoc
@[simp] theorem map_tail (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).tail = xs.tail.map f := rfl
@[simp] theorem map_head (f : α → β) (xs : NonEmptyArray α) : (Functor.map f xs).head = f xs.head := rfl

/-
Helper lemmas
-/
@[simp] theorem _root_.Array.flatten_map_singleton (t : Array α) (f : α → β) :
    (t.map (fun a => #[f a])).flatten = t.map f := by
  have H : (t.map (fun a => #[f a])).flatten.toList = (t.map f).toList := by
    simp [Array.toList_flatten, Array.toList_map, Function.comp_def]
    induction t.toList with
    | nil => rfl
    | cons x xs ih => simp [ih]
  cases h₁ : (t.map (fun a => #[f a])).flatten with | mk l₁ =>
  cases h₂ : t.map f with | mk l₂ =>
  simp_all


@[simp] theorem Array.append_flatten_assoc (a : Array α) (b : Array (Array α)) (c : Array (Array α)) :
    a ++ (b ++ c).flatten = a ++ b.flatten ++ c.flatten := by
  simp [Array.flatten_append, Array.append_assoc]

@[simp] theorem NonEmptyArray.toArray_flatten (xs : NonEmptyArray (NonEmptyArray α)) :
    xs.flatten.toArray = (xs.toArray.map toArray).flatten := by
  cases xs with | mk h t =>
  simp [toArray, flatten]

@[simp] theorem NonEmptyArray.flatten_flatten_eq (xs : NonEmptyArray (NonEmptyArray (NonEmptyArray α))) :
    NonEmptyArray.flatten (NonEmptyArray.flatten xs) =
    NonEmptyArray.flatten (Functor.map NonEmptyArray.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all [NonEmptyArray.flatten, Functor.map]
  congr 2
  rw [Array.flatten_flatten]
  have : (Array.map Array.flatten (Array.map (Array.map toArray ∘ toArray) t)) = Array.map (toArray ∘ flatten) t := by
    simp only [Array.map_map, Function.comp_def]
    congr 1
    funext x
    exact (toArray_flatten x).symm
  rw [this]

-- seq unfolds to flatten of map
theorem seq_def (f : NonEmptyArray (α → β)) (x : NonEmptyArray α) :
    f <*> x = NonEmptyArray.flatten (Functor.map (fun g => Functor.map g x) f) := rfl

end NonEmptyArray

instance : LawfulApplicative NonEmptyArray where
  map_pure g x := by
    ext <;> simp [Functor.map, pure]

  pure_seq g x := by
    simp [NonEmptyArray.seq_def, pure, Functor.map, NonEmptyArray.flatten]

  seq_pure f x := by
    cases f with | mk h t =>
    simp [NonEmptyArray.seq_def, pure, Functor.map, NonEmptyArray.flatten, NonEmptyArray.map, NonEmptyArray.toArray, Function.comp_def]

  seq_assoc x g f := by
    obtain ⟨xh, xt⟩ := x
    obtain ⟨gh, gt⟩ := g
    obtain ⟨fh, ft⟩ := f
    simp [Functor.map, Seq.seq, NonEmptyArray.flatten,
          Function.comp_def, NonEmptyArray.toArray, Array.map_map]
    congr 1
    rw [Array.flatten_flatten]
    have : Array.map Array.flatten (Array.map (fun x => #[#[x (gh xh)] ++ Array.map (fun x_1 => x (gh x_1)) xt] ++ Array.map (fun x_1 => #[x (x_1 xh)] ++ Array.map (fun x_2 => x (x_1 x_2)) xt) gt) ft) = Array.map (fun x => #[x (gh xh)] ++ (Array.map (fun x_1 => x (gh x_1)) xt ++ (Array.map (fun x_1 => #[x (x_1 xh)] ++ Array.map (fun x_2 => x (x_1 x_2)) xt) gt).flatten)) ft := by
      simp only [Array.map_map, Function.comp_def]
      congr 1
      funext x
      simp [Array.flatten_append, Array.append_assoc]
    rw [this]

  seqLeft_eq x y := by
    obtain ⟨xh, xt⟩ := x
    obtain ⟨yh, yt⟩ := y
    simp [SeqLeft.seqLeft, Functor.map, Seq.seq, NonEmptyArray.flatten,
          Function.const, NonEmptyArray.toArray, Array.map_map, Function.comp_def]

  seqRight_eq x y := by
    obtain ⟨xh, xt⟩ := x
    obtain ⟨yh, yt⟩ := y
    simp [SeqRight.seqRight, Functor.map, Seq.seq, NonEmptyArray.flatten,
          Function.const, id, NonEmptyArray.toArray]


instance : Monad NonEmptyArray where
  bind xs f := NonEmptyArray.flatten (Functor.map f xs)

instance : LawfulMonad NonEmptyArray where
  pure_bind x f := by
    simp_all only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.map_head, Array.map,
      NonEmptyArray.toArray, NonEmptyArray.map_tail, List.mapM_toArray, List.mapM_nil, Id.run_map,
      List.idRun_mapM, Array.flatten_toArray, List.map_map]
    rfl
  bind_pure_comp f x := by
    cases x with | mk xh xt =>
    simp [Bind.bind, pure, Functor.map, NonEmptyArray.flatten]
    exact _root_.Array.flatten_map_singleton xt f
  bind_map f x := rfl
  bind_assoc x f g := by
    cases x with | mk xh xt =>
    simp [Bind.bind, NonEmptyArray.flatten, Functor.map, NonEmptyArray.map, NonEmptyArray.toArray, Function.comp_def]
    congr 1
    rw [Array.flatten_flatten]
    have : Array.map Array.flatten (Array.map (fun x => #[#[(g (f x).head).head] ++ (g (f x).head).tail] ++ Array.map (fun x => #[(g x).head] ++ (g x).tail) (f x).tail) xt) = Array.map (fun x => #[(g (f x).head).head] ++ ((g (f x).head).tail ++ (Array.map (fun x => #[(g x).head] ++ (g x).tail) (f x).tail).flatten)) xt := by
      simp only [Array.map_map, Function.comp_def]
      congr 1
      funext a
      simp [Array.flatten_append, Array.append_assoc]
    rw [this]
section

-- Macro for creating non-empty list literals
syntax "#![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#![])                           => Lean.Macro.throwError "#! literal must contain at least one element"
  | `(#![ $head:term ])               => ``(NonEmptyArray.mk $head #[])
  | `(#![ $head:term, $tail:term,* ]) => ``(NonEmptyArray.mk $head #[$tail,*])

example : NonEmptyArray Nat := #![1, 2, 3]
example : NonEmptyArray String := #!["hello", "world"]
example : NonEmptyArray Nat := #![10]

#guard (#![1, 2, 3]).head = 1
#guard (#![1, 2, 3]).tail = #[2, 3]
#guard (#![1, 2, 3]).size = 3

end

end NonEmpty.CorrectByConstruction.Array
