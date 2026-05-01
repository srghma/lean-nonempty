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

@[simp] abbrev toArr (xs : NonEmptyArray α) : Array α :=
  #[xs.head] ++ xs.tail

@[simp] abbrev size (xs : NonEmptyArray α) : Nat := 1 + xs.tail.size

def get (xs : NonEmptyArray α) (i : Fin xs.size) : α :=
  match i with
  | ⟨0,     _⟩ => xs.head
  | ⟨n + 1, h⟩ =>
    have : n < xs.tail.size := by
      -- h is n + 1 < size xs
      -- size xs is 1 + xs.tail.size
      simp only [size] at h
      omega
    xs.tail[n]'this

instance : GetElem? (NonEmptyArray α) Nat α (fun as i => i < as.size) where
  getElem  as i h := as.get ⟨i, h⟩
  getElem? as i   := if h : i < as.size then some (as.get ⟨i, h⟩) else none

instance : LawfulGetElem (NonEmptyArray α) Nat α (fun as i => i < as.size) where

@[simp] theorem size_toArr (as : NonEmptyArray α) : as.toArr.size = as.size := by
  simp only [Array.size_append, Array.size_singleton]

@[simp] theorem toArr_getElem (as : NonEmptyArray α) (i : Nat) (h : i < as.size) :
    as.toArr[i]'(by simp only [size_toArr]; exact h) = as[i] := by
  simp only [GetElem.getElem, get]; split <;> simp_all [Array.getElem_append_left, Array.getElem_append_right]

@[simp] abbrev fromArray? (xs : Array α) : Option (NonEmptyArray α) :=
  if h : xs.size > 0 then some ⟨xs[0]'h, xs[1:]⟩ else none

@[simp] abbrev fromArray! [Inhabited α] (xs : Array α) : NonEmptyArray α :=
  match NonEmptyArray.fromArray? xs with
  | some xs => xs
  | none => panic! "Expected non-empty array"

@[simp] abbrev cons (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  ⟨a, #[xs.head] ++ xs.tail⟩

@[simp] abbrev map (f : α → β) (xs : NonEmptyArray α) : NonEmptyArray β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] def flatten (xs : NonEmptyArray (NonEmptyArray α)) : NonEmptyArray α :=
  let ⟨h, t⟩ := xs
  ⟨h.head, h.tail ++ (t.map toArr).flatten⟩

def foldl {β : Type} (f : β → α → β) (init : β) (xs : NonEmptyArray α) : β :=
  xs.tail.foldl f (f init xs.head)

def mapM [Applicative m] (f : α → m β) (as : NonEmptyArray α) : m (NonEmptyArray β) :=
  (NonEmptyArray.mk · ·) <$> f as.head <*> as.tail.foldl (fun macc x => (·.push ·) <$> macc <*> f x) (pure #[])

def mapFinIdxM [Monad m] (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (NonEmptyArray β) :=
  return ⟨← f 0 as.head (by simp [size]; omega),
          ← as.tail.mapFinIdxM (fun i a h => f (i + 1) a (by simp [size] at h ⊢; omega))⟩

def mapIdxM [Monad m] (as : NonEmptyArray α) (f : Nat → α → m β) : m (NonEmptyArray β) :=
  as.mapFinIdxM (fun i a _ => f i a)

def mapIdx (as : NonEmptyArray α) (f : Nat → α → β) : NonEmptyArray β :=
  Id.run (as.mapIdxM (fun i a => pure (f i a)))

def mapFinIdx (as : NonEmptyArray α) (f : (i : Nat) → α → (h : i < as.size) → β) : NonEmptyArray β :=
  Id.run (as.mapFinIdxM (fun i a h => pure (f i a h)))

--------------------------------------------------------------------------------
-- API Mapped from standard `Array`
--------------------------------------------------------------------------------

@[simp] def toList (xs : NonEmptyArray α) : List α := xs.head :: xs.tail.toList
def toListImpl (xs : NonEmptyArray α) : List α := xs.toList
def toListAppend (xs : NonEmptyArray α) (l : List α) : List α := xs.toList ++ l

@[simp] def isEmpty (_xs : NonEmptyArray α) : Bool := false

def back (xs : NonEmptyArray α) : α := if h : xs.tail.size > 0 then xs.tail.back h else xs.head
def back! [Inhabited α] (xs : NonEmptyArray α) : α := xs.back
def back? (xs : NonEmptyArray α) : Option α := some xs.back

def singleton (a : α) : NonEmptyArray α := ⟨a, #[]⟩

def ofFn {n : Nat} (f : Fin (n + 1) → α) : NonEmptyArray α :=
  ⟨f ⟨0, by omega⟩, Array.ofFn (fun (i : Fin n) => f ⟨i.val + 1, by omega⟩)⟩

-- Modifications returning NonEmptyArray
def push (xs : NonEmptyArray α) (a : α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail.push a⟩

def set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.tail⟩
  else
    have : i - 1 < xs.tail.size := by simp [size] at h; omega
    ⟨xs.head, xs.tail.set (i - 1) a this⟩

def set! (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i < xs.size then xs.set i a h else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def modify (xs : NonEmptyArray α) (i : Nat) (f : α → α) : NonEmptyArray α :=
  if h : i < xs.size then
    if h0 : i = 0 then ⟨f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp [size] at h; omega
      ⟨xs.head, xs.tail.modify (i - 1) f⟩
  else xs

def modifyM [Monad m] (xs : NonEmptyArray α) (i : Nat) (f : α → m α) : m (NonEmptyArray α) := do
  if h : i < xs.size then
    if h0 : i = 0 then return ⟨← f xs.head, xs.tail⟩
    else
      have : i - 1 < xs.tail.size := by simp [size] at h; omega
      return ⟨xs.head, ← xs.tail.modifyM (i - 1) f⟩
  else return xs

def swap (xs : NonEmptyArray α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) : NonEmptyArray α :=
  if h0 : i = 0 ∧ j = 0 then xs
  else if h1 : i = 0 then
    let j' := j - 1; have : j' < xs.tail.size := by simp [size] at hj; omega
    ⟨xs.tail[j'], xs.tail.set j' xs.head this⟩
  else if h2 : j = 0 then
    let i' := i - 1; have : i' < xs.tail.size := by simp [size] at hi; omega
    ⟨xs.tail[i'], xs.tail.set i' xs.head this⟩
  else
    let i' := i - 1; have hi' : i' < xs.tail.size := by simp [size] at hi; omega
    let j' := j - 1; have hj' : j' < xs.tail.size := by simp [size] at hj; omega
    ⟨xs.head, xs.tail.swap i' j' hi' hj'⟩

def swap! (xs : NonEmptyArray α) (i j : Nat) : NonEmptyArray α :=
  if hi : i < xs.size then
    if hj : j < xs.size then xs.swap i j hi hj
    else
      have : Inhabited (NonEmptyArray α) := ⟨xs⟩
      panic! "invalid index"
  else
    have : Inhabited (NonEmptyArray α) := ⟨xs⟩
    panic! "invalid index"

def swapAt (xs : NonEmptyArray α) (i : Nat) (v : α) (hi : i < xs.size) : α × NonEmptyArray α :=
  let e := xs.get ⟨i, hi⟩
  (e, xs.set i v hi)

def swapAt! (xs : NonEmptyArray α) (i : Nat) (v : α) : α × NonEmptyArray α :=
  if hi : i < xs.size then xs.swapAt i v hi
  else
    have : Inhabited (α × NonEmptyArray α) := ⟨(v, xs)⟩
    panic! "invalid index"

def fromArray (xs : Array α) (h : xs.size > 0) : NonEmptyArray α :=
  ⟨xs[0]'h, xs.extract 1 xs.size⟩

@[simp] theorem toArr_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).toArr = xs := by
    simp_all only [toArr]
    aesop?

@[simp] theorem size_fromArray (xs : Array α) (h : xs.size > 0) :
  (fromArray xs h).size = xs.size := by
    simp_all only [size]
    aesop?

@[simp] theorem getElem_fromArray (xs : Array α) (h : xs.size > 0) (i : Nat) (hi : i < (fromArray xs h).size) :
  (fromArray xs h)[i] = xs[i]'(by simpa using hi) := by
    simp_all only [size]
    aesop?

def reverse (xs : NonEmptyArray α) : NonEmptyArray α :=
  let arr := xs.toArr.reverse
  have : arr.size > 0 := by simp [arr]
  fromArray arr this

def append (xs ys : NonEmptyArray α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArr⟩

def appendArray (xs : NonEmptyArray α) (ys : Array α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys⟩

def appendList (xs : NonEmptyArray α) (ys : List α) : NonEmptyArray α :=
  ⟨xs.head, xs.tail ++ ys.toArray⟩

def insertIdx (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i ≤ xs.size) : NonEmptyArray α :=
  if h0 : i = 0 then
    ⟨a, xs.toArr⟩
  else
    have : i - 1 ≤ xs.tail.size := by simp [size] at h; omega
    ⟨xs.head, xs.tail.insertIdx (i - 1) a this⟩

def insertIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) (a : α) : NonEmptyArray α :=
  if h : i ≤ xs.size then xs.insertIdx i a h else xs

def replace [BEq α] (xs : NonEmptyArray α) (a b : α) : NonEmptyArray α :=
  if xs.head == a then ⟨b, xs.tail⟩
  else ⟨xs.head, xs.tail.replace a b⟩

def zipWith (f : α → β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  ⟨f as.head bs.head, as.tail.zipWith f bs.tail⟩

def zipWithAll (f : Option α → Option β → γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray γ :=
  match fromArray? (as.toArr.zipWithAll f bs.toArr) with
  | some res => res
  | none => ⟨f (some as.head) (some bs.head), #[]⟩

def zipWithM [Monad m] (f : α → β → m γ) (as : NonEmptyArray α) (bs : NonEmptyArray β) : m (NonEmptyArray γ) := do
  return ⟨← f as.head bs.head, ← as.tail.zipWithM f bs.tail⟩

def zip (as : NonEmptyArray α) (bs : NonEmptyArray β) : NonEmptyArray (α × β) :=
  as.zipWith Prod.mk bs

def zipIdx (xs : NonEmptyArray α) (start := 0) : NonEmptyArray (α × Nat) :=
  ⟨(xs.head, start), xs.tail.zipIdx (start + 1)⟩

def unzip (as : NonEmptyArray (α × β)) : NonEmptyArray α × NonEmptyArray β :=
  let (a, b) := as.toArr.unzip
  (match fromArray? a with | some a => a | none => ⟨as.head.1, #[]⟩,
   match fromArray? b with | some b => b | none => ⟨as.head.2, #[]⟩)

def flatMap (f : α → Array β) (xs : NonEmptyArray α) : Array β := xs.toArr.flatMap f
def flatMapNonEmpty (f : α → NonEmptyArray β) (xs : NonEmptyArray α) : NonEmptyArray β := flatten (xs.map f)

def leftpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.leftpad n a) with
  | some res => res
  | none => xs

def rightpad (n : Nat) (a : α) (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? (xs.toArr.rightpad n a) with
  | some res => res
  | none => xs

-- Functions returning potentially empty Array
def pop (xs : NonEmptyArray α) : Array α := xs.toArr.pop
def shrink (xs : NonEmptyArray α) (n : Nat) : Array α := xs.toArr.shrink n
def take (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.take i
def takeWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.takeWhile p
def drop (xs : NonEmptyArray α) (i : Nat) : Array α := xs.toArr.drop i
def filter (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.filter p
def filterMap (f : α → Option β) (xs : NonEmptyArray α) : Array β := xs.toArr.filterMap f

def eraseIdx (xs : NonEmptyArray α) (i : Nat) (h : i < xs.size) : Array α :=
  if h0 : i = 0 then
    xs.tail
  else
    have : i - 1 < xs.tail.size := by simp [size] at h; omega
    #[xs.head] ++ xs.tail.eraseIdx (i - 1) this

def eraseIdxIfInBounds (xs : NonEmptyArray α) (i : Nat) : Array α :=
  xs.toArr.eraseIdxIfInBounds i

def erase [BEq α] (xs : NonEmptyArray α) (a : α) : Array α := xs.toArr.erase a
def eraseP (xs : NonEmptyArray α) (p : α → Bool) : Array α := xs.toArr.eraseP p
def popWhile (p : α → Bool) (xs : NonEmptyArray α) : Array α := xs.toArr.popWhile p
def reduceOption (xs : NonEmptyArray (Option α)) : Array α := xs.toArr.reduceOption
def partition (p : α → Bool) (xs : NonEmptyArray α) : Array α × Array α := xs.toArr.partition p

def getEvenElems (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.getEvenElems with
  | some res => res
  | none => ⟨xs.head, #[]⟩

def eraseReps [BEq α] (xs : NonEmptyArray α) : NonEmptyArray α :=
  match fromArray? xs.toArr.eraseReps with
  | some res => res
  | none => ⟨xs.head, #[]⟩

-- Queries / Searches
def foldr {β} (f : α → β → β) (init : β) (xs : NonEmptyArray α) : β := xs.toArr.foldr f init
def any (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.any p
def all (xs : NonEmptyArray α) (p : α → Bool) : Bool := xs.toArr.all p
def contains [BEq α] (xs : NonEmptyArray α) (a : α) : Bool := xs.toArr.contains a
def elem [BEq α] (a : α) (xs : NonEmptyArray α) : Bool := xs.toArr.elem a
def countP (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.countP p
def count [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.count a
def sum [Add α] [Zero α] (xs : NonEmptyArray α) : α := xs.toArr.sum
def find? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.find? p
def findSome? {β} (f : α → Option β) (xs : NonEmptyArray α) : Option β := xs.toArr.findSome? f
def findRev? (p : α → Bool) (xs : NonEmptyArray α) : Option α := xs.toArr.findRev? p
def findIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option Nat := xs.toArr.findIdx? p
def findIdx (p : α → Bool) (xs : NonEmptyArray α) : Nat := xs.toArr.findIdx p
def findFinIdx? (p : α → Bool) (xs : NonEmptyArray α) : Option (Fin xs.size) :=
  xs.toArr.findFinIdx? p |>.map (fun ⟨i, h⟩ => ⟨i, by simp [size] at h ⊢; omega⟩)
def finIdxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option (Fin xs.size) :=
  xs.toArr.finIdxOf? a |>.map (fun ⟨i, h⟩ => ⟨i, by simp [size] at h ⊢; omega⟩)
def idxOf? [BEq α] (xs : NonEmptyArray α) (a : α) : Option Nat := xs.toArr.idxOf? a
def idxOf [BEq α] (a : α) (xs : NonEmptyArray α) : Nat := xs.toArr.idxOf a
def getMax (xs : NonEmptyArray α) (lt : α → α → Bool) : α := xs.tail.foldl (fun best a => if lt best a then a else best) xs.head
def isEqv (xs ys : NonEmptyArray α) (p : α → α → Bool) : Bool := xs.toArr.isEqv ys.toArr p
def isPrefixOf [BEq α] (xs ys : NonEmptyArray α) : Bool := xs.toArr.isPrefixOf ys.toArr
def allDiff [BEq α] (xs : NonEmptyArray α) : Bool := xs.toArr.allDiff

-- Monadic operations
def forM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forM f
def forRevM [Monad m] (xs : NonEmptyArray α) (f : α → m PUnit) : m PUnit := xs.toArr.forRevM f
def foldlM [Monad m] {β} (f : β → α → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldlM f init
def foldrM [Monad m] {β} (f : α → β → m β) (init : β) (xs : NonEmptyArray α) : m β := xs.toArr.foldrM f init
def anyM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.anyM p
def allM [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m Bool := xs.toArr.allM p
def findM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option α) := xs.toArr.findM? p
def findSomeM? [Monad m] {β} (f : α → m (Option β)) (xs : NonEmptyArray α) : m (Option β) := xs.toArr.findSomeM? f
def findIdxM? [Monad m] (p : α → m Bool) (xs : NonEmptyArray α) : m (Option Nat) := xs.toArr.findIdxM? p

instance : Append (NonEmptyArray α) := ⟨append⟩
instance : HAppend (NonEmptyArray α) (Array α) (NonEmptyArray α) := ⟨appendArray⟩
instance : HAppend (NonEmptyArray α) (List α) (NonEmptyArray α) := ⟨appendList⟩

@[simp] theorem toArr_singleton (a : α) : (singleton a).toArr = #[a] := by
  simp_all only [toArr, Array.append_eq_toArray_iff, List.cons_append, List.nil_append, List.cons.injEq, Array.toList_eq_nil_iff]
  apply And.intro
  · rfl
  · rfl
@[simp] theorem toArr_push (xs : NonEmptyArray α) (a : α) : (xs.push a).toArr = xs.toArr.push a := by
  simp_all only [toArr, Array.push_append]
  rfl
@[simp] theorem toArr_map (f : α → β) (xs : NonEmptyArray α) : (xs.map f).toArr = xs.toArr.map f := by
  simp_all only [toArr, Array.map_append, List.map_toArray, List.map_cons, List.map_nil]
@[simp] theorem size_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).size = n + 1 := by
  simp_all only [size]
  aesop?
@[simp] theorem toArr_ofFn {n : Nat} (f : Fin (n + 1) → α) : (ofFn f).toArr = Array.ofFn f := by
  simp_all only [toArr]
  aesop?
@[simp] theorem size_append (xs ys : NonEmptyArray α) : (xs ++ ys).size = xs.size + ys.size := by
  simp_all only [size]
  aesop?
@[simp] theorem toArr_append (xs ys : NonEmptyArray α) : (xs ++ ys).toArr = xs.toArr ++ ys.toArr := by
  simp_all only [toArr, Array.append_singleton_assoc, Array.push_append, Array.append_assoc]
  aesop?
@[simp] theorem toArr_set (xs : NonEmptyArray α) (i : Nat) (a : α) (h : i < xs.size) :
  (xs.set i a h).toArr = xs.toArr.set i a (by simp_all only [size, toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]) := by
    simp_all only [toArr]
    aesop?

@[simp] theorem size_reverse (xs : NonEmptyArray α) : xs.reverse.size = xs.size := by
  simp_all only [size, Nat.add_left_cancel_iff]
  aesop?
@[simp] theorem toArr_reverse (xs : NonEmptyArray α) : xs.reverse.toArr = xs.toArr.reverse := by
  simp_all only [toArr, Array.reverse_append, List.reverse_toArray, List.reverse_cons, List.reverse_nil, List.nil_append, Array.append_singleton]
  aesop?



structure Mem (as : NonEmptyArray α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (NonEmptyArray α) where
  mem := Mem

@[simp] theorem toArr_toList (xs : NonEmptyArray α) : xs.toArr.toList = xs.toList := by
  simp only [Array.toList_append]
  rfl

instance [Monad m] : ForIn m (NonEmptyArray α) α where
  forIn xs init f := forIn xs.toArr init f

theorem mem_def {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a ∈ as.toArr := by
  constructor
  · intro ⟨h⟩; rw [Array.mem_def, toArr_toList]; exact h
  · intro h; rw [Array.mem_def, toArr_toList] at h; exact ⟨h⟩

theorem mem_head_or_tail {a : α} {as : NonEmptyArray α} : a ∈ as ↔ a = as.head ∨ a ∈ as.tail := by
  constructor
  · intro ⟨h⟩; exact (List.mem_cons.1 h).imp id (Array.mem_def.2)
  · intro h; exact ⟨List.mem_cons.2 (h.imp id (Array.mem_def.1))⟩

instance [Monad m] : ForIn' m (NonEmptyArray α) α inferInstance where
  forIn' xs init f := forIn' xs.toArr init (fun a h => f a ⟨by
    rw [Array.mem_def, toArr_toList] at h
    exact h
  ⟩)

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

/--
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

@[simp] theorem NonEmptyArray.toArr_flatten (xs : NonEmptyArray (NonEmptyArray α)) :
    xs.flatten.toArr = (xs.toArr.map toArr).flatten := by
  cases xs with | mk h t =>
  simp [flatten]

@[simp] theorem NonEmptyArray.flatten_flatten_eq (xs : NonEmptyArray (NonEmptyArray (NonEmptyArray α))) :
    NonEmptyArray.flatten (NonEmptyArray.flatten xs) =
    NonEmptyArray.flatten (Functor.map NonEmptyArray.flatten xs) := by
  obtain ⟨⟨hh, ht⟩, t⟩ := xs
  simp_all [NonEmptyArray.flatten, Functor.map]
  congr 2
  rw [Array.flatten_flatten]
  have : (Array.map Array.flatten (Array.map (Array.map toArr ∘ toArr) t)) = Array.map (toArr ∘ flatten) t := by
    simp only [Array.map_map, Function.comp_def]
    congr 1
    funext x
    exact (toArr_flatten x).symm
  rw [this]

-- seq unfolds to flatten of map
theorem seq_def (f : NonEmptyArray (α → β)) (x : NonEmptyArray α) :
    f <*> x = NonEmptyArray.flatten (Functor.map (fun g => Functor.map g x) f) := rfl

@[simp] theorem map_id (xs : NonEmptyArray α) : (id <$> xs) = xs := LawfulFunctor.id_map xs
@[simp] theorem map_map (f : α → β) (g : β → γ) (xs : NonEmptyArray α) : (g <$> f <$> xs) = ((g ∘ f) <$> xs) := (LawfulFunctor.comp_map f g xs).symm

end NonEmptyArray

instance : LawfulApplicative NonEmptyArray where
  map_pure g x := by
    ext <;> simp [Functor.map, pure]

  pure_seq g x := by
    simp [NonEmptyArray.seq_def, pure, Functor.map, NonEmptyArray.flatten]

  seq_pure f x := by
    cases f with | mk h t =>
    simp [NonEmptyArray.seq_def, pure, Functor.map, NonEmptyArray.flatten, NonEmptyArray.map, Function.comp_def]

  seq_assoc x g f := by
    obtain ⟨xh, xt⟩ := x
    obtain ⟨gh, gt⟩ := g
    obtain ⟨fh, ft⟩ := f
    simp [Functor.map, Seq.seq, NonEmptyArray.flatten,
          Function.comp_def, Array.map_map]
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
          Function.const, Array.map_map, Function.comp_def]

  seqRight_eq x y := by
    obtain ⟨xh, xt⟩ := x
    obtain ⟨yh, yt⟩ := y
    simp [SeqRight.seqRight, Functor.map, Seq.seq, NonEmptyArray.flatten,
          Function.const, id]


instance : Monad NonEmptyArray where
  bind xs f := NonEmptyArray.flatten (Functor.map f xs)

instance : LawfulMonad NonEmptyArray where
  pure_bind x f := by
    simp_all only [bind, NonEmptyArray.flatten, pure, NonEmptyArray.map_head, Array.map,
      NonEmptyArray.map_tail, List.mapM_toArray, List.mapM_nil, Id.run_map,
      List.idRun_mapM, Array.flatten_toArray, List.map_map]
    rfl
  bind_pure_comp f x := by
    cases x with | mk xh xt =>
    simp [Bind.bind, pure, Functor.map, NonEmptyArray.flatten]
    exact _root_.Array.flatten_map_singleton xt f
  bind_map f x := rfl
  bind_assoc x f g := by
    cases x with | mk xh xt =>
    simp [Bind.bind, NonEmptyArray.flatten, Functor.map, NonEmptyArray.map, Function.comp_def]
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

#guard #![1, 2, 3].head = 1
#guard #![1, 2, 3].tail = #[2, 3]
#guard #![1, 2, 3].size = 3
#guard #![1, 2, 3][0] = 1
#guard #![1, 2, 3][1] = 2
#guard #![1, 2, 3][2] = 3

end

end NonEmpty.CorrectByConstruction.Array
