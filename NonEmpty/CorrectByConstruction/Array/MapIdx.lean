
-- module

import Aesop
import Init
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Omega
import Init.Data.List.MapIdx
import Init.Data.Array.OfFn
import NonEmpty.CorrectByConstruction.Array.Basic

namespace NonEmpty.CorrectByConstruction.Array

open NonEmptyArray

theorem toArr_inj {xs ys : NonEmptyArray α} : xs.toArr = ys.toArr ↔ xs = ys := by
  cases xs; cases ys
  simp only [toArr, mk.injEq]
  constructor
  · intro h
    have ⟨h1, h2⟩ := Array.append_inj' h (by have hsz := congrArg Array.size h; simp at hsz; omega)
    exact ⟨Array.singleton_inj.mp h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### mapFinIdx -/

private theorem mapFinIdx_head {xs : NonEmptyArray α} {f : (i : Nat) → α → i < xs.size → β} :
    (xs.mapFinIdx f).head = f 0 xs.head (by simp only [size]; omega) := rfl

private theorem mapFinIdx_tail {xs : NonEmptyArray α} {f : (i : Nat) → α → i < xs.size → β} :
    (xs.mapFinIdx f).tail =
      xs.tail.mapFinIdx (fun i a h => f (i + 1) a (by simp only [size] at h ⊢; omega)) := rfl

private theorem mapIdx_head {xs : NonEmptyArray α} {f : Nat → α → β} :
    (xs.mapIdx f).head = f 0 xs.head := rfl

private theorem mapIdx_tail {xs : NonEmptyArray α} {f : Nat → α → β} :
    (xs.mapIdx f).tail = xs.tail.mapIdx (fun i => f (i + 1)) := rfl

@[simp] theorem toArr_mapFinIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    (xs.mapFinIdx f).toArr = xs.toArr.mapFinIdx (fun i a h => f i a (by simpa [size, toArr] using h)) := by
  simp only [toArr, mapFinIdx_head, mapFinIdx_tail, Array.mapFinIdx_append, Array.mapFinIdx_singleton, Array.size_singleton]

@[simp, grind =] theorem size_mapFinIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    (xs.mapFinIdx f).size = xs.size := by
  simp only [size, mapFinIdx_tail, _root_.Array.size_mapFinIdx]

theorem mapFinIdx_induction {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β}
    {motive : Nat → Prop} (h0 : motive 0)
    {p : (i : Nat) → β → (h : i < xs.size) → Prop}
    (hs : ∀ i h, motive i → p i (f i xs[i] h) h ∧ motive (i + 1)) :
    motive xs.size ∧ ∃ eq : (xs.mapFinIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapFinIdx f)[i]) h := by
  have ⟨h_mot, h_eq, h_get⟩ := _root_.Array.mapFinIdx_induction xs.toArr
    (motive := motive)
    (h0 := h0)
    (f := fun i a h => f i a (by simpa [size, toArr] using h))
    (p := fun i b h => p i b (by simpa [size, toArr] using h))
    (by
      intro i h hm
      simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add] at h
      have ⟨h_p, h_mot'⟩ := hs i (by omega) hm
      refine ⟨?_, h_mot'⟩
      simp_all only [size, toArr, toArr_getElem])
  have hsz : (xs.mapFinIdx f).size = xs.size := size_mapFinIdx
  refine ⟨by simpa [size_toArr] using h_mot, hsz, ?_⟩
  intro i h
  have hg := h_get i (by simpa [size_toArr] using h)
  rw [← toArr_getElem (as := xs.mapFinIdx f) i (by rw [hsz]; simpa [size_toArr] using h)]
  simp_all only [size, toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, _root_.Array.getElem_mapFinIdx, toArr_getElem, toArr_mapFinIdx]

theorem mapFinIdx_spec {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β}
    {p : (i : Nat) → β → (h : i < xs.size) → Prop} (hs : ∀ i h, p i (f i xs[i] h) h) :
    ∃ eq : (xs.mapFinIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapFinIdx f)[i]) h :=
  (mapFinIdx_induction (motive := fun _ => True) (h0 := trivial) (hs := fun i h _ => ⟨hs i h, trivial⟩)).2

@[simp, grind =] theorem size_zipIdx {xs : NonEmptyArray α} {k : Nat} : (xs.zipIdx k).size = xs.size := by
  simp only [size, zipIdx, _root_.Array.size_zipIdx]

@[simp, grind =] theorem getElem_mapFinIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {i : Nat}
    (h : i < (xs.mapFinIdx f).size) :
    (xs.mapFinIdx f)[i] = f i (xs[i]'(by simp_all only [size, size_mapFinIdx])) (by simp_all only [size,
      size_mapFinIdx]) :=
  (mapFinIdx_spec (p := fun i b h => b = f i xs[i] h) fun _ _ => rfl).2 i (by simp_all only [size,
    size_mapFinIdx])

@[simp, grind =] theorem getElem?_mapFinIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {i : Nat} :
    (xs.mapFinIdx f)[i]? =
      xs[i]?.pbind fun b h => some <| f i b (getElem?_eq_some_iff.1 h).1 := by
  simp only [getElem?_def, size_mapFinIdx, getElem_mapFinIdx]
  split <;> simp_all

@[simp, grind =] theorem toList_mapFinIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    (xs.mapFinIdx f).toList = xs.toList.mapFinIdx (fun i a h => f i a (by
    simp_all only [toList, List.length_cons, Array.length_toList, size]
    grind only)) := by
  apply List.ext_getElem
  · unfold size toList mapFinIdx; simp only [_root_.Array.toList_mapFinIdx, Array.length_toList,
    List.length_cons, List.length_mapFinIdx, List.mapFinIdx_cons]
  · intro i h1 h2
    simp only [toList, mapFinIdx, _root_.Array.toList_mapFinIdx, Array.length_toList, List.length_cons, List.mapFinIdx_cons]

/-! ### mapIdx -/

theorem mapIdx_induction {f : Nat → α → β} {xs : NonEmptyArray α}
    {motive : Nat → Prop} (h0 : motive 0)
    {p : (i : Nat) → β → (h : i < xs.size) → Prop}
    (hs : ∀ i h, motive i → p i (f i xs[i]) h ∧ motive (i + 1)) :
    motive xs.size ∧ ∃ eq : (xs.mapIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapIdx f)[i]) h :=
  mapFinIdx_induction (f := fun i a _ => f i a) (h0 := h0) (p := p) (hs := hs)

theorem mapIdx_spec {f : Nat → α → β} {xs : NonEmptyArray α}
    {p : (i : Nat) → β → (h : i < xs.size) → Prop} (hs : ∀ i h, p i (f i xs[i]) h) :
    ∃ eq : (xs.mapIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapIdx f)[i]) h :=
  (mapIdx_induction (motive := fun _ => True) (h0 := trivial) (hs := fun i h _ => ⟨hs i h, trivial⟩)).2

@[simp, grind =] theorem size_mapIdx {f : Nat → α → β} {xs : NonEmptyArray α} : (xs.mapIdx f).size = xs.size :=
  (mapIdx_spec (p := fun _ _ _ => True) (hs := fun _ _ => trivial)).1

@[simp, grind =] theorem getElem_mapIdx {f : Nat → α → β} {xs : NonEmptyArray α} {i : Nat}
    (h : i < (xs.mapIdx f).size) :
    (xs.mapIdx f)[i] = f i (xs[i]'(by simp_all only [size, size_mapIdx])) :=
  (mapIdx_spec (p := fun i b h => b = f i xs[i]) fun _ _ => rfl).2 i (by simp_all only [size,
    size_mapIdx])

@[simp, grind =] theorem getElem?_mapIdx {f : Nat → α → β} {xs : NonEmptyArray α} {i : Nat} :
    (xs.mapIdx f)[i]? =
      xs[i]?.map (f i) := by
  simp only [size, getElem?_def, size_mapIdx, getElem_mapIdx, Option.map_dif]

@[simp, grind =] theorem toList_mapIdx {f : Nat → α → β} {xs : NonEmptyArray α} :
    (xs.mapIdx f).toList = xs.toList.mapIdx (fun i a => f i a) := by
  apply List.ext_getElem
  · simp only [toList, mapIdx, _root_.Array.toList_mapIdx, List.length_cons, List.length_mapIdx,
    Array.length_toList, List.mapIdx_cons]
  · intro i h1 h2
    cases i with
    | zero => simp only [toList, mapIdx, _root_.Array.toList_mapIdx, List.getElem_cons_zero,
      List.mapIdx_cons]
    | succ i => simp only [toList, mapIdx, _root_.Array.toList_mapIdx, List.getElem_cons_succ,
      List.getElem_mapIdx, Array.getElem_toList, List.mapIdx_cons]

/-! ### zipIdx -/

@[simp, grind =] theorem getElem_zipIdx {xs : NonEmptyArray α} {k : Nat} {i : Nat} (h : i < (xs.zipIdx k).size) :
    (xs.zipIdx k)[i] = (xs[i]'(by simp_all only [size, size_zipIdx]), k + i) := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [getElem, zipIdx, size]
    unfold NonEmptyArray.get
    simp
    omega

@[simp, grind =] theorem zipIdx_toArr {xs : NonEmptyArray α} {k : Nat} :
    (xs.zipIdx k).toArr = xs.toArr.zipIdx k := by
  simp only [toArr, zipIdx, Array.zipIdx_append, Array.zipIdx_toArray, List.zipIdx_cons,
    List.zipIdx_nil, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]

@[simp, grind =] theorem toList_zipIdx {xs : NonEmptyArray α} {k : Nat} :
    (xs.zipIdx k).toList = xs.toList.zipIdx k := by
  simp only [toList, zipIdx, _root_.Array.toList_zipIdx, List.zipIdx_cons]

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {k i : Nat} {x : α} {xs : NonEmptyArray α} :
    (x, i) ∈ xs.zipIdx k ↔ k ≤ i ∧ xs[i - k]? = some x := by
  simp only [mem_def, toArr, zipIdx_toArr, _root_.Array.mk_mem_zipIdx_iff_le_and_getElem?_sub,
    getElem?, Option.dite_none_right_eq_some, Option.some.injEq, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size, and_congr_right_iff]
  intro a
  simp_all only [size, toArr_getElem]
  rfl

theorem mk_mem_zipIdx_iff_getElem? {x : α} {i : Nat} {xs : NonEmptyArray α} :
    (x, i) ∈ xs.zipIdx ↔ xs[i]? = some x := by
  rw [mk_mem_zipIdx_iff_le_and_getElem?_sub]
  simp

theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {xs : NonEmptyArray α} {k : Nat} :
    x ∈ xs.zipIdx k ↔ k ≤ x.2 ∧ xs[x.2 - k]? = some x.1 := by
  cases x
  simp only [mk_mem_zipIdx_iff_le_and_getElem?_sub, size]

theorem mem_zipIdx_iff_getElem? {x : α × Nat} {xs : NonEmptyArray α} :
    x ∈ xs.zipIdx ↔ xs[x.2]? = some x.1 := by
  rw [mk_mem_zipIdx_iff_getElem?]

/-! ### mapFinIdx -/

@[congr] theorem mapFinIdx_congr {xs ys : NonEmptyArray α} (w : xs = ys)
    (f : (i : Nat) → α → (h : i < xs.size) → β) :
    xs.mapFinIdx f = ys.mapFinIdx (fun i a h => f i a (by simp only [size, w]; omega)) := by
  subst w
  rfl

theorem mapFinIdx_eq_ofFn {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = NonEmptyArray.ofFn (n := xs.tail.size) fun i =>
      f i.val (xs[i.val]'(by simp only [size]; omega)) (by simp only [size]; omega) := by
  apply toArr_inj.1
  simp only [toArr, toArr_mapFinIdx, _root_.Array.mapFinIdx_eq_ofFn, Fin.getElem_fin, size,
    toArr_ofFn]
  apply Array.ext
  · simp at *; omega
  · intro i h1 h2
    simp only [Array.getElem_ofFn]
    rw [toArr_getElem xs i (by simp only [Array.size_ofFn, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add, size] at *; omega)]

@[grind =]
theorem mapFinIdx_append {xs ys : NonEmptyArray α} {f : (i : Nat) → α → (h : i < (xs ++ ys).size) → β} :
    (xs ++ ys).mapFinIdx f =
      xs.mapFinIdx (fun i a h => f i a (by simp; grind only)) ++
        ys.mapFinIdx (fun i a h => f (i + xs.size) a (by simp; grind only)) := by
  apply toArr_inj.1
  simp only [toArr, toArr_mapFinIdx, toArr_append, Array.append_singleton_assoc, Array.push_append,
    Array.append_assoc, _root_.Array.mapFinIdx_append, List.mapFinIdx_toArray, List.mapFinIdx_cons,
    List.length_nil, List.mapFinIdx_nil,
    List.size_toArray, List.length_cons, Nat.zero_add, Array.mapFinIdx_push, Array.size_push, size]
  simp_all only [Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd]

@[simp, grind =]
theorem mapFinIdx_push {xs : NonEmptyArray α} {a : α} {f : (i : Nat) → α → (h : i < (xs.push a).size) → β} :
    mapFinIdx (xs.push a) f =
      (mapFinIdx xs (fun i a h => f i a (by simp only [size, push, Array.size_push] at *; omega))).push (f xs.size a (by simp only [size,
        push, Array.size_push, Nat.add_lt_add_iff_left, Nat.lt_add_one] at *)) := by
  apply toArr_inj.1
  apply Array.ext
  · simp only [toArr, push, _root_.Array.size_mapFinIdx, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Array.size_push, size,
    mapFinIdx_tail] at *
  · intro i h1 h2
    simp only [toArr, mapFinIdx, push, _root_.Array.mapFinIdx_push, Array.getElem_append,
      List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff,
      List.getElem_toArray, List.getElem_singleton, Array.getElem_push, _root_.Array.size_mapFinIdx,
      _root_.Array.getElem_mapFinIdx, dite_eq_ite, size] at *
    repeat split
    all_goals (congr <;> (simp only [toArr, push, toArr_mapFinIdx, _root_.Array.size_mapFinIdx,
      Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Array.size_push, size] at *; grind only))

theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (h : i < 1) → β} :
    (NonEmptyArray.singleton a).mapFinIdx f = NonEmptyArray.singleton (f 0 a (by simp)) := by
  simp only [mapFinIdx, NonEmptyArray.singleton, List.mapFinIdx_toArray,
    List.mapFinIdx_nil]

theorem mapFinIdx_eq_zipIdx_map {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = xs.zipIdx.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f i x (by simp only [mk_mem_zipIdx_iff_getElem?, size, getElem?_eq_some_iff] at m; exact m.1) := by
  ext
  · simp_all only [attach]
    rfl
  · simp only [mapFinIdx, _root_.Array.size_mapFinIdx, zipIdx, Nat.reduceAdd, attach, Nat.zero_add,
    Array.map_map, Array.size_map, Array.size_attach, _root_.Array.size_zipIdx]
  · simp only [mapFinIdx, _root_.Array.getElem_mapFinIdx, zipIdx, Nat.reduceAdd, attach,
    Nat.zero_add, Array.map_map, Array.getElem_map, Array.getElem_attach,
    _root_.Array.getElem_zipIdx, Nat.add_comm, Function.comp_apply]

theorem exists_of_mem_mapFinIdx {b : β} {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β}
    (h : b ∈ xs.mapFinIdx f) : ∃ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  have h' := h
  rw [mem_def, toArr_mapFinIdx] at h'
  obtain ⟨i, hi, h_eq⟩ := _root_.Array.exists_of_mem_mapFinIdx h'
  refine ⟨i, by simpa using hi, ?_⟩
  rw [← h_eq]
  congr 1
  · subst h_eq
    simp_all only [toArr, Array.mem_mapFinIdx, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, size, toArr_getElem]
    obtain ⟨w, h_1⟩ := h'
    obtain ⟨w_1, h_1⟩ := h_1
    aesop?

@[simp, grind =] theorem mem_mapFinIdx {b : β} {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    b ∈ xs.mapFinIdx f ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  constructor
  · intro h; exact exists_of_mem_mapFinIdx h
  · intro a
    simp_all only [size]
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    subst h
    aesop?

theorem mapFinIdx_eq_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys : NonEmptyArray β} :
    xs.mapFinIdx f = ys ↔ ys.size = xs.size ∧ ∀ (i : Nat) (hi : i < xs.size), ys[i]'(by
    simp_all only [size]
    aesop?) = f i xs[i] hi := by
  rw [← toArr_inj, toArr_mapFinIdx, _root_.Array.mapFinIdx_eq_iff]
  simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_left_cancel_iff, size]
  constructor
  · rintro ⟨hsz, h⟩
    refine ⟨hsz, ?_⟩
    intro i hi
    specialize h i hi
    simp_all only [size, toArr_getElem]
  · rintro ⟨hsz, h⟩
    refine ⟨hsz, ?_⟩
    intro i hi
    specialize h i hi
    simp_all only [size, toArr_getElem]

@[simp] theorem mapFinIdx_eq_singleton_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
    xs.mapFinIdx f = NonEmptyArray.singleton b ↔ ∃ (a : α) (w : xs = NonEmptyArray.singleton a), f 0 a (by aesop) = b := by
  rw [← toArr_inj, toArr_mapFinIdx, NonEmptyArray.toArr_singleton, _root_.Array.mapFinIdx_eq_singleton_iff]
  simp only [toArr, Array.append_eq_toArray_iff, List.cons_append, List.nil_append, List.cons.injEq,
    Array.toList_eq_nil_iff]
  aesop

theorem mapFinIdx_eq_append_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys zs : NonEmptyArray β} :
    xs.mapFinIdx f = ys ++ zs ↔
      ∃ (ys' : NonEmptyArray α) (zs' : NonEmptyArray α) (w : xs = ys' ++ zs'),
        ys'.mapFinIdx (fun i a h => f i a (by
          simp only [size, w, size_append]
          subst w
          simp_all only [size]
          aesop?)) = ys ∧
        zs'.mapFinIdx (fun i a h => f (i + ys'.size) a (by
          simp only [size, w, size_append]
          subst w
          simp_all only [size]
          aesop?)) = zs := by
  rw [← toArr_inj, toArr_mapFinIdx, toArr_append, _root_.Array.mapFinIdx_eq_append_iff]
  constructor
  · rintro ⟨ys', zs', w, h1, h2⟩
    have hys : ys'.size > 0 := by
      have := congrArg Array.size w;
      simp at this;
      simp_all only [toArr, gt_iff_lt]
      aesop?
    have hzs : zs'.size > 0 := by
      have := congrArg Array.size w;
      simp at this;
      simp_all only [toArr, gt_iff_lt]
      aesop?
    refine ⟨⟨ys'[0], ys'[1:]⟩, ⟨zs'[0], zs'[1:]⟩, ?_, ?_, ?_⟩
    · simp_all only [toArr, Subarray.copy_eq_toArray]
      aesop?
    · simp_all only [toArr, Subarray.copy_eq_toArray, size]
      aesop?
    · simp_all only [toArr, Subarray.copy_eq_toArray, size, Std.Slice.size_toArray_eq_size]
      aesop?
  · intro a
    simp_all only [size, toArr]
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst w_2 left right
    simp_all only [toArr_mapFinIdx, toArr, toArr_append, Array.append_singleton_assoc, Array.push_append,
      Array.append_assoc]
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · apply And.intro
          · rfl
          · simp_all only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
            rfl
        · simp_all only [Array.append_singleton_assoc, Array.push_append, Array.append_assoc]

theorem mapFinIdx_eq_push_iff {xs : NonEmptyArray α} {b : β} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = ys.push b ↔
      ∃ (zs : NonEmptyArray α) (a : α) (w : xs = zs.push a),
        zs.mapFinIdx (fun i a h => f i a (by
          simp only [size, w];
          subst w
          simp_all only [size]
          aesop?)
          ) = ys ∧ b = f (xs.size - 1) a (by simp only [size, w, Nat.add_sub_cancel_left,
            Nat.lt_add_left_iff_pos, Nat.lt_add_one]) := by
  rw [← toArr_inj, toArr_mapFinIdx, toArr_push, _root_.Array.mapFinIdx_eq_push_iff]
  constructor
  · rintro ⟨zs, a, w, h1, h2⟩
    have hzs : zs.size > 0 := by
      have := congrArg Array.size w; simp at this;
      subst h2
      simp_all only [toArr, gt_iff_lt]
      aesop?
    refine ⟨⟨zs[0], zs[1:]⟩, a, ?_, ?_, ?_⟩
    · subst h2
      simp_all only [toArr, Subarray.copy_eq_toArray]
      aesop?
    · subst h2
      simp_all only [toArr, Subarray.copy_eq_toArray, size]
      aesop?
    · simp only [h2, toArr, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_sub_cancel_left, size]
  · rintro ⟨zs, a, rfl, rfl, rfl⟩
    simp_all only [toArr, size, toArr_mapFinIdx, Nat.add_sub_cancel_left, Array.size_push, Nat.add_one_sub_one,
      toArr_push, Array.push_append]
    aesop?

-- theorem mapFinIdx_eq_mapFinIdx_iff {xs : NonEmptyArray α} {f g : (i : Nat) → α → (h : i < xs.size) → β} :
--     xs.mapFinIdx f = xs.mapFinIdx g ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i] h := by
--   simp_all only [size]
--   apply Iff.intro
--   · intro a i h
--     aesop?
--   · intro a
--     aesop?

-- @[simp, grind =] theorem mapFinIdx_mapFinIdx {xs : NonEmptyArray α}
--     {f : (i : Nat) → α → (h : i < xs.size) → β}
--     {g : (i : Nat) → β → (h : i < (xs.mapFinIdx f).size) → γ} :
--     (xs.mapFinIdx f).mapFinIdx g = xs.mapFinIdx (fun i a h => g i (f i a h) (by simpa using h)) := by
--   simp_all only [size]
--   aesop?

-- theorem mapFinIdx_eq_replicate_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
--     xs.mapFinIdx f = NonEmptyArray.ofFn (fun _ => b) ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
--   aesop?

-- @[simp, grind =] theorem mapFinIdx_reverse {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.reverse.size) → β} :
--     xs.reverse.mapFinIdx f = (xs.mapFinIdx (fun i a h => f (xs.size - 1 - i) a (by simp; omega))).reverse := by
--   simp_all only [size, Nat.add_sub_cancel_left]
--   aesop?

/-! ### mapIdx -/

-- @[simp] theorem mapFinIdx_eq_mapIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {g : Nat → α → β}
--     (h : ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i]) :
--     xs.mapFinIdx f = xs.mapIdx g := by
--   ext
--   simp_all only [size]
--   apply h
--   simp_all only [size]
--   aesop?

-- theorem mapIdx_eq_mapFinIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
--     xs.mapIdx f = xs.mapFinIdx (fun i a _ => f i a) := by
--   simp? [mapFinIdx_eq_mapIdx]

-- theorem mapIdx_eq_zipIdx_map {xs : NonEmptyArray α} {f : Nat → α → β} :
--     xs.mapIdx f = xs.zipIdx.map fun ⟨a, i⟩ => f i a := by
--   ext <;> simp_all only
--   · rfl
--   · simp_all only [Array.size_map]
--     aesop?
--   · simp_all only [Array.getElem_map]
--     aesop?

-- @[grind =]
-- theorem mapIdx_append {xs ys : NonEmptyArray α} :
--     (xs ++ ys).mapIdx f = xs.mapIdx f ++ ys.mapIdx (fun i => f (i + xs.size)) := by
--   ext <;> simp only [mapIdx, size, Nat.zero_add]

-- @[simp, grind =]
-- theorem mapIdx_push {xs : NonEmptyArray α} {a : α} :
--     mapIdx f (xs.push a) = (mapIdx f xs).push (f xs.size a) := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_push]

-- theorem mapIdx_singleton {a : α} : mapIdx f (NonEmptyArray.singleton a) = NonEmptyArray.singleton (f 0 a) := by
--   simp? [NonEmptyArray.singleton, mapIdx, mapIdxM, mapFinIdxM]

-- @[simp]
-- theorem mapIdx_eq_singleton_iff {xs : NonEmptyArray α} {f : Nat → α → β} {b : β} :
--     mapIdx f xs = NonEmptyArray.singleton b ↔ ∃ (a : α), xs = NonEmptyArray.singleton a ∧ f 0 a = b := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_eq_singleton_iff]

-- theorem exists_of_mem_mapIdx {b : β} {xs : NonEmptyArray α}
--     (h : b ∈ mapIdx f xs) : ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
--   simp? [mem_def, toArr, mapIdx] at h
--   exact Array.exists_of_mem_mapIdx h

-- @[simp, grind =] theorem mem_mapIdx {b : β} {xs : NonEmptyArray α} :
--     b ∈ mapIdx f xs ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
--   simp? [mem_def, toArr, mapIdx, Array.mem_mapIdx]

-- theorem mapIdx_eq_push_iff {xs : NonEmptyArray α} {b : β} :
--     mapIdx f xs = ys.push b ↔
--       ∃ (a : α) (zs : NonEmptyArray α), xs = zs.push a ∧ mapIdx f zs = ys ∧ f zs.size a = b := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_eq_push_iff]

-- theorem mapIdx_eq_append_iff {xs : NonEmptyArray α} {f : Nat → α → β} {ys zs : NonEmptyArray β} :
--     mapIdx f xs = ys ++ zs ↔
--       ∃ (xs' : NonEmptyArray α) (zs' : NonEmptyArray α), xs = xs' ++ zs' ∧
--         xs'.mapIdx f = ys ∧
--         zs'.mapIdx (fun i => f (i + xs'.size)) = zs := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_eq_append_iff]

-- theorem mapIdx_eq_iff {xs : NonEmptyArray α} : mapIdx f xs = ys ↔ ∀ i : Nat, ys[i]? = xs[i]?.map (f i) := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_eq_iff]

-- theorem mapIdx_eq_mapIdx_iff {xs : NonEmptyArray α} :
--     mapIdx f xs = mapIdx g xs ↔ ∀ i : Nat, (h : i < xs.size) → f i xs[i] = g i xs[i] := by
--   ext <;> simp

-- @[simp, grind =] theorem mapIdx_set {f : Nat → α → β} {xs : NonEmptyArray α} {i : Nat} {h : i < xs.size} {a : α} :
--     (xs.set i a h).mapIdx f = (xs.mapIdx f).set i (f i a) (by simpa) := by
--   ext <;> aesop?

-- @[simp, grind =] theorem back?_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
--     (mapIdx f xs).back? = (xs.back?).map (f (xs.size - 1)) := by
--   ext <;> simp? [mapIdx, back?, toArr, Array.back?_mapIdx]

-- @[simp, grind =] theorem back_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
--     (xs.mapIdx f).back = f (xs.size - 1) xs.back := by
--   ext <;> simp? [mapIdx, back, toArr, Array.back_mapIdx]

-- @[simp, grind =] theorem mapIdx_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} {g : Nat → β → γ} :
--     (xs.mapIdx f).mapIdx g = xs.mapIdx (fun i => g i ∘ f i) := by
--   ext <;> try rfl
--   · aesop?

-- theorem mapIdx_eq_replicate_iff {xs : NonEmptyArray α} {f : Nat → α → β} {b : β} :
--     mapIdx f xs = NonEmptyArray.ofFn (fun _ => b) ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
--   ext <;> simp? [mapIdx, toArr, Array.mapIdx_eq_replicate_iff, Array.size]

-- @[simp, grind =] theorem mapIdx_reverse {xs : NonEmptyArray α} {f : Nat → α → β} :
--     xs.reverse.mapIdx f = (mapIdx (fun i => f (xs.size - 1 - i)) xs).reverse := by
--   ext <;> simp? [mapIdx, reverse, toArr, Array.mapIdx_reverse, fromArray]

-- theorem toList_mapFinIdxM [Monad m] [LawfulMonad m] {xs : NonEmptyArray α}
--     {f : (i : Nat) → α → (h : i < xs.size) → m β} :
--     toList <$> xs.mapFinIdxM f = xs.toList.mapFinIdxM f := by
--   simp? [mapFinIdxM, toList, Functor.map, pure, bind]
--   congr
--   funext a
--   rw [Array.toList_mapFinIdxM]

-- theorem toList_mapIdxM [Monad m] [LawfulMonad m] {xs : NonEmptyArray α}
--     {f : Nat → α → m β} :
--     toList <$> xs.mapIdxM f = xs.toList.mapIdxM f := by
--   rw [mapIdxM, toList_mapFinIdxM]
--   simp? [List.mapIdxM]

end NonEmpty.CorrectByConstruction.Array
