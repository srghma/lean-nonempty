
module

import all NonEmpty.CorrectByConstruction.Array.Basic

namespace NonEmpty.CorrectByConstruction.Array

open NonEmptyArray

theorem toArr_inj {xs ys : NonEmptyArray α} : xs.toArr = ys.toArr ↔ xs = ys := by
  cases xs; cases ys
  simp only [toArr, mk.injEq]
  constructor
  · intro h
    have ⟨h1, h2⟩ := _root_.Array.append_inj' h (by
      have hsz := congrArg _root_.Array.size h
      simp only [_root_.Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.add_left_cancel_iff] at hsz
      omega)
    exact ⟨_root_.Array.singleton_inj.mp h1, h2⟩
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
    (xs.mapFinIdx f).toArr = xs.toArr.mapFinIdx (fun i a h => f i a (by simpa only [size, toArr,
      Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add] using h)) := by
  simp only [toArr, mapFinIdx_head, mapFinIdx_tail, _root_.Array.mapFinIdx_append, _root_.Array.mapFinIdx_singleton, _root_.Array.size_singleton]

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
    (f := fun i a h => f i a (by simpa only [size, toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add] using h))
    (p := fun i b h => p i b (by simpa only [size, toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add] using h))
    (by
      intro i h hm
      simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
        Nat.zero_add] at h
      have ⟨h_p, h_mot'⟩ := hs i (by omega) hm
      refine ⟨?_, h_mot'⟩
      simp_all only [size, toArr, toArr_getElem])
  have hsz : (xs.mapFinIdx f).size = xs.size := size_mapFinIdx
  refine ⟨by simpa only [size, toArr, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add] using h_mot, hsz, ?_⟩
  intro i h
  have hg := h_get i (by simpa only [toArr, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, size] using h)
  rw [← toArr_getElem (as := xs.mapFinIdx f) i (by rw [hsz]; simpa only [size] using h)]
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

@[simp] theorem toArr_mapIdx {f : Nat → α → β} {xs : NonEmptyArray α} :
    (xs.mapIdx f).toArr = xs.toArr.mapIdx f := by
  obtain ⟨h, t⟩ := xs
  apply _root_.Array.ext
  · simp only [toArr, mapIdx, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, _root_.Array.size_mapIdx]
  · intro i h1 h2
    simp only [toArr, mapIdx, Array.getElem_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.lt_one_iff, List.getElem_toArray, List.getElem_singleton,
      _root_.Array.getElem_mapIdx]
    split
    · next =>
      rename_i h_1
      subst h_1
      simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,  Nat.zero_add,
        size_mapIdx, size, _root_.Array.size_mapIdx]
    · next h0 => grind only [#0168]

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
  simp only [toArr, zipIdx, _root_.Array.zipIdx_append, _root_.Array.zipIdx_toArray, List.zipIdx_cons,
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
  apply _root_.Array.ext
  · simp only [Array.size_ofFn, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add] at *; omega
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
  apply _root_.Array.ext
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
    (NonEmptyArray.singleton a).mapFinIdx f = NonEmptyArray.singleton (f 0 a (by simp only [Nat.lt_add_one])) := by
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
  rw [mem_def, toArr_mapFinIdx] at h
  obtain ⟨i, hi, h_eq⟩ := _root_.Array.exists_of_mem_mapFinIdx h
  refine ⟨i, by simpa only [size, toArr, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add] using hi, ?_⟩
  rw [toArr_getElem] at h_eq
  exact h_eq

@[simp, grind =] theorem mem_mapFinIdx {b : β} {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    b ∈ xs.mapFinIdx f ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  constructor
  · apply exists_of_mem_mapFinIdx
  · rintro ⟨i, hi, rfl⟩
    rw [mem_def, toArr_mapFinIdx]
    apply _root_.Array.mem_mapFinIdx.2
    refine ⟨i, by simpa only [toArr, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, size] using hi, ?_⟩
    rw [toArr_getElem]

theorem mapFinIdx_eq_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys : NonEmptyArray β} :
    xs.mapFinIdx f = ys ↔ ∃ (hsz : ys.size = xs.size), ∀ (i : Nat) (hi : i < xs.size), ys[i]'(by simp_all only [size,
      Nat.add_left_cancel_iff]) = f i xs[i] hi := by
  rw [← toArr_inj, toArr_mapFinIdx, _root_.Array.mapFinIdx_eq_iff]
  simp only [size_toArr, size]
  constructor
  · rintro ⟨hsz, h⟩
    refine ⟨by simpa only [Nat.add_left_cancel_iff] using hsz, ?_⟩
    intro i hi
    specialize h i (by simpa only using hi)
    rw [toArr_getElem, toArr_getElem] at h
    exact h
  · rintro ⟨hsz, h⟩
    refine ⟨by simpa only [Nat.add_left_cancel_iff] using hsz, ?_⟩
    intro i hi
    specialize h i hi
    rw [toArr_getElem, toArr_getElem]
    exact h

@[simp] theorem mapFinIdx_eq_singleton_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
    xs.mapFinIdx f = NonEmptyArray.singleton b ↔ ∃ (a : α) (w : xs = NonEmptyArray.singleton a), f 0 a (by subst w; simp only [size,
      NonEmptyArray.singleton, List.size_toArray, List.length_nil, Nat.add_zero, Nat.lt_add_one]) = b := by
  rw [← toArr_inj, toArr_mapFinIdx, NonEmptyArray.toArr_singleton, _root_.Array.mapFinIdx_eq_singleton_iff]
  simp only [toArr, Array.append_eq_toArray_iff, List.cons_append, List.nil_append, List.cons.injEq,
    Array.toList_eq_nil_iff]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := w_1
    subst left h
    simp_all only
    apply Exists.intro
    · apply Exists.intro
      · rfl
      · ext : 1
        · rfl
        · ext i hi₁ hi₂ : 1
          · simp_all only [List.size_toArray, List.length_nil]
            rfl
          · simp_all only [List.getElem_toArray]
            rfl
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    subst w_1 h
    apply Exists.intro
    · apply Exists.intro
      · rfl
      · apply And.intro
        · rfl
        · rfl

theorem mapFinIdx_eq_append_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys zs : NonEmptyArray β} :
    xs.mapFinIdx f = ys ++ zs ↔
      ∃ (ys' : NonEmptyArray α) (zs' : NonEmptyArray α) (w : xs = ys' ++ zs'),
        ys'.mapFinIdx (fun i a h => f i a (by
          simp only [size, w, size_append]
          subst w
          simp_all only [size]
          grind only)) = ys ∧
        zs'.mapFinIdx (fun i a h => f (i + ys'.size) a (by
          simp only [size, w, size_append]
          subst w
          simp_all only [size]
          grind only)) = zs := by
  rw [← toArr_inj, toArr_mapFinIdx, toArr_append, _root_.Array.mapFinIdx_eq_append_iff]
  constructor
  · rintro ⟨ys', zs', w, h1, h2⟩
    have hys : ys'.size > 0 := by
      have h := congrArg Array.size h1
      simp only [_root_.Array.size_mapFinIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at h; omega
    have hzs : zs'.size > 0 := by
      have h := congrArg Array.size h2
      simp only [_root_.Array.size_mapFinIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at h; omega
    refine ⟨fromArray ys' hys, fromArray zs' hzs, ?_, ?_, ?_⟩
    · rw [← toArr_inj, toArr_append, toArr_fromArray, toArr_fromArray, w]
    · rw [← toArr_inj, toArr_mapFinIdx]
      congr; simp_all only [toArr, toArr_fromArray]
    · rw [← toArr_inj, toArr_mapFinIdx]
      congr; simp_all only [toArr, toArr_fromArray, size, size_fromArray]
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

theorem mapFinIdx_eq_push_iff {xs : NonEmptyArray α} {b : β} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys : NonEmptyArray β} :
    xs.mapFinIdx f = ys.push b ↔
      ∃ (zs : NonEmptyArray α) (a : α) (w : xs = zs.push a),
        zs.mapFinIdx (fun i a h => f i a (by
        simp only [size, w, push, Array.size_push];
        subst w
        simp_all only [size]
        grind only)
        ) = ys ∧
        b = f zs.size a (by simp only [size, w, push, Array.size_push, Nat.add_lt_add_iff_left,
          Nat.lt_add_one]) := by
  rw [← toArr_inj, toArr_mapFinIdx, toArr_push, _root_.Array.mapFinIdx_eq_push_iff]
  constructor
  · rintro ⟨zs', a, w, h1, h2⟩
    have hzs : zs'.size > 0 := by
      have h := congrArg Array.size h1
      simp only [_root_.Array.size_mapFinIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at h; omega
    refine ⟨fromArray zs' hzs, a, ?_, ?_, ?_⟩
    · rw [← toArr_inj, toArr_push, toArr_fromArray, w]
    · rw [← toArr_inj, toArr_mapFinIdx]
      congr;
      subst h2
      simp_all only [toArr, toArr_fromArray]
    · rw [h2];
      subst h2
      simp_all only [toArr, Array.size_push, Nat.add_one_sub_one, size, size_fromArray]
  · intro a
    simp_all only [size, toArr, Array.size_push, Nat.add_one_sub_one]
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst w_2 left right
    simp_all only [toArr_mapFinIdx, toArr, toArr_push, Array.push_append]
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · apply And.intro
          · rfl
          · simp_all only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
            rfl
        · simp_all only [Array.push_append]

theorem mapFinIdx_eq_mapFinIdx_iff {xs : NonEmptyArray α} {f g : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = xs.mapFinIdx g ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i] h := by
  rw [← toArr_inj, toArr_mapFinIdx, toArr_mapFinIdx, _root_.Array.mapFinIdx_eq_mapFinIdx_iff]
  constructor
  · intro h i hi
    specialize h i (by simpa only [toArr, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add, size] using hi)
    simp_all only [toArr, size, toArr_getElem]
  · intro h i hi
    specialize h i (by simpa only [size, toArr, Array.size_append, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add] using hi)
    rw [toArr_getElem]
    exact h

@[simp, grind =] theorem mapFinIdx_mapFinIdx {xs : NonEmptyArray α}
    {f : (i : Nat) → α → (h : i < xs.size) → β}
    {g : (i : Nat) → β → (h : i < (xs.mapFinIdx f).size) → γ} :
    (xs.mapFinIdx f).mapFinIdx g = xs.mapFinIdx (fun i a h => g i (f i a h) (by simpa only [size,
      size_mapFinIdx] using h)) := by
  rw [← toArr_inj, toArr_mapFinIdx]
  congr;
  simp_all only [toArr, toArr_mapFinIdx, _root_.Array.mapFinIdx_mapFinIdx, size]

theorem mapFinIdx_eq_replicate_iff {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
    xs.mapFinIdx f = NonEmptyArray.ofFn (n := xs.tail.size) (fun _ => b) ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  constructor
  · intro h i hi
    have h_size : xs.size = 1 + xs.tail.size := rfl
    have h_eq : (xs.mapFinIdx f)[i]'(by simpa) = (NonEmptyArray.ofFn (n := xs.tail.size) (fun _ => b))[i]'(by rw [size_ofFn]; omega) := by
      simp only [size, h, getElem_ofFn]
    simpa only [size, getElem_mapFinIdx, getElem_ofFn] using h_eq
  · intro h
    rw [← toArr_inj, toArr_mapFinIdx, toArr_ofFn]
    apply _root_.Array.ext
    · simp
      omega
    · intro i hi₁ hi₂
      simp only [_root_.Array.getElem_mapFinIdx, Array.getElem_ofFn]
      rw [toArr_getElem]
      exact h i (by simpa only [size, toArr, _root_.Array.size_mapFinIdx, Array.size_append,
        List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add] using hi₁)

@[simp, grind =] theorem mapFinIdx_reverse {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.reverse.size) → β} :
    xs.reverse.mapFinIdx f = (xs.mapFinIdx (fun i a h => f (xs.size - 1 - i) a (by
      have hsz := size_reverse xs
      omega))).reverse := by
  apply toArr_inj.1
  simp only [toArr_mapFinIdx, toArr_reverse, _root_.Array.mapFinIdx_reverse]
  congr; funext i a h
  simp only [size, size_toArr]

/-! ### mapIdx -/

@[simp] theorem mapFinIdx_eq_mapIdx {xs : NonEmptyArray α} {f : (i : Nat) → α → (h : i < xs.size) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i]) :
    xs.mapFinIdx f = xs.mapIdx g := by
  apply toArr_inj.1
  simp only [toArr_mapFinIdx, toArr_mapIdx]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp_all only [size, toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, toArr_getElem, _root_.Array.mapFinIdx_eq_mapIdx, _root_.Array.getElem_mapIdx]

theorem mapIdx_eq_mapFinIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
    xs.mapIdx f = xs.mapFinIdx (fun i a _ => f i a) := by
  simp only [size, mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_zipIdx_map {xs : NonEmptyArray α} {f : Nat → α → β} :
    xs.mapIdx f = xs.zipIdx.map (fun ⟨a, i⟩ => f i a) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, toArr_map, _root_.Array.mapIdx_eq_zipIdx_map]
  simp_all only [toArr, zipIdx_toArr]

theorem mapIdx_append_ne {xs ys : NonEmptyArray α} {f : Nat → α → β} :
    (xs ++ ys).mapIdx f = xs.mapIdx f ++ ys.mapIdx (fun i => f (i + xs.size)) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, toArr_append, Array.mapIdx_append, size, size_toArr]

@[simp]
theorem mapIdx_push_ne {xs : NonEmptyArray α} {a : α} {f : Nat → α → β} :
    (xs.push a).mapIdx f = (xs.mapIdx f).push (f xs.size a) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, toArr_push, Array.mapIdx_push, size, size_toArr]

theorem mapIdx_singleton {a : α} {f : Nat → α → β} : (NonEmptyArray.singleton a).mapIdx f = NonEmptyArray.singleton (f 0 a) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, toArr_singleton, _root_.Array.mapIdx_singleton]

@[simp]
theorem mapIdx_eq_singleton_iff {xs : NonEmptyArray α} {f : Nat → α → β} {b : β} :
    xs.mapIdx f = NonEmptyArray.singleton b ↔ ∃ (a : α), xs = NonEmptyArray.singleton a ∧ f 0 a = b := by
  rw [← toArr_inj, toArr_mapIdx, toArr_singleton, _root_.Array.mapIdx_eq_singleton_iff]
  constructor
  · rintro ⟨a, h1, h2⟩
    have h_a : xs = NonEmptyArray.singleton a := by
      rw [← toArr_inj, toArr_singleton]
      exact h1
    exact ⟨a, h_a, h2⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, rfl, rfl⟩

theorem exists_of_mem_mapIdx {b : β} {xs : NonEmptyArray α} {f : Nat → α → β}
    (h : b ∈ xs.mapIdx f) : ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  rw [mem_def, toArr_mapIdx] at h
  obtain ⟨i, h1, h2⟩ := _root_.Array.exists_of_mem_mapIdx h
  refine ⟨i, by simpa only [size, toArr, Array.size_append, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add] using h1, ?_⟩
  rw [← toArr_getElem, h2]

@[simp] theorem mem_mapIdx {b : β} {xs : NonEmptyArray α} {f : Nat → α → β} :
    b ∈ xs.mapIdx f ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  rw [mem_def, toArr_mapIdx, _root_.Array.mem_mapIdx]
  simp only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, size]
  simp_all only [size, toArr_getElem]

theorem mapIdx_eq_push_iff {xs : NonEmptyArray α} {f : Nat → α → β} {ys : NonEmptyArray β} {b : β} :
    xs.mapIdx f = ys.push b ↔
      ∃ (a : α) (zs : NonEmptyArray α), xs = zs.push a ∧ zs.mapIdx f = ys ∧ f zs.size a = b := by
  rw [← toArr_inj, toArr_mapIdx, toArr_push, _root_.Array.mapIdx_eq_push_iff]
  constructor
  · rintro ⟨a, zs_arr, hxs, hmap, hb⟩
    have hzs_size : zs_arr.size > 0 := by
      have := congrArg Array.size hmap
      simp only [_root_.Array.size_mapIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at this
      omega
    let zs := fromArray zs_arr hzs_size
    refine ⟨a, zs, ?_, ?_, ?_⟩
    · rw [← toArr_inj, toArr_push, toArr_fromArray, hxs]
    · rw [← toArr_inj, toArr_mapIdx, toArr_fromArray, hmap]
    · subst hb
      simp_all only [toArr, size, size_fromArray, zs]
  · rintro ⟨a, zs, rfl, rfl, rfl⟩
    refine ⟨a, zs.toArr, ?_, ?_, ?_⟩
    · exact toArr_push zs a
    · exact toArr_mapIdx.symm
    · rw [size_toArr]

theorem mapIdx_eq_append_iff {xs : NonEmptyArray α} {f : Nat → α → β} {ys zs : NonEmptyArray β} :
    xs.mapIdx f = ys ++ zs ↔
      ∃ (xs' zs' : NonEmptyArray α), xs = xs' ++ zs' ∧
        xs'.mapIdx f = ys ∧
        zs'.mapIdx (fun i => f (i + xs'.size)) = zs := by
  rw [← toArr_inj, toArr_mapIdx, toArr_append, _root_.Array.mapIdx_eq_append_iff]
  constructor
  · rintro ⟨xs'_arr, zs'_arr, hxs, hmap1, hmap2⟩
    have hxs'_size : xs'_arr.size > 0 := by
      have := congrArg Array.size hmap1
      simp only [_root_.Array.size_mapIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at this
      omega
    have hzs'_size : zs'_arr.size > 0 := by
      have := congrArg Array.size hmap2
      simp only [_root_.Array.size_mapIdx, toArr, Array.size_append, List.size_toArray,
        List.length_cons, List.length_nil, Nat.zero_add] at this
      omega
    let xs' := fromArray xs'_arr hxs'_size
    let zs' := fromArray zs'_arr hzs'_size
    refine ⟨xs', zs', ?_, ?_, ?_⟩
    · rw [← toArr_inj, toArr_append, toArr_fromArray, toArr_fromArray, hxs]
    · rw [← toArr_inj, toArr_mapIdx, toArr_fromArray, hmap1]
    · rw [← toArr_inj, toArr_mapIdx, toArr_fromArray, size_fromArray, hmap2]
  · rintro ⟨xs', zs', rfl, rfl, rfl⟩
    refine ⟨xs'.toArr, zs'.toArr, ?_, ?_, ?_⟩
    · exact toArr_append xs' zs'
    · exact toArr_mapIdx.symm
    · rw [size_toArr]
      exact toArr_mapIdx.symm

theorem mapIdx_eq_iff {xs : NonEmptyArray α} {f : Nat → α → β} {ys : NonEmptyArray β} :
    xs.mapIdx f = ys ↔ ∀ i : Nat, ys[i]? = (xs[i]?).map (f i) := by
  rw [← toArr_inj, toArr_mapIdx, _root_.Array.mapIdx_eq_iff]
  simp only [getElem?_eq_toArr_getElem?]

theorem mapIdx_eq_mapIdx_iff {xs : NonEmptyArray α} {f g : Nat → α → β} :
    xs.mapIdx f = xs.mapIdx g ↔ ∀ i : Nat, (h : i < xs.size) → f i xs[i] = g i xs[i] := by
  rw [← toArr_inj, toArr_mapIdx, toArr_mapIdx, _root_.Array.mapIdx_eq_mapIdx_iff]
  simp_all only [toArr, Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, size,
    toArr_getElem]

@[simp, grind =] theorem mapIdx_set {f : Nat → α → β} {xs : NonEmptyArray α} {i : Nat} {h : i < xs.size} {a : α} :
    (xs.set i a h).mapIdx f = (xs.mapIdx f).set i (f i a) (by simpa) := by
  apply toArr_inj.1
  simp only [toArr, _root_.Array.mapIdx_set, toArr_set, toArr_mapIdx]

@[simp, grind =] theorem back_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
    (xs.mapIdx f).back = f (xs.size - 1) xs.back := by
  simp only [← NonEmptyArray.toArr_back, toArr_mapIdx, _root_.Array.back_mapIdx, size_toArr, size]

@[simp, grind =] theorem back?_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} :
    (xs.mapIdx f).back? = (xs.back?).map (f (xs.size - 1)) := by
  simp only [back?, back_mapIdx, size, Nat.add_sub_cancel_left, Option.map_some]

@[simp, grind =] theorem mapIdx_mapIdx {xs : NonEmptyArray α} {f : Nat → α → β} {g : Nat → β → γ} :
    (xs.mapIdx f).mapIdx g = xs.mapIdx (fun i a => g i (f i a)) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, _root_.Array.mapIdx_mapIdx, Function.comp_def]

theorem mapIdx_eq_replicate_iff {xs : NonEmptyArray α} {f : Nat → α → β} {b : β} :
    xs.mapIdx f = NonEmptyArray.ofFn (n := xs.tail.size) (fun _ => b) ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  constructor
  · intro heq i hi
    have h_eq : (xs.mapIdx f)[i]? = (NonEmptyArray.ofFn (n := xs.tail.size) fun _ => b)[i]? :=
      congrArg (fun xs => xs[i]?) heq
    simp only [NonEmptyArray.getElem?_def, size_mapIdx, dif_pos hi,
        getElem_mapIdx, size_ofFn, getElem_ofFn] at h_eq
    simp only [size] at hi
    rw [dif_pos (by omega)] at h_eq
    exact Option.some.inj h_eq
  · intro h
    apply toArr_inj.1
    rw [toArr_mapIdx, toArr_ofFn]
    apply _root_.Array.ext
    · simp only [_root_.Array.size_mapIdx, size_toArr, _root_.Array.size_ofFn, size]; omega
    · intro i hi₁ hi₂
      simp only [_root_.Array.getElem_mapIdx, _root_.Array.getElem_ofFn]
      rw [toArr_getElem]
      apply h
      simp only [_root_.Array.size_mapIdx, size_toArr, size] at hi₁; exact hi₁

@[simp, grind =] theorem mapIdx_reverse {xs : NonEmptyArray α} {f : Nat → α → β} :
    (reverse xs).mapIdx f = reverse (xs.mapIdx (fun i a => f (xs.size - 1 - i) a)) := by
  apply toArr_inj.1
  simp only [toArr_mapIdx, toArr_reverse, _root_.Array.mapIdx_reverse, size_toArr]

private theorem List_mapFinIdxM_go_eq [Monad m] [LawfulMonad m] :
    ∀ bs as (f : (i : Nat) → α → i < as.length → m β) acc h1,
    List.mapFinIdxM.go as f bs acc h1 =
      (do let res ← List.mapFinIdxM.go bs (fun i a h' => f (i + acc.size) a (by omega)) bs #[] (by simp only [List.size_toArray,
        List.length_nil, Nat.add_zero])
          pure (acc.toList ++ res)) := by
  intro bs
  induction bs with
  | nil =>
    intro as f acc h1
    simp only [List.mapFinIdxM.go, bind_pure_comp, map_pure, List.append_nil]
  | cons b bs ih =>
    intro as f acc h1
    unfold List.mapFinIdxM.go
    have s0 : (#[ ] : Array β).size = 0 := rfl
    simp only [s0, Nat.zero_add]
    simp only [bind_pure_comp, map_bind]
    congr 1; funext res
    have h1' : bs.length + (acc.push res).size = as.length := by
      simp only [Array.size_push, List.length_cons] at h1 ⊢
      omega
    have h2' : bs.length + #[res].size = (b :: bs).length := rfl
    have eq1 := ih as f (acc.push res) h1'
    have eq2 := ih (b :: bs) (fun i a h' => f (i + acc.size) a (by omega)) #[res] h2'
    apply Eq.trans eq1
    have eq3 : (HAppend.hAppend acc.toList <$> List.mapFinIdxM.go (b :: bs) (fun i a h' => f (i + acc.size) a (by omega)) bs #[res] h2') =
      (HAppend.hAppend acc.toList <$> do let res_1 ← List.mapFinIdxM.go bs (fun i a h' => f (i + #[res].size + acc.size) a (by omega)) bs #[] (by simp only [List.size_toArray,
        List.length_nil, Nat.add_zero]); pure (#[res].toList ++ res_1)) := by
      congr 1
    apply Eq.symm
    apply Eq.trans eq3
    simp only [bind_pure_comp, Functor.map_map, Array.toList_push, List.append_assoc]
    have s2 : (acc.push res).size = acc.size + 1 := by simp only [Array.size_push]
    have s3 : #[res].size = 1 := rfl
    simp only [s2, s3]
    congr 1
    congr; funext i a h'
    have idx_eq : i + 1 + acc.size = i + (acc.size + 1) := by omega
    simp only [idx_eq]

private theorem List_mapFinIdxM_cons [Monad m] [LawfulMonad m] {h : α} {t : List α}
    {f : (i : Nat) → α → i < (h :: t).length → m β} :
    (h :: t).mapFinIdxM f = (do
      let b ← f 0 h (by simp only [List.length_cons, Nat.zero_lt_succ])
      let bs ← t.mapFinIdxM (fun i a h' => f (i + 1) a (by
        simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega))
      pure (b :: bs)) := by
  unfold List.mapFinIdxM
  unfold List.mapFinIdxM.go
  simp only [bind_pure_comp]
  congr; funext res
  rw [List_mapFinIdxM_go_eq]
  simp_all only [List.push_toArray, List.nil_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, List.cons_append, bind_pure_comp, List.cons.injEq, true_and, implies_true,
    map_inj_right_of_nonempty]
  split
  next x x_1 x_2
    x_3 =>
    simp_all only [List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, Array.size_eq_zero_iff,
      List.size_toArray, Nat.add_zero]
    obtain ⟨left, right⟩ := x_2
    subst left right
    rfl
  next x x_1 a as x_2
    x_3 =>
    simp_all only [List.length_cons, List.size_toArray, List.length_nil, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rfl

private theorem List_mapIdxM_go_eq [Monad m] [LawfulMonad m] :
    ∀ bs (f : Nat → α → m β) acc,
    List.mapIdxM.go f bs acc =
      (do let res ← List.mapIdxM.go (fun i a => f (i + acc.size) a) bs #[]
          pure (acc.toList ++ res)) := by
  intro bs
  induction bs with
  | nil =>
    intro f acc
    simp only [List.mapIdxM.go, bind_pure_comp, map_pure, List.append_nil]
  | cons b bs ih =>
    intro f acc
    unfold List.mapIdxM.go
    have s0 : (#[ ] : Array β).size = 0 := rfl
    simp only [s0, Nat.zero_add]
    simp only [map_bind, bind_pure_comp]
    congr 1; funext res
    have : #[].push res = #[res] := rfl
    rw [this]
    rw [ih f (acc.push res)]
    rw [ih (fun i a => f (i + acc.size) a) #[res]]
    simp only [bind_pure_comp, Functor.map_map, Array.toList_push, List.append_assoc]
    have s2 : (acc.push res).size = acc.size + 1 := by simp only [Array.size_push]
    have s3 : #[res].size = 1 := rfl
    simp only [s2, s3]
    congr 1
    congr; funext i a
    have idx_eq : i + (acc.size + 1) = i + 1 + acc.size := by omega
    simp only [idx_eq]

private theorem List_mapIdxM_cons [Monad m] [LawfulMonad m] (h : α) (t : List α) (f : Nat → α → m β) :
    List.mapIdxM f (h :: t) = (do
      let b ← f 0 h
      let bs ← List.mapIdxM (fun i a => f (i + 1) a) t
      pure (b :: bs)) := by
  unfold List.mapIdxM
  unfold List.mapIdxM.go
  simp only [bind_pure_comp]
  congr; funext res
  rw [List_mapIdxM_go_eq]
  simp_all only [List.push_toArray, List.nil_append, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, List.cons_append, bind_pure_comp, List.cons.injEq, true_and, implies_true,
    map_inj_right_of_nonempty]
  split
  next x x_1 =>
    simp_all only
    rfl
  next x x_1 a
    as =>
    simp_all only [List.size_toArray, List.length_nil, Nat.zero_add, List.push_toArray, List.nil_append]
    rfl

theorem toList_mapFinIdxM [Monad m] [LawfulMonad m] {as : NonEmptyArray α}
    {f : (i : Nat) → α → (h : i < as.size) → m β} :
    toList <$> as.mapFinIdxM f = as.toList.mapFinIdxM (fun i a h => f i a (by
      simp_all only [toList, List.length_cons, Array.length_toList, size]
      omega)) := by
  obtain ⟨h, t⟩ := as
  simp only [mapFinIdxM, toList, bind_pure_comp, map_bind, Functor.map_map, List.length_cons, Array.length_toList]
  rw [List_mapFinIdxM_cons]
  simp only [bind_pure_comp]
  congr; funext b
  have eq_lhs : (fun as' : Array β => b :: as'.toList) = (List.cons b ∘ Array.toList) := by funext as'; rfl
  rw [eq_lhs]
  rw [Function.comp_def, ← Functor.map_map, _root_.Array.toList_mapFinIdxM]
  rfl

@[simp] theorem List.mapFinIdxM_eq_of_same_list [Monad m] [LawfulMonad m]
    {l : List α} {f g : (i : Nat) → α → i < l.length → m β}
    (h : ∀ i a hi, f i a hi = g i a hi) : l.mapFinIdxM f = l.mapFinIdxM g := by
  congr 1; funext i a hi; exact h i a hi

set_option pp.proofs true

private theorem List.mapFinIdxM_congr_lists [Monad m] {l1 l2 : List α} (hl : l1 = l2)
    (f : (i : Nat) → α → i < l1.length → m β)
    (g : (i : Nat) → α → i < l2.length → m β)
    (hfg : ∀ i a (h1 : i < l1.length) (h2 : i < l2.length), f i a h1 = g i a h2) :
    l1.mapFinIdxM f = l2.mapFinIdxM g := by
  subst hl
  have eq : f = g := by funext i a h; exact hfg i a h h
  rw [eq]

@[simp] theorem toArr_mapFinIdxM [Monad m] [LawfulMonad m] {as : NonEmptyArray α}
    {f : (i : Nat) → α → (h : i < as.size) → m β} :
    toArr <$> as.mapFinIdxM f = as.toArr.mapFinIdxM (fun i a h => f i a (by simpa only [size, toArr,
      Array.size_append, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add] using h)) := by
  have h_inj {X Y : m (Array β)} (h : Array.toList <$> X = Array.toList <$> Y) : X = Y := by
    have h2 : List.toArray <$> (Array.toList <$> X) = List.toArray <$> (Array.toList <$> Y) := by rw [h]
    simp only [Functor.map_map, Array.toArray_toList] at h2
    simp_all only [Array.toList_inj, implies_true, map_inj_right_of_nonempty, id_map']

  apply h_inj

  have lhs_eq : Array.toList <$> (toArr <$> as.mapFinIdxM f) = toList <$> as.mapFinIdxM f := by
    rw [Functor.map_map]
    simp_all only [Array.toList_inj, implies_true, map_inj_right_of_nonempty, toArr, Array.toList_append,
      List.cons_append, List.nil_append]
    rfl

  rw [lhs_eq, toList_mapFinIdxM, _root_.Array.toList_mapFinIdxM]

  -- Use `simp only` to safely rewrite the RHS list to match the LHS list (`as.toList`)
  -- This safely handles the dependent types without failing motives.
  apply List.mapFinIdxM_congr_lists (toArr_toList as).symm
  intro i a h1 h2

  rfl

@[simp] theorem toArr_mapIdxM [Monad m] [LawfulMonad m] {f : Nat → α → m β} {as : NonEmptyArray α} :
    toArr <$> as.mapIdxM f = as.toArr.mapIdxM f := by
  have h_inj {X Y : m (Array β)} (h : Array.toList <$> X = Array.toList <$> Y) : X = Y := by
    have h2 : List.toArray <$> (Array.toList <$> X) = List.toArray <$> (Array.toList <$> Y) := by rw [h]
    simp only [Functor.map_map, Array.toArray_toList] at h2
    simp_all only [Array.toList_inj, implies_true, map_inj_right_of_nonempty, id_map']
  apply h_inj
  simp only [mapIdxM, size, Array.mapIdxM, toArr]
  simp_all only [Array.toList_inj, implies_true, map_inj_right_of_nonempty, toArr_mapFinIdxM, toArr]

theorem toList_mapIdxM [Monad m] [LawfulMonad m] {f : Nat → α → m β} {as : NonEmptyArray α} :
    toList <$> as.mapIdxM f = as.toList.mapIdxM f := by
  obtain ⟨h, t⟩ := as
  simp only [mapIdxM, mapFinIdxM, bind_pure_comp, map_bind, Functor.map_map, toList]
  rw [List_mapIdxM_cons]
  congr; funext b
  have eq1 : Array.toList <$> Array.mapIdxM (fun i a => f (i + 1) a) t = List.mapIdxM (fun i a => f (i + 1) a) t.toList :=
    _root_.Array.toList_mapIdxM
  have eq2 : Array.mapIdxM (fun i a => f (i + 1) a) t = Array.mapFinIdxM t (fun i a _ => f (i + 1) a) := rfl
  rw [eq2] at eq1
  rw [← eq1]
  simp only [bind_pure_comp, Functor.map_map]

end NonEmpty.CorrectByConstruction.Array
