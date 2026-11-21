import RMFormal.Schur.ZeroBlock

/-!
# Weighted prefix collisions, retaining original index multiplicities

This version of the zero-block lemma uses a list of *indices* and
an arbitrary integer weight function. It does not assume that
different indices have different numerical weights.

It gives a zero-sum proper sublist of indices, rather than a
sublist of the integer-valued weight image. This is convenient for
transferring a primitive indexed-family hypothesis.
-/

namespace SchurFormal

theorem weighted_zero_sublist_of_prefix_collision
    {α : Type*} (xs : List α) (f : α → ℤ) (i j : ℕ)
    (hij : i < j) (hj : j < xs.length)
    (hcollision :
      ((xs.take i).map f).sum = ((xs.take j).map f).sum) :
    ∃ ys : List α,
      ys.Sublist xs ∧ ys ≠ [] ∧ ys.length < xs.length ∧
        (ys.map f).sum = 0 := by
  let ys : List α := (xs.take j).drop i
  have hLen : ys.length = j - i := by
    simp [ys, List.length_drop, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsub : ys.Sublist xs :=
    (List.drop_sublist i (xs.take j)).trans (List.take_sublist j xs)
  have htake : (xs.take j).take i = xs.take i := by
    simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have hsplit :
      ((xs.take i).map f).sum + (ys.map f).sum =
        ((xs.take j).map f).sum := by
    have h := congrArg (fun z : List α => (z.map f).sum)
      (List.take_append_drop i (xs.take j))
    simpa only [List.map_append, List.sum_append, htake, ys] using h
  refine ⟨ys, hsub, ?_, ?_, ?_⟩
  · intro he
    have hzero : ys.length = 0 := by simp [he]
    omega
  · omega
  · omega

theorem weighted_proper_prefix_sums_injective
    {α : Type*} (xs : List α) (f : α → ℤ)
    (hprimitive : ∀ ys : List α, ys.Sublist xs →
      ys ≠ [] → ys.length < xs.length → (ys.map f).sum ≠ 0) :
    Function.Injective
      (fun i : Fin xs.length => ((xs.take (i : ℕ)).map f).sum) := by
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨ys, hsub, hnonempty, hproper, hsum⟩ :=
      weighted_zero_sublist_of_prefix_collision xs f i.val j.val hij j.isLt heq
    exact (hprimitive ys hsub hnonempty hproper) hsum
  · obtain ⟨ys, hsub, hnonempty, hproper, hsum⟩ :=
      weighted_zero_sublist_of_prefix_collision xs f j.val i.val hji i.isLt heq.symm
    exact (hprimitive ys hsub hnonempty hproper) hsum

end SchurFormal
