import RMFormal.Schur.MinimalZeroSum

/-!
# Primitive zero sums: collisions of prefix sums

If two distinct proper prefixes of an integer list have the same
sum, their difference is a nonempty proper contiguous sublist
whose sum is zero. Consequently, a list having no nonempty
proper zero-sum sublist has pairwise distinct proper-prefix sums.

This is the combinatorial injectivity component of Lambert's
length argument, isolated from the permutation machinery.
-/

namespace SchurFormal

/-- A collision between two proper prefix sums yields a
nonempty, proper, zero-sum sublist. -/
theorem zero_sum_sublist_of_prefix_collision
    (xs : List ℤ) (i j : ℕ)
    (hij : i < j) (hj : j < xs.length)
    (hcollision : (xs.take i).sum = (xs.take j).sum) :
    ∃ ys : List ℤ,
      ys.Sublist xs ∧ ys ≠ [] ∧ ys.length < xs.length ∧ ys.sum = 0 := by
  let ys : List ℤ := (xs.take j).drop i
  have hLen : ys.length = j - i := by
    simp [ys, List.length_drop, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  have hsub : ys.Sublist xs :=
    (List.drop_sublist i (xs.take j)).trans (List.take_sublist j xs)
  have htake : (xs.take j).take i = xs.take i := by
    simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have hsplit : (xs.take i).sum + ys.sum = (xs.take j).sum := by
    have h := congrArg List.sum (List.take_append_drop i (xs.take j))
    simpa only [List.sum_append, htake, ys] using h
  refine ⟨ys, hsub, ?_, ?_, ?_⟩
  · intro he
    have hzero : ys.length = 0 := by simp [he]
    omega
  · omega
  · omega

/-- If every proper nonempty sublist has nonzero sum, then
proper-prefix sums are pairwise distinct. -/
theorem proper_prefix_sums_injective
    (xs : List ℤ)
    (hprimitive : ∀ ys : List ℤ, ys.Sublist xs →
      ys ≠ [] → ys.length < xs.length → ys.sum ≠ 0) :
    Function.Injective
      (fun i : Fin xs.length => (xs.take (i : ℕ)).sum) := by
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨ys, hsub, hnonempty, hproper, hsum⟩ :=
      zero_sum_sublist_of_prefix_collision xs i.val j.val hij j.isLt heq
    exact (hprimitive ys hsub hnonempty hproper) hsum
  · obtain ⟨ys, hsub, hnonempty, hproper, hsum⟩ :=
      zero_sum_sublist_of_prefix_collision xs j.val i.val hji i.isLt heq.symm
    exact (hprimitive ys hsub hnonempty hproper) hsum

end SchurFormal
