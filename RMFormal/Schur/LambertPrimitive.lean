import RMFormal.Schur.ZeroBlock

/-!
# Lambert's length estimate from the primitive-sublist condition

Combine:
1. the bounded greedy permutation of the terms,
2. the absence of nonempty proper zero-sum sublists,
3. distinctness of all proper prefix sums, and
4. the interval pigeonhole bound.

The hypothesis is stated on the actually constructed reordered
list; transferring primitivity from the original indexed multiset
to that list remains a separate formal obligation.
-/

namespace SchurFormal

/-- A Lambert greedy ordering with no nonempty proper zero-sum
sublist has at most a+b terms. -/
theorem lambert_length_of_no_proper_zero_sublist
    {α : Type*} (f : α → ℤ) (a b : ℕ)
    (t : ℤ) (order : List α)
    (hwalk : LambertBoundedWalk f a b t order)
    (hprimitive : ∀ ys : List ℤ,
      ys.Sublist (order.map f) →
      ys ≠ [] → ys.length < (order.map f).length →
      ys.sum ≠ 0) :
    order.length ≤ a + b := by
  have hlistInject :=
    proper_prefix_sums_injective (order.map f) hprimitive
  have hpartialInject :
      Function.Injective
        (fun i : Fin order.length =>
          t + ((order.take (i : ℕ)).map f).sum) := by
    intro i j heq
    have hcancel :
        ((order.take (i : ℕ)).map f).sum =
          ((order.take (j : ℕ)).map f).sum :=
      add_left_cancel heq
    have hi : i.val < (order.map f).length := by
      simpa only [List.length_map] using i.isLt
    have hj : j.val < (order.map f).length := by
      simpa only [List.length_map] using j.isLt
    have hmap :
        ((order.map f).take i.val).sum =
          ((order.map f).take j.val).sum := by
      simpa only [List.map_take] using hcancel
    have heqFin : (⟨i.val, hi⟩ : Fin (order.map f).length) =
        (⟨j.val, hj⟩ : Fin (order.map f).length) :=
      hlistInject hmap
    exact Fin.ext (congrArg Fin.val heqFin)
  exact lambert_length_of_distinct_prefixes
    f a b t order hwalk hpartialInject

end SchurFormal
