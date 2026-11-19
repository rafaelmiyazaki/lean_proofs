import Mathlib

/-!
# Weighted color-class pigeonhole

For a coloring with chi classes, one class carries at least 1/chi
of the total mass. This simple averaging argument is used twice
in the induction for Lemma 2.1.

The statement is about arbitrary real-valued masses assigned to
classes, and therefore does not yet assume a graph structure.
-/

namespace SchurFormal

/-- Some member of a nonempty finite indexed family has at
least the average of all entries. -/
theorem exists_color_with_large_weight
    (chi : ℕ) (hchi : 0 < chi) (M : Fin chi → ℝ) :
    ∃ i : Fin chi, (∑ j : Fin chi, M j) ≤ (chi : ℝ) * M i := by
  classical
  by_contra hnone
  have hlt (i : Fin chi) :
      (chi : ℝ) * M i < ∑ j : Fin chi, M j := by
    have hi : ¬ (∑ j : Fin chi, M j) ≤ (chi : ℝ) * M i := by
      intro hi
      exact hnone ⟨i, hi⟩
    exact lt_of_not_ge hi
  have hltSum :
      (∑ i : Fin chi, (chi : ℝ) * M i) <
        ∑ i : Fin chi, (∑ j : Fin chi, M j) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · exact Finset.univ_nonempty
    · intro i _
      exact hlt i
  have hleft :
      (∑ i : Fin chi, (chi : ℝ) * M i) =
        (chi : ℝ) * ∑ i : Fin chi, M i := by
    rw [Finset.mul_sum]
  have hright :
      (∑ i : Fin chi, (∑ j : Fin chi, M j)) =
        (chi : ℝ) * ∑ i : Fin chi, M i := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hleft, hright] at hltSum
  exact lt_irrefl _ hltSum

end SchurFormal
