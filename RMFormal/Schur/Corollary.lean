import RMFormal.Schur.Padding

/-!
# Corollary 1.2 conditional on Theorem 1.1

This is a deduction from an explicit parameter `main : MainBoundPowered`.
That parameter is not an imported theorem.
-/

namespace SchurFormal

theorem corollary_1_2_of_main_bound
    (main : MainBoundPowered)
    (m r N d w : ℕ) (hm : 0 < m) (hr : 0 < r) (_hd : 0 < d)
    (color : ℕ → Fin r)
    (hAvoid : ∀ i : Fin r,
      ¬ HasEquation (ColorClass N color i)
          (d * (m + 1) + w) (d * m + w)) :
    N ^ m ≤ (2 * m + 1) ^ (r * m) * Nat.factorial r := by
  apply main m r N hm hr color
  intro i hshort
  have hpad := padding_lemma_3_1 (A := ColorClass N color i)
    (by omega : 0 < m + 1) hshort d w
  apply hAvoid i
  simpa only [Nat.mul_comm] using hpad

end SchurFormal
