import Mathlib

/-!
# Slow-growth layer in the weighted local-coloring lemma

For a nonnegative mass sequence bounded by the total mass, once the
initial mass is sufficiently large, one of the first ell growth
steps cannot exceed a fixed multiplicative factor alpha.

This is the abstract "there exists an i in [ell]" step in
Lemma 2.1 of Miyazaki--Mulrenin--Pohoata--Zheng.
It uses only real arithmetic, independently of the graph structure.
-/

namespace SchurFormal

/-- Abstract slow-growth lemma. If `M (ell+1) ≤ T ≤ alpha^ell * M 1`,
then among the first ell steps one satisfies `M (i+1) ≤ alpha * M i`.
Here `alpha ≥ 1`, and `ell > 0`. -/
theorem exists_slow_growth_step
    (ell : ℕ) (hEll : 0 < ell)
    (alpha T : ℝ) (hAlpha : 1 ≤ alpha)
    (M : ℕ → ℝ)
    (hUpper : M (ell + 1) ≤ T)
    (hSeed : T ≤ alpha ^ ell * M 1) :
    ∃ i ∈ Finset.Icc 1 ell, M (i + 1) ≤ alpha * M i := by
  by_contra hNot
  have hFast (i : ℕ) (hi : 1 ≤ i) (hiEll : i ≤ ell) :
      alpha * M i < M (i + 1) := by
    by_contra hSlow
    exact hNot ⟨i, Finset.mem_Icc.mpr ⟨hi, hiEll⟩,
      le_of_not_gt hSlow⟩
  have hPos : 0 < alpha := lt_of_lt_of_le zero_lt_one hAlpha
  have hGrowth (k : ℕ) (hk : 1 ≤ k) (hkEll : k ≤ ell) :
      alpha ^ k * M 1 < M (k + 1) := by
    induction k with
    | zero =>
      omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa [pow_one] using hFast 1 (by omega) hkEll
      · have hprev : alpha ^ k * M 1 < M (k + 1) :=
          ih (by omega) (by omega)
        calc
          alpha ^ (k + 1) * M 1 =
              alpha * (alpha ^ k * M 1) := by rw [pow_succ]; ring
          _ < alpha * M (k + 1) :=
              mul_lt_mul_of_pos_left hprev hPos
          _ < M ((k + 1) + 1) :=
              hFast (k + 1) (by omega) (by omega)
  have hContr := hGrowth ell (by omega) (by omega)
  linarith

/-- Equivalent version in terms of the size of the newly-added
layer rather than the cumulative mass. -/
theorem exists_small_new_layer
    (ell : ℕ) (hEll : 0 < ell)
    (alpha T : ℝ) (hAlpha : 1 ≤ alpha)
    (M : ℕ → ℝ)
    (hUpper : M (ell + 1) ≤ T)
    (hSeed : T ≤ alpha ^ ell * M 1) :
    ∃ i ∈ Finset.Icc 1 ell,
      M (i + 1) - M i ≤ (alpha - 1) * M i := by
  obtain ⟨i, hi, hstep⟩ :=
    exists_slow_growth_step ell hEll alpha T hAlpha M hUpper hSeed
  refine ⟨i, hi, ?_⟩
  nlinarith

end SchurFormal
