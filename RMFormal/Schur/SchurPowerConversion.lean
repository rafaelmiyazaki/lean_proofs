import Mathlib

/-!
# Convert the real bound of Theorem 1.1 to an exact natural inequality

The weighted graph argument yields
  N <= (2m+1)^r * (r!)^(1/m)
in real arithmetic. Raise both sides to the mth power and
use the exact real root identity to obtain
  N^m <= (2m+1)^(r*m) * r!
as an inequality of natural numbers, with no rounding.
-/

namespace SchurFormal

theorem real_schur_bound_to_powered
    (m r N : ℕ) (hm : 0 < m)
    (hBound : (N : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ r *
      (Nat.factorial r : ℝ) ^ (1 / (m : ℝ))) :
    N ^ m ≤ (2 * m + 1) ^ (r * m) * Nat.factorial r := by
  have hRoot :
      ((Nat.factorial r : ℝ) ^ (1 / (m : ℝ))) ^ m =
        (Nat.factorial r : ℝ) := by
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow
        (x := (Nat.factorial r : ℝ)) (n := m)
        (by positivity : (0 : ℝ) ≤ Nat.factorial r)
        (Nat.ne_of_gt hm))
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N)
    hBound m
  have hRhs :
      (((2 * m + 1 : ℕ) : ℝ) ^ r *
        (Nat.factorial r : ℝ) ^ (1 / (m : ℝ))) ^ m =
        ((2 * m + 1 : ℕ) : ℝ) ^ (r * m) *
          (Nat.factorial r : ℝ) := by
    rw [mul_pow, ← pow_mul, hRoot]
  rw [hRhs] at hpow
  exact_mod_cast hpow

end SchurFormal
