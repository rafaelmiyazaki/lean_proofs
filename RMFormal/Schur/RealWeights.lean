import Mathlib

/-!
# Actual real-valued weights for weighted local coloring

Unlike the previous powered-weight identity, this file uses precisely
the real-valued weights of Lemma 2.1:
  w(d) = 1/(chi^d * (d!)^(1/ell)).
We establish positive weights and their monotonicity under
a decrease of incident color-degree.

The sharper multiplicative gain from losing one color still needs
a separate theorem.
-/

namespace SchurFormal

/-- Vertex weight as a function of the number of incident colors. -/
noncomputable def realColorWeight (chi ell d : ℕ) : ℝ :=
  1 / ((chi : ℝ) ^ d *
    (Nat.factorial d : ℝ) ^ (1 / (ell : ℝ)))

theorem real_color_weight_pos
    (chi ell d : ℕ) (hchi : 0 < chi) (hell : 0 < ell) :
    0 < realColorWeight chi ell d := by
  have hchiR : 0 < (chi : ℝ) := by exact_mod_cast hchi
  have hfact : 0 < (Nat.factorial d : ℝ) := by positivity
  have hpow : 0 < (Nat.factorial d : ℝ) ^ (1 / (ell : ℝ)) :=
    Real.rpow_pos_of_pos hfact _
  unfold realColorWeight
  exact one_div_pos.mpr (mul_pos (pow_pos hchiR d) hpow)

/-- The weight does not decrease when vertex deletion reduces
the number of incident edge colors. -/
theorem real_color_weight_antitone
    (chi ell a b : ℕ) (hchi : 1 ≤ chi) (hell : 0 < ell)
    (hab : a ≤ b) :
    realColorWeight chi ell b ≤ realColorWeight chi ell a := by
  have hchiR : 1 ≤ (chi : ℝ) := by exact_mod_cast hchi
  have haFact : 0 < (Nat.factorial a : ℝ) := by positivity
  have hbFact : 0 < (Nat.factorial b : ℝ) := by positivity
  have hfac : (Nat.factorial a : ℝ) ≤ (Nat.factorial b : ℝ) := by
    exact_mod_cast (Nat.factorial_le hab)
  have hexp : 0 ≤ (1 / (ell : ℝ)) := by positivity
  have hpowchi : (chi : ℝ) ^ a ≤ (chi : ℝ) ^ b :=
    pow_le_pow_right₀ hchiR hab
  have hpowfac :
      (Nat.factorial a : ℝ) ^ (1 / (ell : ℝ)) ≤
        (Nat.factorial b : ℝ) ^ (1 / (ell : ℝ)) :=
    Real.rpow_le_rpow haFact.le hfac hexp
  have hden :
      (chi : ℝ) ^ a * (Nat.factorial a : ℝ) ^ (1 / (ell : ℝ)) ≤
        (chi : ℝ) ^ b * (Nat.factorial b : ℝ) ^ (1 / (ell : ℝ)) := by
    calc
      _ ≤ (chi : ℝ) ^ b *
          (Nat.factorial a : ℝ) ^ (1 / (ell : ℝ)) :=
        mul_le_mul_of_nonneg_right hpowchi (Real.rpow_nonneg haFact.le _)
      _ ≤ (chi : ℝ) ^ b *
          (Nat.factorial b : ℝ) ^ (1 / (ell : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowfac (pow_nonneg (by positivity) _)
  have hdenPos : 0 < (chi : ℝ) ^ a *
      (Nat.factorial a : ℝ) ^ (1 / (ell : ℝ)) :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hchiR) _)
      (Real.rpow_pos_of_pos haFact _)
  unfold realColorWeight
  exact one_div_le_one_div_of_le hdenPos hden

end SchurFormal
