import Mathlib

/-!
# Powered weights for the weighted local-coloring lemma

The proof of Lemma 2.1 uses vertex weights
  w(d) = χ^{-d} (d!)^{-1/m}.
To avoid fractional powers in the first arithmetic stage, define
the mth power of the weight:
  W(d) = (χ^{d*m} d!)^{-1}.

When a vertex's incident color-degree drops from d to d-1,
this powered weight increases by exactly χ^m * d.
This module verifies that elementary identity over rational numbers.

The weighted graph induction itself is NOT proved here.
-/

namespace SchurFormal

/-- The mth power of a vertex weight with incident color-degree d. -/
def poweredColorWeight (χ m d : ℕ) : ℚ :=
  1 / ((χ : ℚ) ^ (d * m) * (Nat.factorial d : ℚ))

/-- Losing one incident color multiplies the powered weight
by χ^m d, the exact algebraic factor required by the
weighted local-coloring argument. -/
theorem powered_color_weight_step
    (χ m d : ℕ) (hχ : 0 < χ) (hd : 0 < d) :
    poweredColorWeight χ m (d - 1) =
      (χ : ℚ) ^ m * (d : ℚ) * poweredColorWeight χ m d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hχq : (χ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hχ)
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  simp only [poweredColorWeight, Nat.succ_sub_one,
    Nat.succ_mul, pow_add, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

end SchurFormal
