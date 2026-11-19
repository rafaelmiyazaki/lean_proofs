import RMFormal.Schur.RealWeights

/-!
# Multiplicative gain in actual vertex weights

For chi ≥ 1 and ell ≥ 1, the exact weight function
  w(d)=1/(chi^d (d!)^(1/ell))
satisfies w(k)=chi*(k+1)^(1/ell)*w(k+1).

Consequently, if a vertex has color-degree at least d_min and
loses one or more colors after deleting vertices, its new
weight is at least chi*d_min^(1/ell) times its old weight.
This is the sharp gain used in Lemma 2.1.
-/

namespace SchurFormal

theorem real_color_weight_step
    (chi ell k : ℕ) (hchi : 0 < chi) (hell : 0 < ell) :
    realColorWeight chi ell k =
      (chi : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (1 / (ell : ℝ)) *
        realColorWeight chi ell (k + 1) := by
  have hchiR : 0 < (chi : ℝ) := by exact_mod_cast hchi
  have hfact : 0 < (Nat.factorial k : ℝ) := by positivity
  have hnext : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hrpowFact :
      (((Nat.factorial (k + 1) : ℕ) : ℝ)) ^ (1 / (ell : ℝ)) =
        ((k + 1 : ℕ) : ℝ) ^ (1 / (ell : ℝ)) *
          (Nat.factorial k : ℝ) ^ (1 / (ell : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact Real.mul_rpow hnext.le hfact.le
  have hrpowNext :
      0 < ((k + 1 : ℕ) : ℝ) ^ (1 / (ell : ℝ)) :=
    Real.rpow_pos_of_pos hnext _
  have hrpowFactPos :
      0 < (Nat.factorial k : ℝ) ^ (1 / (ell : ℝ)) :=
    Real.rpow_pos_of_pos hfact _
  simp only [realColorWeight, pow_succ, hrpowFact]
  field_simp
  ring

/-- A single lost color increases weight by at least the factor
chi*d_min^(1/ell), provided the previous degree was ≥ d_min. -/
theorem real_color_weight_one_step_gain
    (chi ell k dmin : ℕ) (hchi : 0 < chi) (hell : 0 < ell)
    (hmin : dmin ≤ k + 1) :
    (chi : ℝ) * (dmin : ℝ) ^ (1 / (ell : ℝ)) *
        realColorWeight chi ell (k + 1) ≤
      realColorWeight chi ell k := by
  have hminR : (dmin : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hmin
  have hbase : (0 : ℝ) ≤ (dmin : ℝ) := by positivity
  have hexp : 0 ≤ (1 / (ell : ℝ)) := by positivity
  have hpow : (dmin : ℝ) ^ (1 / (ell : ℝ)) ≤
      ((k + 1 : ℕ) : ℝ) ^ (1 / (ell : ℝ)) :=
    Real.rpow_le_rpow hbase hminR hexp
  have hchiR : 0 ≤ (chi : ℝ) := by positivity
  have hw : 0 ≤ realColorWeight chi ell (k + 1) :=
    (real_color_weight_pos chi ell (k + 1) hchi hell).le
  calc
    _ ≤ (chi : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (1 / (ell : ℝ)) *
          realColorWeight chi ell (k + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hchiR) hw
    _ = realColorWeight chi ell k :=
      (real_color_weight_step chi ell k hchi hell).symm

/-- The actual vertex-weight multiplier under any strict decrease
in color-degree, using a global lower bound on the old degree. -/
theorem real_color_weight_strict_gain
    (chi ell oldDegree newDegree dmin : ℕ)
    (hchi : 0 < chi) (hell : 0 < ell)
    (hd : newDegree < oldDegree) (hmin : dmin ≤ oldDegree) :
    (chi : ℝ) * (dmin : ℝ) ^ (1 / (ell : ℝ)) *
        realColorWeight chi ell oldDegree ≤
      realColorWeight chi ell newDegree := by
  cases oldDegree with
  | zero => omega
  | succ k =>
    have hnew : newDegree ≤ k := by omega
    calc
      _ ≤ realColorWeight chi ell k :=
        real_color_weight_one_step_gain chi ell k dmin hchi hell
          (by simpa only [Nat.succ_eq_add_one] using hmin)
      _ ≤ realColorWeight chi ell newDegree :=
        real_color_weight_antitone chi ell newDegree k
          (by omega) hell hnew

end SchurFormal
