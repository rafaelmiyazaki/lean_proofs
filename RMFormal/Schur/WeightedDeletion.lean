import Mathlib

/-!
# The weighted deletion inequality (Lemma 2.1)

This separates the final inequality in the induction step from the
graph-theoretic work of constructing the sets S, T and S'.

Notation:
W  = old total mass,
s  = mass of the closed colored ball S,
t  = mass of its next layer T,
s' = mass of the heaviest proper color class S',
W' = total mass after deleting T and S \ S'.

Given t <= (alpha-1)s, chi*s' >= s and the loss-of-color mass
increase W' >= W-s-t+chi*alpha*s', the new mass cannot be smaller.

The geometric construction of S, T and S' is still missing.
-/

namespace SchurFormal

/-- The algebraic heart of the weighted deletion argument in Lemma 2.1. -/
theorem weighted_deletion_preserves_mass
    (W Wnew s t sprime chi alpha : ℝ)
    (halpha : 1 ≤ alpha)
    (hLayer : t ≤ (alpha - 1) * s)
    (hClass : s ≤ chi * sprime)
    (hNew : W - s - t + chi * alpha * sprime ≤ Wnew) :
    W ≤ Wnew := by
  have hPos : 0 ≤ alpha := le_trans (by norm_num : (0 : ℝ) ≤ 1) halpha
  have hGain : alpha * s ≤ chi * alpha * sprime := by
    calc
      alpha * s ≤ alpha * (chi * sprime) :=
        mul_le_mul_of_nonneg_left hClass hPos
      _ = chi * alpha * sprime := by ring
  nlinarith

/-- With `alpha = 1`, a vanished next layer is enough to
    preserve weighted mass. -/
theorem weighted_deletion_no_layer
    (W Wnew s sprime chi : ℝ)
    (hClass : s ≤ chi * sprime)
    (hNew : W - s + chi * sprime ≤ Wnew) :
    W ≤ Wnew := by
  linarith

end SchurFormal
