import RMFormal.Schur.MainTheorem11
import RMFormal.Schur.Corollary

/-!
# Unconditional Corollary 1.2

The earlier padding corollary required MainBoundPowered as an
explicit hypothesis. Theorem 1.1 now provides precisely that
proposition. This closes the auxiliary generalized equation
bound with no research-theorem assumptions.
-/

namespace SchurFormal

theorem corollary_1_2_unconditional
    (m r N d w : ℕ) (hm : 0 < m) (hr : 0 < r) (hd : 0 < d)
    (color : ℕ → Fin r)
    (hAvoid : ∀ i : Fin r,
      ¬ HasEquation (ColorClass N color i)
          (d * (m + 1) + w) (d * m + w)) :
    N ^ m ≤ (2 * m + 1) ^ (r * m) * Nat.factorial r :=
  corollary_1_2_of_main_bound main_bound_powered
    m r N d w hm hr hd color hAvoid

end SchurFormal
