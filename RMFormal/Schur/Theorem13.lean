import RMFormal.Schur.ResidueRootProduct
import RMFormal.Schur.DyadicLower

/-!
# Theorem 1.3: both directions

This packages the general 2^r upper bound and the matching
(2^r - 1)-point lower construction as one unconditional theorem.

The upper bound uses the independent root-of-unity argument from
ResidueRootProduct, not an assumed covering theorem.
-/

namespace SchurFormal

theorem theorem_1_3_unconditional : TwoPowerUpper ∧ TwoPowerLower :=
  ⟨two_power_upper_unconditional, two_power_lower⟩

#print axioms primitive_root_pow_eq_iff_mod
#print axioms residue_covering_from_exponential
#print axioms two_power_upper_unconditional
#print axioms theorem_1_3_unconditional

end SchurFormal
