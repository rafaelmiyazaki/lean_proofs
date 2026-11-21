import RMFormal.Schur.Section5Diameter
import RMFormal.Schur.Section5Sharpness
import RMFormal.Schur.LambertGreedyStep
import RMFormal.Schur.LambertWalk
import RMFormal.Schur.LambertPrefix
import RMFormal.Schur.LambertLength
import RMFormal.Schur.Section5Bridge
import RMFormal.Schur.MinimalZeroSum
import RMFormal.Schur.Section5Numerics

/-!
# Section 5: audit the exact proof-dependency boundary

The declarations below must depend only on standard Lean axioms,
never `sorryAx`. The bounded-obstruction theorem is NOT proved here:
`bounded_two_power_upper_of_bounded_obstruction` takes that proposition
as an explicit assumption.
-/

#print axioms SchurFormal.exists_minimal_schur_length
#print axioms SchurFormal.nonresidue_has_minimal_schur_length
#print axioms SchurFormal.ordered_difference_diameter_le
#print axioms SchurFormal.ordered_opposite_differences_le
#print axioms SchurFormal.consecutive_pair_exact_minimum
#print axioms SchurFormal.exists_lambert_greedy_step
#print axioms SchurFormal.exists_lambert_bounded_order
#print axioms SchurFormal.LambertBoundedWalk.prefix_bounds
#print axioms SchurFormal.lambert_length_of_distinct_prefixes
#print axioms SchurFormal.bounded_two_power_upper_of_bounded_obstruction

#print axioms SchurFormal.primitive_zero_sum_term_ne_zero

#print axioms SchurFormal.weighted_zero_sublist_of_prefix_collision
#print axioms SchurFormal.weighted_proper_prefix_sums_injective
#print axioms SchurFormal.lambert_length_of_no_proper_zero_sublist
#print axioms SchurFormal.lambert_length_of_primitive_finset
#print axioms SchurFormal.lambert_minimal_zero_sum_length
#print axioms SchurFormal.primitive_balanced_pair_to_zero_sum
#print axioms SchurFormal.primitive_balanced_pair_length_bound
#print axioms SchurFormal.section_5_numerical_conclusion
