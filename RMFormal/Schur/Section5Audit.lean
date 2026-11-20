import RMFormal.Schur.Section5Diameter
import RMFormal.Schur.Section5Sharpness
import RMFormal.Schur.LambertGreedyStep
import RMFormal.Schur.LambertWalk
import RMFormal.Schur.LambertPrefix
import RMFormal.Schur.LambertLength
import RMFormal.Schur.Section5Bridge
import RMFormal.Schur.MinimalZeroSum

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
