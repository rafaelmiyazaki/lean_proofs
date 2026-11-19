import RMFormal.Schur.GcdOne
import RMFormal.Schur.DyadicLower
import RMFormal.Schur.SmallThresholds

/-!
Print proof dependencies for the main *unconditional* statements.
Unexpected entries such as `sorryAx` would be a serious problem.
Lean's standard `propext`, `Quot.sound`, and `Classical.choice`
are not unproved statements of the research paper.
-/

#print axioms SchurFormal.padding_lemma_3_1
#print axioms SchurFormal.affine_relation_forces_solution
#print axioms SchurFormal.difference_certificate_forces_solution
#print axioms SchurFormal.integerListGcd_bezout
#print axioms SchurFormal.integerListGcd_dvd_entry
#print axioms SchurFormal.gcd_one_differences_force_solution
#print axioms SchurFormal.two_power_lower
#print axioms SchurFormal.two_color_four
