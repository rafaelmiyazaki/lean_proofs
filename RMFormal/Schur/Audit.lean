import RMFormal.Schur.GcdOne
import RMFormal.Schur.ResidueNecessity
import RMFormal.Schur.ColorPaths
import RMFormal.Schur.PoweredWeights
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

-- New affine-obstruction results
#print axioms SchurFormal.base_difference_certificate_forces_solution
#print axioms SchurFormal.gcd_differences_dvd_base_forces_solution
#print axioms SchurFormal.residue_obstruction_principle
#print axioms SchurFormal.bounded_set_no_solutions_iff_residue

-- Section 3: signed walks, charge-class independence, and local proper coloring
#print axioms SchurFormal.same_charge_edge_creates_solution
#print axioms SchurFormal.reachable_has_charge_coloring
#print axioms SchurFormal.differencePath_has_short_rep
#print axioms SchurFormal.radius_ball_charge_coloring

-- Arithmetic of weighted local coloring
#print axioms SchurFormal.powered_color_weight_step
