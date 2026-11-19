import RMFormal.Schur.GcdOne
import RMFormal.Schur.ResidueNecessity
import RMFormal.Schur.ColorPaths
import RMFormal.Schur.PoweredWeights
import RMFormal.Schur.SlowGrowth
import RMFormal.Schur.WeightedDeletion
import RMFormal.Schur.ColorFiberMass
import RMFormal.Schur.GraphLayerDeletion
import RMFormal.Schur.DyadicLower
import RMFormal.Schur.SmallThresholds
import RMFormal.Schur.MassAccounting
import RMFormal.Schur.DeletionSize
import RMFormal.Schur.RealWeights
import RMFormal.Schur.WeightGain
import RMFormal.Schur.WeightMassInductionStep
import RMFormal.Schur.MassInduction
import RMFormal.Schur.FinalWeightBound
import RMFormal.Schur.WeightedLemmaReduction
import RMFormal.Schur.HeavyNeighbor
import RMFormal.Schur.SeedMass

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

-- New components of the weighted local-coloring induction
#print axioms SchurFormal.exists_slow_growth_step
#print axioms SchurFormal.exists_small_new_layer
#print axioms SchurFormal.weighted_deletion_preserves_mass
#print axioms SchurFormal.exists_color_with_large_weight
#print axioms SchurFormal.exists_heavy_color_fiber
#print axioms SchurFormal.incident_color_degree_strict_drop
#print axioms SchurFormal.selected_color_degree_strictly_drops
#print axioms SchurFormal.single_color_neighbor_in_ball_or_layer
#print axioms SchurFormal.color_radius_deletion_drops_degree

-- Real-weight, mass-induction, heavy-neighbor and final bound subproofs
#print axioms SchurFormal.old_mass_partition
#print axioms SchurFormal.mass_after_deletion_lower_bound
#print axioms SchurFormal.total_mass_preserved_by_layer_deletion
#print axioms SchurFormal.kept_card_lt_of_unselected_vertex
#print axioms SchurFormal.kept_card_lt_of_independent_class
#print axioms SchurFormal.real_color_weight_pos
#print axioms SchurFormal.real_color_weight_antitone
#print axioms SchurFormal.real_color_weight_step
#print axioms SchurFormal.real_color_weight_one_step_gain
#print axioms SchurFormal.real_color_weight_strict_gain
#print axioms SchurFormal.weighted_graph_deletion_preserves_mass
#print axioms SchurFormal.mass_le_one_by_strict_vertex_deletion
#print axioms SchurFormal.count_bound_of_uniform_weight
#print axioms SchurFormal.count_bound_of_total_vertex_mass
#print axioms SchurFormal.total_graph_weight_small
#print axioms SchurFormal.weighted_local_bound_of_deletion_principle
#print axioms SchurFormal.exists_large_finset_color
#print axioms SchurFormal.exists_heavy_incident_color
#print axioms SchurFormal.heavy_neighbor_seed_mass

-- Minimum color-degree-one induction case
import RMFormal.Schur.DegreeOneMassStep
#print axioms SchurFormal.independent_class_proper
#print axioms SchurFormal.degree_one_color_ball_is_univ
#print axioms SchurFormal.exists_heavy_independent_class
#print axioms SchurFormal.degree_one_mass_preserving_induced_subgraph
