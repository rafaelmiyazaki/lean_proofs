import RMFormal.Schur.GraphLayerDeletion

/-!
# Strict reduction of the vertex set in weighted deletion

The induction proving the weighted local-coloring lemma requires the
retained induced subgraph to have strictly fewer vertices.

If a color-c edge is contained in the radius-i ball and S' is a
color-c independent subset of that ball, then S' is a proper subset.
Deleting the other vertices of the ball (and the next layer) therefore
strictly decreases the ambient vertex set.

In the application i >= 1 and a color-c edge from the base point
provides the required edge inside the ball.
-/

namespace SchurFormal

theorem independent_class_proper
    {V C : Type*} [DecidableEq V]
    (E : V → V → C) (c : C) (S Sprime : Finset V)
    (hsub : Sprime ⊆ S)
    (x y : V) (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) (hxy : E x y = c)
    (hindep : ∀ u ∈ Sprime, ∀ v ∈ Sprime,
      u ≠ v → E u v ≠ c) :
    Sprime ⊂ S := by
  apply (Finset.ssubset_iff_of_subset hsub).2
  by_cases hx' : x ∈ Sprime
  · have hy' : y ∉ Sprime := by
      intro hy'
      exact hindep x hx' y hy' hne hxy
    exact ⟨y, hy, hy'⟩
  · exact ⟨x, hx, hx'⟩

theorem deletion_strictly_reduces_vertex_set
    {V : Type*} [DecidableEq V]
    (U S T Sprime : Finset V)
    (hS : S ⊆ U)
    (hSprime : Sprime ⊂ S) :
    keptAfterLayerDeletion U S T Sprime ⊂ U := by
  have hsub : Sprime ⊆ U := Finset.Subset.trans hSprime.subset hS
  have hkeep : keptAfterLayerDeletion U S T Sprime ⊆ U :=
    kept_vertices_subset hsub
  apply (Finset.ssubset_iff_of_subset hkeep).2
  obtain ⟨x, hxS, hxNot⟩ :=
    (Finset.ssubset_iff_of_subset hSprime.subset).1 hSprime
  refine ⟨x, hS hxS, ?_⟩
  intro hx
  change x ∈ (U \ (S ∪ T)) ∪ Sprime at hx
  rcases Finset.mem_union.mp hx with hout | hin
  · have hnot := (Finset.mem_sdiff.mp hout).2
    exact hnot (Finset.mem_union.mpr (Or.inl hxS))
  · exact hxNot hin

/-- In a finite graph, a color-c edge from the base vertex
lies entirely within every radius-i ball for i>=1. -/
theorem base_edge_in_color_ball
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C)
    (a y : V) (i : ℕ) (hi : 1 ≤ i)
    (hay : E a y = c) :
    a ∈ singleColorBall E c a i ∧
      y ∈ singleColorBall E c a i := by
  classical
  constructor
  · unfold singleColorBall
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, 0, by omega, ?_⟩
    exact SingleColorWalk.nil a
  · unfold singleColorBall
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, 1, hi, ?_⟩
    exact SingleColorWalk.snoc (SingleColorWalk.nil a) hay

/-- Every color-c independent class inside a radius-i ball is
proper if i>=1 and the base vertex has an incident c-edge. -/
theorem radius_ball_independent_class_proper
    {V C : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → C) (c : C)
    (a y : V) (i : ℕ) (hi : 1 ≤ i)
    (hne : a ≠ y) (hay : E a y = c)
    (Sprime : Finset V)
    (hsub : Sprime ⊆ singleColorBall E c a i)
    (hindep : ∀ u ∈ Sprime, ∀ v ∈ Sprime,
      u ≠ v → E u v ≠ c) :
    Sprime ⊂ singleColorBall E c a i := by
  obtain ⟨ha, hy⟩ := base_edge_in_color_ball E c a y i hi hay
  exact independent_class_proper E c
    (singleColorBall E c a i) Sprime hsub a y
    ha hy hne hay hindep

end SchurFormal
