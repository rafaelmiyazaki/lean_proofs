import RMFormal.Schur.GraphLayers

/-!
# The weighted deletion geometry for color-radius balls

This discharges the abstract closure assumption of
`selected_color_degree_strictly_drops` in `ColorDeletion.lean`:
take S to be a color-c radius-i ball, T to be the next layer,
and S' an independent class inside S. A color-c edge from
any vertex of S' ends in S ∪ T, so removing T and S \ S'
removes color c entirely from every retained selected vertex.

The global weighted induction remains unproved.
-/

namespace SchurFormal

/-- For any independent class S' within a color-radius-i ball,
every selected vertex loses color c in the induced graph
after the layer deletion. -/
theorem color_radius_deletion_drops_degree
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (a : V) (i : ℕ)
    (Sprime : Finset V)
    (hSprime : Sprime ⊆ singleColorBall E c a i)
    (hIndependent : ∀ x ∈ Sprime, ∀ y ∈ Sprime,
      x ≠ y → E x y ≠ c)
    (x : V) (hx : x ∈ Sprime)
    (hIncident : c ∈ incidentColors E Finset.univ x) :
    incidentColorDegree E
      (keptAfterLayerDeletion Finset.univ
        (singleColorBall E c a i)
        (singleColorBall E c a (i + 1) \
          singleColorBall E c a i) Sprime) x <
      incidentColorDegree E Finset.univ x := by
  apply selected_color_degree_strictly_drops E
      Finset.univ (singleColorBall E c a i)
      (singleColorBall E c a (i + 1) \
        singleColorBall E c a i) Sprime c
      (by
        intro y _
        exact Finset.mem_univ y)
      ?_ hIndependent x hx hIncident
  intro z hz y _ hzy
  exact single_color_neighbor_in_ball_or_layer
    E c a z y i (hSprime hz) hzy

end SchurFormal
