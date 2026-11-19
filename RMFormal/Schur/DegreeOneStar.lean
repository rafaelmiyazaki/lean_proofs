import RMFormal.Schur.MinColorDegree

/-!
# The minimum-color-degree-one branch of weighted Lemma 2.1

When a vertex has incident color-degree one, all edges leaving
that vertex in the induced complete graph have the same color.
This identifies the entire induced vertex set with its
radius-one monochromatic neighborhood.

The heavier-color-class selection and weight comparison in this
branch are separate downstream steps.
-/

namespace SchurFormal

/-- If vertex v has at most one incident color in U, then
all edges from v to other vertices of U have the same color. -/
theorem incident_degree_one_uniform_star
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (U : Finset V) (v x y : V)
    (hdeg : incidentColorDegree E U v ≤ 1)
    (hx : x ∈ U) (hy : y ∈ U)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    E v x = E v y := by
  have hcX : E v x ∈ incidentColors E U v := by
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩, rfl⟩
  have hcY : E v y ∈ incidentColors E U v := by
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_erase.mpr ⟨hyv, hy⟩, rfl⟩
  exact (Finset.card_le_one_iff.mp hdeg) hcX hcY

/-- On a finite complete graph, the color-c radius-one ball
around a vertex with only one incident color is the entire graph.
Here the graph is represented by its finite vertex type. -/
theorem degree_one_color_ball_is_univ
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (v y : V) (hne : y ≠ v)
    (hdeg : incidentColorDegree E Finset.univ v = 1)
    (c : C) (hvc : E v y = c) :
    singleColorBall E c v 1 = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  unfold singleColorBall
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_univ x
  · by_cases hx : x = v
    · subst x
      exact ⟨0, by omega, SingleColorWalk.nil v⟩
    · have hxx : E v x = c := by
        have hu := incident_degree_one_uniform_star E Finset.univ v x y
          (by omega) (Finset.mem_univ _) (Finset.mem_univ _) hx hne
        exact hu.trans hvc
      exact ⟨1, by omega, SingleColorWalk.snoc (SingleColorWalk.nil v) hxx⟩

end SchurFormal
