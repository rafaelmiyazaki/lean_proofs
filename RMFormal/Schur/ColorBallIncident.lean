import RMFormal.Schur.GraphLayers

/-!
# Every vertex in a nontrivial monochromatic component sees its color

If the base vertex is incident to color c and the edge coloring
is symmetric, every vertex reached by a color-c walk is also
incident to color c. This includes the radius-i ball, so
selected independent vertices lose an actually present color
during the deletion argument of weighted Lemma 2.1.

The proof allows walks with repeated vertices and self-steps.
-/

namespace SchurFormal

/-- A symmetric color-c walk starting at a vertex incident to c
ends at a vertex incident to c. -/
theorem incident_color_of_walk
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (a : V)
    (hSym : ∀ x y : V, E x y = E y x)
    (hBase : c ∈ incidentColors E Finset.univ a)
    {x : V} {n : ℕ} (hp : SingleColorWalk E c a x n) :
    c ∈ incidentColors E Finset.univ x := by
  induction hp with
  | nil => exact hBase
  | snoc hprev hedge ih =>
    rename_i start b dest steps
    by_cases hEq : b = dest
    · subst dest
      exact ih
    · apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · exact hEq
      · rw [hSym dest b]
        exact hedge

/-- Every vertex of a color-c ball has an incident c-colored edge
provided the base vertex does. -/
theorem incident_color_of_ball
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (a : V)
    (hSym : ∀ x y : V, E x y = E y x)
    (hBase : c ∈ incidentColors E Finset.univ a)
    (i : ℕ) (x : V)
    (hx : x ∈ singleColorBall E c a i) :
    c ∈ incidentColors E Finset.univ x := by
  classical
  have hreach : WithinSingleColorRadius E c a i x := by
    unfold singleColorBall at hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨n, _, hp⟩ := hreach
  exact incident_color_of_walk E c a hSym hBase hp

end SchurFormal
