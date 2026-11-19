import RMFormal.Schur.ColorPaths

/-!
# Finite difference-colored complete graphs

The quantitative Schur bound applies the weighted local-coloring
lemma to the graph on Fin N where the color of an edge is the
given color of the positive integer difference.

The diagonal color is immaterial because all edges in a complete
graph join distinct vertices.
-/

namespace SchurFormal

/-- Symmetric edge coloring by the absolute difference of two
finite integer vertices. -/
def finiteDifferenceColor {r N : ℕ}
    (color : ℕ → Fin r) (x y : Fin N) : Fin r :=
  color (max x.1 y.1 - min x.1 y.1)

theorem finite_difference_color_symmetric {r N : ℕ}
    (color : ℕ → Fin r) (x y : Fin N) :
    finiteDifferenceColor color x y =
      finiteDifferenceColor color y x := by
  simp [finiteDifferenceColor, max_comm, min_comm]

/-- A color-i finite edge is an actual difference edge in the
positive integer color class i. -/
theorem finite_color_edge_is_difference
    {r N : ℕ} (color : ℕ → Fin r) (i : Fin r)
    (x y : Fin N) (hxy : x ≠ y)
    (hcol : finiteDifferenceColor color x y = i) :
    DifferenceEdge (ColorClass N color i) x.1 y.1 := by
  have hval : x.1 ≠ y.1 := by
    intro heq
    exact hxy (Fin.ext heq)
  by_cases hlt : x.1 < y.1
  · have hColor : color (y.1 - x.1) = i := by
      simpa [finiteDifferenceColor, max_eq_right (le_of_lt hlt),
        min_eq_left (le_of_lt hlt)] using hcol
    have hRange : 1 ≤ y.1 - x.1 ∧ y.1 - x.1 ≤ N := by
      have hyBound := y.isLt
      omega
    exact Or.inl ⟨hlt, ⟨hRange, hColor⟩⟩
  · have hgt : y.1 < x.1 := by omega
    have hColor : color (x.1 - y.1) = i := by
      simpa [finiteDifferenceColor, max_eq_left (le_of_lt hgt),
        min_eq_right (le_of_lt hgt)] using hcol
    have hRange : 1 ≤ x.1 - y.1 ∧ x.1 - y.1 ≤ N := by
      have hxBound := x.isLt
      omega
    exact Or.inr ⟨hgt, ⟨hRange, hColor⟩⟩

end SchurFormal
