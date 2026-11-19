import RMFormal.Schur.FiniteDifferenceGraph
import RMFormal.Schur.GraphLayers

/-!
# Lifting monochromatic finite graph walks to Schur difference paths

A color-i walk in the finite difference-colored graph on Fin N
projects to a walk in the integer difference graph of the
color class A_i. Diagonal steps can be omitted, so the
projected walk has length at most the original length.
-/

namespace SchurFormal

theorem finite_color_walk_to_difference_path
    {r N : ℕ} (color : ℕ → Fin r) (i : Fin r)
    {a x : Fin N} {n : ℕ}
    (hp : SingleColorWalk (finiteDifferenceColor color) i a x n) :
    ∃ k : ℕ, k ≤ n ∧
      DifferencePath (ColorClass N color i) a.1 x.1 k := by
  induction hp with
  | nil =>
    exact ⟨0, by omega, DifferencePath.nil _⟩
  | snoc hprev hedge ih =>
    rename_i first b d steps
    obtain ⟨k, hk, hDiff⟩ := ih
    by_cases hEq : b = d
    · subst d
      exact ⟨k, by omega, hDiff⟩
    · have hEdge :
          DifferenceEdge (ColorClass N color i) b.1 d.1 :=
        finite_color_edge_is_difference color i b d hEq hedge
      exact ⟨k + 1, by omega, DifferencePath.snoc hDiff hEdge⟩

/-- A finite monochromatic graph ball embeds in the
corresponding integer-difference radius ball. -/
theorem finite_color_ball_reaches_difference
    {r N : ℕ} (color : ℕ → Fin r) (i : Fin r)
    (a x : Fin N) (m : ℕ)
    (hx : x ∈ singleColorBall (finiteDifferenceColor color) i a m) :
    WithinDifferenceRadius (ColorClass N color i) a.1 m x.1 := by
  classical
  have hReach : WithinSingleColorRadius
      (finiteDifferenceColor color) i a m x := by
    unfold singleColorBall at hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨n, hn, hp⟩ := hReach
  obtain ⟨k, hk, hDiff⟩ :=
    finite_color_walk_to_difference_path color i hp
  exact ⟨k, by omega, hDiff⟩

/-- Every finite monochromatic radius-m ball admits the
charge coloring with 2m+1 colors when the corresponding
Schur color class avoids the (m+1,m) equation. -/
theorem finite_ball_charge_coloring
    {r N : ℕ} (color : ℕ → Fin r) (i : Fin r)
    (a : Fin N) (m : ℕ)
    (hAvoid : ¬ HasEquation (ColorClass N color i) (m + 1) m) :
    ∃ col : Fin N → Fin (2 * m + 1),
      ∀ x ∈ singleColorBall (finiteDifferenceColor color) i a m,
      ∀ y ∈ singleColorBall (finiteDifferenceColor color) i a m,
        x ≠ y →
        finiteDifferenceColor color x y = i →
        col x ≠ col y := by
  classical
  let A : Set ℕ := ColorClass N color i
  obtain ⟨colInt, hProper⟩ :=
    radius_ball_charge_coloring (A := A) (a := a.1) (m := m) hAvoid
  let col : Fin N → Fin (2 * m + 1) := fun x =>
    if hx : WithinDifferenceRadius A a.1 m x.1 then
      colInt ⟨x.1, hx⟩
    else ⟨0, by omega⟩
  refine ⟨col, ?_⟩
  intro x hx y hy hne hEdgeColor
  have hxReach : WithinDifferenceRadius A a.1 m x.1 :=
    finite_color_ball_reaches_difference color i a x m hx
  have hyReach : WithinDifferenceRadius A a.1 m y.1 :=
    finite_color_ball_reaches_difference color i a y m hy
  have hDiff : DifferenceEdge A x.1 y.1 :=
    finite_color_edge_is_difference color i x y hne hEdgeColor
  have hDifferent :
      colInt ⟨x.1, hxReach⟩ ≠ colInt ⟨y.1, hyReach⟩ :=
    hProper ⟨x.1, hxReach⟩ ⟨y.1, hyReach⟩ hDiff
  simpa only [col, dif_pos hxReach, dif_pos hyReach] using hDifferent

end SchurFormal
