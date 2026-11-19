import RMFormal.Schur.BallMass

/-!
# The heavy initial colored neighborhood sits in the radius-one ball

The weighted graph induction starts from a color-c star at v.
The star plus v is contained in the radius-one ball. Thus
the latter's mass is at least the star's mass for nonnegative
weights. This is the set-theoretic bridge between the
heavy-neighbor averaging argument and the slow-growth lemma.
-/

namespace SchurFormal

private def colorStar
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (v : V) : Finset V :=
  (Finset.univ.erase v).filter (fun x => E v x = c)

/-- The selected monochromatic star and its center lie in
the graph's radius-one color-c ball. -/
private theorem star_insert_subset_ball
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (v : V) :
    insert v (colorStar E c v) ⊆ singleColorBall E c v 1 := by
  classical
  intro x hx
  rcases Finset.mem_insert.mp hx with h | h
  · subst x
    unfold singleColorBall
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨0, by omega, SingleColorWalk.nil v⟩⟩
  · have hcolor : E v x = c := (Finset.mem_filter.mp h).2
    unfold singleColorBall
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨1, by omega,
        SingleColorWalk.snoc (SingleColorWalk.nil v) hcolor⟩⟩

/-- The mass of the weighted radius-one monochromatic ball is at
least the center plus all its incident same-color neighbors. -/
theorem heavy_star_mass_le_ball_one
    {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (E : V → V → C) (c : C) (v : V)
    (w : V → ℝ) (hw : ∀ x : V, 0 ≤ w x) :
    w v +
      (∑ x ∈ Finset.univ.erase v,
        if c = E v x then w x else 0) ≤
      colorBallMass E c v w 1 := by
  classical
  let star := colorStar E c v
  have hnot : v ∉ star := by
    simp [star, colorStar]
  have hStarSum :
      (∑ x ∈ star, w x) =
      ∑ x ∈ Finset.univ.erase v,
        if c = E v x then w x else 0 := by
    simp only [star, colorStar, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : E v x = c
    · simp [h]
    · simp [h, eq_comm]
  have hSubset :
      (∑ x ∈ insert v star, w x) ≤
        ∑ x ∈ singleColorBall E c v 1, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (star_insert_subset_ball E c v)
      (by intro x _ _; exact hw x)
  rw [Finset.sum_insert hnot, hStarSum] at hSubset
  exact hSubset

end SchurFormal
